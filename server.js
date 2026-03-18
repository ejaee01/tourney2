'use strict';
const express = require('express');
const { WebSocketServer, WebSocket } = require('ws');
const cors = require('cors');
const http = require('http');
const crypto = require('crypto');

const app = express();
app.use(cors());
app.use(express.json());

const server = http.createServer(app);
const wss = new WebSocketServer({ server });

// ── In-memory store (replace with Supabase for production) ──────────────────
const users = new Map();       // id -> user
const sessions = new Map();    // token -> userId
const games = new Map();       // gameId -> game
const sockets = new Map();     // ws -> {userId, gameId, tourneyId}
const userSockets = new Map(); // userId -> ws
const matchQueue = new Map();  // timeControl -> [{userId, rating, rd, ts}]
const tournaments = new Map(); // tourneyId -> tournament

// ── Glicko-2 ────────────────────────────────────────────────────────────────
const GLICKO = {
  q: Math.log(10) / 400,
  TAU: 0.5,        // volatility constraint
  EPSILON: 0.000001,
  DEFAULT_R: 1500,
  DEFAULT_RD: 350,
  DEFAULT_SIGMA: 0.06,
  C: 34.6,         // RD increase per period (~weekly)

  toScale(r, rd) {
    return { mu: (r - 1500) / 173.7178, phi: rd / 173.7178 };
  },

  fromScale(mu, phi) {
    return { r: Math.round(mu * 173.7178 + 1500), rd: Math.round(phi * 173.7178) };
  },

  g(phi) { return 1 / Math.sqrt(1 + 3 * phi * phi / (Math.PI * Math.PI)); },

  E(mu, muj, phij) { return 1 / (1 + Math.exp(-this.g(phij) * (mu - muj))); },

  update(player, opponents) {
    // opponents: [{r, rd, score}] where score = 1 win, 0.5 draw, 0 loss
    const { mu, phi } = this.toScale(player.r, player.rd);
    let sigma = player.sigma || this.DEFAULT_SIGMA;

    if (opponents.length === 0) {
      // Inactive period — increase RD only
      const phiStar = Math.sqrt(phi * phi + this.C * this.C / (173.7178 * 173.7178));
      const out = this.fromScale(mu, Math.min(phiStar, this.DEFAULT_RD / 173.7178));
      return { r: out.r, rd: out.rd, sigma };
    }

    const opp = opponents.map(o => {
      const s = this.toScale(o.r, o.rd);
      return { mu: s.mu, phi: s.phi, score: o.score };
    });

    // Step 3: compute v
    let v = 0;
    for (const o of opp) {
      const gp = this.g(o.phi);
      const E = this.E(mu, o.mu, o.phi);
      v += gp * gp * E * (1 - E);
    }
    v = 1 / v;

    // Step 4: compute delta
    let delta = 0;
    for (const o of opp) {
      delta += this.g(o.phi) * (o.score - this.E(mu, o.mu, o.phi));
    }
    delta *= v;

    // Step 5: update sigma via Illinois algorithm
    const a = Math.log(sigma * sigma);
    const f = (x) => {
      const ex = Math.exp(x);
      const d2 = phi * phi + v + ex;
      return (ex * (delta * delta - d2)) / (2 * d2 * d2) - (x - a) / (this.TAU * this.TAU);
    };
    let A = a, B;
    if (delta * delta > phi * phi + v) B = Math.log(delta * delta - phi * phi - v);
    else { let k = 1; while (f(a - k * this.TAU) < 0) k++; B = a - k * this.TAU; }
    let fA = f(A), fB = f(B);
    for (let i = 0; i < 100 && Math.abs(B - A) > this.EPSILON; i++) {
      const C2 = A + (A - B) * fA / (fB - fA);
      const fC = f(C2);
      if (fC * fB <= 0) { A = B; fA = fB; }
      else fA /= 2;
      B = C2; fB = fC;
    }
    const newSigma = Math.exp(A / 2);

    // Step 6: update phi*
    const phiStar = Math.sqrt(phi * phi + newSigma * newSigma);

    // Step 7: new phi, mu
    const newPhi = 1 / Math.sqrt(1 / (phiStar * phiStar) + 1 / v);
    let newMu = mu;
    for (const o of opp) {
      newMu += newPhi * newPhi * this.g(o.phi) * (o.score - this.E(mu, o.mu, o.phi));
    }

    const out = this.fromScale(newMu, newPhi);
    return { r: Math.max(100, out.r), rd: Math.max(30, Math.min(350, out.rd)), sigma: newSigma };
  },

  expectedPoints(r, evalCP) {
    // Convert centipawn eval to win probability using rating-adjusted sigmoid
    const k = 4 / Math.max(1000, r);
    return 1 / (1 + Math.exp(-k * evalCP));
  }
};

// ── Chess engine (full rules) ────────────────────────────────────────────────
const CHESS = {
  PIECES: { P:1, N:2, B:3, R:4, Q:5, K:6, p:7, n:8, b:9, r:10, q:11, k:12 },
  WHITE: 'w', BLACK: 'b',

  initialFen: 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1',

  fenToState(fen) {
    const [board, turn, castle, ep, half, full] = fen.split(' ');
    const squares = Array(64).fill(null);
    let sq = 0;
    for (const c of board) {
      if (c === '/') continue;
      if (c >= '1' && c <= '8') { sq += parseInt(c); continue; }
      squares[sq++] = c;
    }
    return {
      board: squares, turn, castle, ep: ep === '-' ? null : ep,
      halfMove: parseInt(half), fullMove: parseInt(full),
      history: [], captured: { w: [], b: [] }
    };
  },

  stateToFen(s) {
    let fen = '', empty = 0;
    for (let i = 0; i < 64; i++) {
      if (i && i % 8 === 0) { if (empty) { fen += empty; empty = 0; } fen += '/'; }
      if (s.board[i]) { if (empty) { fen += empty; empty = 0; } fen += s.board[i]; }
      else empty++;
    }
    if (empty) fen += empty;
    const ep = s.ep || '-';
    return `${fen} ${s.turn} ${s.castle || '-'} ${ep} ${s.halfMove} ${s.fullMove}`;
  },

  file(sq) { return sq % 8; },
  rank(sq) { return Math.floor(sq / 8); },
  sq(f, r) { return r * 8 + f; },
  sqName(sq) { return 'abcdefgh'[sq % 8] + (8 - Math.floor(sq / 8)); },
  nameToSq(name) { return (8 - parseInt(name[1])) * 8 + 'abcdefgh'.indexOf(name[0]); },

  isWhite(p) { return p && p === p.toUpperCase(); },
  color(p) { return p ? (p === p.toUpperCase() ? 'w' : 'b') : null; },

  knightMoves(sq) {
    const f = this.file(sq), r = this.rank(sq);
    return [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]
      .filter(([df,dr]) => f+df>=0&&f+df<8&&r+dr>=0&&r+dr<8)
      .map(([df,dr]) => this.sq(f+df, r+dr));
  },

  slidingMoves(sq, board, dirs) {
    const moves = [];
    for (const [df,dr] of dirs) {
      let f = this.file(sq)+df, r = this.rank(sq)+dr;
      while (f>=0&&f<8&&r>=0&&r<8) {
        const to = this.sq(f,r);
        if (board[to]) { moves.push(to); break; }
        moves.push(to); f+=df; r+=dr;
      }
    }
    return moves;
  },

  pseudoMoves(sq, state) {
    const { board, turn, ep, castle } = state;
    const p = board[sq]; if (!p || this.color(p) !== turn) return [];
    const moves = [], upper = p.toUpperCase();
    const f = this.file(sq), r = this.rank(sq);
    const opp = turn === 'w' ? 'b' : 'w';
    const canCapture = (to) => !board[to] || this.color(board[to]) === opp;

    if (upper === 'P') {
      const dir = turn === 'w' ? -1 : 1, startRank = turn === 'w' ? 6 : 1;
      const fwd = this.sq(f, r+dir);
      if (fwd >= 0 && fwd < 64 && !board[fwd]) {
        moves.push(fwd);
        if (r === startRank && !board[this.sq(f, r+dir*2)]) moves.push(this.sq(f, r+dir*2));
      }
      for (const df of [-1,1]) {
        if (f+df<0||f+df>7) continue;
        const cap = this.sq(f+df, r+dir);
        if (board[cap] && this.color(board[cap]) === opp) moves.push(cap);
        if (ep && this.nameToSq(ep) === cap) moves.push(cap);
      }
    } else if (upper === 'N') {
      this.knightMoves(sq).filter(to => canCapture(to)).forEach(to => moves.push(to));
    } else if (upper === 'B') {
      this.slidingMoves(sq, board, [[-1,-1],[-1,1],[1,-1],[1,1]]).filter(to => canCapture(to)).forEach(to => moves.push(to));
    } else if (upper === 'R') {
      this.slidingMoves(sq, board, [[-1,0],[1,0],[0,-1],[0,1]]).filter(to => canCapture(to)).forEach(to => moves.push(to));
    } else if (upper === 'Q') {
      this.slidingMoves(sq, board, [[-1,-1],[-1,1],[1,-1],[1,1],[-1,0],[1,0],[0,-1],[0,1]]).filter(to => canCapture(to)).forEach(to => moves.push(to));
    } else if (upper === 'K') {
      const f2 = this.file(sq), r2 = this.rank(sq);
      for (const [df,dr] of [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]]) {
        if (f2+df<0||f2+df>7||r2+dr<0||r2+dr>7) continue;
        const to = this.sq(f2+df, r2+dr);
        if (canCapture(to)) moves.push(to);
      }
      // Castling
      if (turn === 'w' && r === 7) {
        if (castle?.includes('K') && !board[61] && !board[62]) moves.push(62);
        if (castle?.includes('Q') && !board[59] && !board[58] && !board[57]) moves.push(58);
      }
      if (turn === 'b' && r === 0) {
        if (castle?.includes('k') && !board[5] && !board[6]) moves.push(6);
        if (castle?.includes('q') && !board[3] && !board[2] && !board[1]) moves.push(2);
      }
    }
    return moves;
  },

  isAttacked(sq, byColor, board) {
    const tmpState = { board, turn: byColor, castle: '', ep: null };
    for (let i = 0; i < 64; i++) {
      if (!board[i] || this.color(board[i]) !== byColor) continue;
      const p = board[i].toUpperCase();
      if (p === 'K') continue; // avoid infinite recursion
      if (this.pseudoMoves(i, tmpState).includes(sq)) return true;
    }
    // Check pawns manually (pseudoMoves direction issue)
    const pDir = byColor === 'w' ? -1 : 1;
    const f = this.file(sq), r = this.rank(sq);
    for (const df of [-1,1]) {
      if (f+df<0||f+df>7) continue;
      const from = this.sq(f+df, r-pDir);
      if (from>=0&&from<64&&board[from]===(byColor==='w'?'P':'p')) return true;
    }
    return false;
  },

  kingSquare(color, board) {
    const k = color === 'w' ? 'K' : 'k';
    return board.indexOf(k);
  },

  inCheck(color, board) {
    const ksq = this.kingSquare(color, board);
    return ksq >= 0 && this.isAttacked(ksq, color === 'w' ? 'b' : 'w', board);
  },

  legalMoves(sq, state) {
    const moves = this.pseudoMoves(sq, state);
    return moves.filter(to => {
      const next = this.applyMoveRaw(state, sq, to);
      return !this.inCheck(state.turn, next.board);
    });
  },

  allLegalMoves(state) {
    const result = [];
    for (let i = 0; i < 64; i++) {
      if (state.board[i] && this.color(state.board[i]) === state.turn) {
        const moves = this.legalMoves(i, state);
        moves.forEach(to => result.push({ from: i, to }));
      }
    }
    return result;
  },

  applyMoveRaw(state, from, to, promo) {
    const board = [...state.board];
    const p = board[from];
    const upper = p?.toUpperCase();
    let ep = null, castle = state.castle || '';

    // En passant capture
    if (upper === 'P' && state.ep && this.nameToSq(state.ep) === to) {
      const epDir = state.turn === 'w' ? 1 : -1;
      board[to + epDir * 8] = null;
    }

    // Double pawn push — set EP square
    if (upper === 'P' && Math.abs(this.rank(to) - this.rank(from)) === 2) {
      ep = this.sqName((from + to) >> 1);
    }

    // Castling
    if (upper === 'K') {
      if (to - from === 2) { board[to-1] = board[to+1]; board[to+1] = null; }
      if (from - to === 2) { board[to+1] = board[to-2]; board[to-2] = null; }
      castle = castle.replace(state.turn === 'w' ? /[KQ]/g : /[kq]/g, '');
    }
    if (upper === 'R') {
      if (from === 63) castle = castle.replace('K','');
      if (from === 56) castle = castle.replace('Q','');
      if (from === 7)  castle = castle.replace('k','');
      if (from === 0)  castle = castle.replace('q','');
    }

    board[to] = promo ? (state.turn === 'w' ? promo.toUpperCase() : promo.toLowerCase()) : board[from];
    board[from] = null;

    return {
      ...state,
      board,
      turn: state.turn === 'w' ? 'b' : 'w',
      ep,
      castle: castle || '-',
      halfMove: (upper === 'P' || state.board[to]) ? 0 : state.halfMove + 1,
      fullMove: state.turn === 'b' ? state.fullMove + 1 : state.fullMove
    };
  },

  applyMove(state, from, to, promo) {
    const legal = this.legalMoves(from, state);
    if (!legal.includes(to)) return null;
    const captured = state.board[to];
    const next = this.applyMoveRaw(state, from, to, promo);
    if (captured) {
      const capturedBy = state.turn;
      next.captured[capturedBy] = [...(next.captured[capturedBy] || []), captured];
    }
    // Move history
    next.history = [...(state.history || []), {
      from, to, piece: state.board[from], captured, promo,
      fen: this.stateToFen(next), san: this.toSAN(state, from, to, promo)
    }];
    return next;
  },

  toSAN(state, from, to, promo) {
    const p = state.board[from];
    if (!p) return '?';
    const upper = p.toUpperCase();
    const toName = this.sqName(to);
    const captured = state.board[to];
    const epCapture = upper === 'P' && state.ep && this.nameToSq(state.ep) === to;

    if (upper === 'K') {
      if (to - from === 2) return 'O-O';
      if (from - to === 2) return 'O-O-O';
    }

    let san = '';
    if (upper !== 'P') san += upper;
    if (upper === 'P' && (captured || epCapture)) san += 'abcdefgh'[this.file(from)];
    if (captured || epCapture) san += 'x';
    san += toName;
    if (promo) san += '=' + promo.toUpperCase();

    const next = this.applyMoveRaw(state, from, to, promo);
    if (this.inCheck(next.turn, next.board)) {
      san += this.allLegalMoves(next).length === 0 ? '#' : '+';
    }
    return san;
  },

  gameStatus(state) {
    const moves = this.allLegalMoves(state);
    if (moves.length === 0) {
      if (this.inCheck(state.turn, state.board)) return { status: 'checkmate', winner: state.turn === 'w' ? 'b' : 'w' };
      return { status: 'stalemate', winner: null };
    }
    if (state.halfMove >= 100) return { status: 'draw', reason: '50-move rule', winner: null };
    // Check insufficient material
    const pieces = state.board.filter(Boolean);
    if (pieces.length <= 3) {
      const nonKing = pieces.filter(p => p.toUpperCase() !== 'K');
      if (nonKing.length === 0) return { status: 'draw', reason: 'insufficient material', winner: null };
      if (nonKing.length === 1 && ['B','N','b','n'].includes(nonKing[0]))
        return { status: 'draw', reason: 'insufficient material', winner: null };
    }
    return { status: 'playing' };
  }
};

// ── Auth helpers ─────────────────────────────────────────────────────────────
function genId() { return crypto.randomUUID(); }
function genToken() { return crypto.randomBytes(32).toString('hex'); }
function hashPass(pw) { return crypto.createHash('sha256').update(pw + 'chess_salt_42').digest('hex'); }

app.post('/api/register', (req, res) => {
  const { username, password, email } = req.body;
  if (!username || !password || username.length < 3)
    return res.status(400).json({ error: 'Invalid username or password' });
  if ([...users.values()].find(u => u.username === username))
    return res.status(409).json({ error: 'Username taken' });

  const id = genId();
  users.set(id, {
    id, username, email: email || '',
    password: hashPass(password),
    ratings: { bullet: { r:1500,rd:350,sigma:0.06 }, blitz: { r:1500,rd:350,sigma:0.06 }, rapid: { r:1500,rd:350,sigma:0.06 }, classical: { r:1500,rd:350,sigma:0.06 } },
    ratingHistory: [],
    games: [], wins: 0, losses: 0, draws: 0,
    lastActive: Date.now(), createdAt: Date.now()
  });
  const token = genToken();
  sessions.set(token, id);
  const u = users.get(id);
  res.json({ token, user: publicUser(u) });
});

app.post('/api/login', (req, res) => {
  const { username, password } = req.body;
  const user = [...users.values()].find(u => u.username === username && u.password === hashPass(password));
  if (!user) return res.status(401).json({ error: 'Invalid credentials' });
  const token = genToken();
  sessions.set(token, user.id);
  res.json({ token, user: publicUser(user) });
});

app.get('/api/profile/:username', (req, res) => {
  const user = [...users.values()].find(u => u.username === req.params.username);
  if (!user) return res.status(404).json({ error: 'Not found' });
  res.json(publicUser(user));
});

app.get('/api/leaderboard', (req, res) => {
  const tc = req.query.tc || 'blitz';
  const list = [...users.values()]
    .map(u => ({ username: u.username, rating: u.ratings[tc]?.r || 1500, rd: u.ratings[tc]?.rd || 350, games: u.games.length }))
    .filter(u => u.games > 0)
    .sort((a,b) => b.rating - a.rating)
    .slice(0, 50);
  res.json(list);
});

app.get('/api/game/:id', (req, res) => {
  const g = games.get(req.params.id);
  if (!g) return res.status(404).json({ error: 'Not found' });
  res.json(publicGame(g));
});

app.get('/api/tournaments', (req, res) => {
  res.json([...tournaments.values()].map(publicTourney));
});

function publicUser(u) {
  return { id: u.id, username: u.username, ratings: u.ratings, ratingHistory: u.ratingHistory.slice(-50), games: u.games.slice(-20), wins: u.wins, losses: u.losses, draws: u.draws, lastActive: u.lastActive };
}
function publicGame(g) {
  return { id: g.id, white: g.white, black: g.black, timeControl: g.timeControl, status: g.status, winner: g.winner, state: g.state, moves: g.state?.history || [], tourneyId: g.tourneyId };
}
function publicTourney(t) {
  return { id: t.id, name: t.name, type: t.type, timeControl: t.timeControl, status: t.status, players: t.players, rounds: t.rounds, currentRound: t.currentRound, pairings: t.pairings, standings: t.standings };
}

// ── WebSocket ────────────────────────────────────────────────────────────────
function send(ws, type, data) {
  if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify({ type, ...data }));
}
function broadcast(type, data, filter) {
  for (const [ws] of sockets) {
    if (filter && !filter(ws)) continue;
    send(ws, type, data);
  }
}
function broadcastGame(gameId, type, data) {
  for (const [ws, meta] of sockets) {
    if (meta.gameId === gameId || meta.watchingGameId === gameId) send(ws, type, data);
  }
}
function broadcastTourney(tourneyId, type, data) {
  for (const [ws, meta] of sockets) {
    if (meta.tourneyId === tourneyId) send(ws, type, data);
  }
}

wss.on('connection', ws => {
  sockets.set(ws, {});

  ws.on('message', raw => {
    let msg;
    try { msg = JSON.parse(raw); } catch { return; }
    const meta = sockets.get(ws);
    const userId = meta.userId;

    switch (msg.type) {

      case 'auth': {
        const token = msg.token;
        const uid = sessions.get(token);
        if (!uid) { send(ws, 'auth_error', { error: 'Invalid token' }); return; }
        sockets.set(ws, { ...meta, userId: uid });
        userSockets.set(uid, ws);
        const user = users.get(uid);
        user.lastActive = Date.now();
        send(ws, 'auth_ok', { user: publicUser(user) });
        // Rejoin active game if any
        const activeGame = [...games.values()].find(g => g.status === 'playing' && (g.white === uid || g.black === uid));
        if (activeGame) {
          sockets.set(ws, { ...sockets.get(ws), gameId: activeGame.id });
          send(ws, 'game_rejoined', { game: publicGame(activeGame) });
        }
        break;
      }

      case 'queue_join': {
        if (!userId) return;
        const tc = msg.timeControl || 'blitz';
        const user = users.get(userId);
        if (!user) return;
        const rating = user.ratings[tc];
        if (!matchQueue.has(tc)) matchQueue.set(tc, []);
        const q = matchQueue.get(tc);
        // Remove if already queued
        const existing = q.findIndex(e => e.userId === userId);
        if (existing >= 0) q.splice(existing, 1);
        q.push({ userId, r: rating.r, rd: rating.rd, ts: Date.now(), tc });
        sockets.set(ws, { ...sockets.get(ws), queued: tc });
        send(ws, 'queue_joined', { timeControl: tc, position: q.length });
        tryMatch(tc);
        break;
      }

      case 'queue_leave': {
        const tc = sockets.get(ws).queued;
        if (tc && matchQueue.has(tc)) {
          const q = matchQueue.get(tc);
          const i = q.findIndex(e => e.userId === userId);
          if (i >= 0) q.splice(i, 1);
        }
        sockets.set(ws, { ...sockets.get(ws), queued: null });
        send(ws, 'queue_left', {});
        break;
      }

      case 'move': {
        const { gameId, from, to, promo } = msg;
        const game = games.get(gameId);
        if (!game || game.status !== 'playing') return;
        const isWhite = game.white === userId;
        const isBlack = game.black === userId;
        if (!isWhite && !isBlack) return;
        if ((game.state.turn === 'w' && !isWhite) || (game.state.turn === 'b' && !isBlack)) {
          // Premove — store it
          if (!game.premoves) game.premoves = {};
          const pKey = isWhite ? 'w' : 'b';
          if (!game.premoves[pKey]) game.premoves[pKey] = [];
          if (game.premoves[pKey].length < 3) game.premoves[pKey].push({ from, to, promo });
          send(ws, 'premove_queued', { premoves: game.premoves[pKey] });
          return;
        }
        executeMove(game, from, to, promo);
        break;
      }

      case 'premove_clear': {
        const game = games.get(msg.gameId);
        if (!game) return;
        const pKey = game.white === userId ? 'w' : 'b';
        if (game.premoves) game.premoves[pKey] = [];
        send(ws, 'premove_cleared', {});
        break;
      }

      case 'resign': {
        const game = games.get(msg.gameId);
        if (!game || game.status !== 'playing') return;
        if (game.white !== userId && game.black !== userId) return;
        const winner = game.white === userId ? game.black : game.white;
        endGame(game, winner, 'resign');
        break;
      }

      case 'offer_draw': {
        const game = games.get(msg.gameId);
        if (!game || game.status !== 'playing') return;
        const oppId = game.white === userId ? game.black : game.white;
        const oppWs = userSockets.get(oppId);
        if (oppWs) send(oppWs, 'draw_offered', { gameId: game.id, by: users.get(userId)?.username });
        break;
      }

      case 'accept_draw': {
        const game = games.get(msg.gameId);
        if (!game || game.status !== 'playing') return;
        endGame(game, null, 'draw_agreement');
        break;
      }

      case 'watch': {
        sockets.set(ws, { ...sockets.get(ws), watchingGameId: msg.gameId });
        const game = games.get(msg.gameId);
        if (game) send(ws, 'game_state', { game: publicGame(game) });
        break;
      }

      case 'unwatch': {
        sockets.set(ws, { ...sockets.get(ws), watchingGameId: null });
        break;
      }

      case 'tourney_create': {
        if (!userId) return;
        const t = createTournament(msg.name, msg.type || 'swiss', msg.timeControl || 'blitz', msg.rounds || 5);
        send(ws, 'tourney_created', { tourney: publicTourney(t) });
        broadcast('tourney_list', { tourney: publicTourney(t) });
        break;
      }

      case 'tourney_join': {
        if (!userId) return;
        const t = tournaments.get(msg.tourneyId);
        if (!t || t.status !== 'waiting') return;
        if (!t.players.find(p => p.userId === userId)) {
          const user = users.get(userId);
          t.players.push({ userId, username: user.username, r: user.ratings[t.timeControl]?.r || 1500, score: 0, bucholz: 0 });
          sockets.set(ws, { ...sockets.get(ws), tourneyId: t.id });
          broadcastTourney(t.id, 'tourney_update', { tourney: publicTourney(t) });
          broadcast('tourney_list_update', { tourney: publicTourney(t) });
        }
        break;
      }

      case 'tourney_start': {
        if (!userId) return;
        const t = tournaments.get(msg.tourneyId);
        if (!t || t.status !== 'waiting' || t.players.length < 2) return;
        startTournamentRound(t);
        break;
      }

      case 'ping':
        send(ws, 'pong', { ts: Date.now() });
        break;
    }
  });

  ws.on('close', () => {
    const meta = sockets.get(ws);
    if (meta?.userId) userSockets.delete(meta.userId);
    if (meta?.queued && matchQueue.has(meta.queued)) {
      const q = matchQueue.get(meta.queued);
      const i = q.findIndex(e => e.userId === meta.userId);
      if (i >= 0) q.splice(i, 1);
    }
    sockets.delete(ws);
  });
});

// ── Matchmaking ──────────────────────────────────────────────────────────────
function tryMatch(tc) {
  const q = matchQueue.get(tc);
  if (!q || q.length < 2) return;
  const now = Date.now();

  for (let i = 0; i < q.length; i++) {
    for (let j = i+1; j < q.length; j++) {
      const a = q[i], b = q[j];
      const wait = Math.min((now - a.ts) / 1000, (now - b.ts) / 1000);
      const window = 100 + Math.floor(wait / 15) * 50;
      if (Math.abs(a.r - b.r) <= window) {
        q.splice(j, 1); q.splice(i, 1);
        startGame(a.userId, b.userId, tc);
        return;
      }
    }
  }
}

setInterval(() => { for (const tc of matchQueue.keys()) tryMatch(tc); }, 5000);

function startGame(whiteId, blackId, tc, tourneyId = null) {
  // Randomly assign colors
  if (Math.random() > 0.5) [whiteId, blackId] = [blackId, whiteId];
  const id = genId();
  const times = { bullet: 60, blitz: 180, rapid: 600, classical: 1800 };
  const increments = { bullet: 0, blitz: 2, rapid: 0, classical: 30 };
  const game = {
    id, white: whiteId, black: blackId, timeControl: tc,
    status: 'playing', winner: null, result: null,
    state: CHESS.fenToState(CHESS.initialFen),
    clocks: { w: (times[tc] || 180) * 1000, b: (times[tc] || 180) * 1000 },
    increment: (increments[tc] || 0) * 1000,
    lastMoveTime: Date.now(),
    tourneyId, premoves: { w: [], b: [] },
    spectators: []
  };
  games.set(id, game);

  const wUser = users.get(whiteId);
  const bUser = users.get(blackId);

  // Update socket meta for both players
  const wWs = userSockets.get(whiteId);
  const bWs = userSockets.get(blackId);
  if (wWs) { sockets.set(wWs, { ...sockets.get(wWs), gameId: id, queued: null }); }
  if (bWs) { sockets.set(bWs, { ...sockets.get(bWs), gameId: id, queued: null }); }

  const gameData = {
    game: publicGame(game),
    white: { id: whiteId, username: wUser?.username, rating: wUser?.ratings[tc]?.r || 1500 },
    black: { id: blackId, username: bUser?.username, rating: bUser?.ratings[tc]?.r || 1500 }
  };

  if (wWs) send(wWs, 'game_start', { ...gameData, color: 'w' });
  if (bWs) send(bWs, 'game_start', { ...gameData, color: 'b' });

  // Notify tournament watchers
  if (tourneyId) broadcastTourney(tourneyId, 'tourney_game_start', { gameId: id, white: wUser?.username, black: bUser?.username });

  // Start clock ticker
  game.clockInterval = setInterval(() => tickClock(game), 100);
  return game;
}

function tickClock(game) {
  if (game.status !== 'playing') { clearInterval(game.clockInterval); return; }
  const elapsed = Date.now() - game.lastMoveTime;
  const turn = game.state.turn;
  const timeLeft = game.clocks[turn] - elapsed;
  if (timeLeft <= 0) {
    clearInterval(game.clockInterval);
    // Flag — check if opponent has mating material
    const oppColor = turn === 'w' ? 'b' : 'w';
    endGame(game, oppColor, 'timeout');
  }
}

function executeMove(game, from, to, promo) {
  const now = Date.now();
  const turn = game.state.turn;
  const elapsed = now - game.lastMoveTime;
  game.clocks[turn] = Math.max(0, game.clocks[turn] - elapsed) + game.increment;
  game.lastMoveTime = now;

  const nextState = CHESS.applyMove(game.state, from, to, promo);
  if (!nextState) return; // illegal move

  game.state = nextState;

  const status = CHESS.gameStatus(nextState);
  broadcastGame(game.id, 'move', {
    gameId: game.id,
    from, to, promo,
    san: nextState.history[nextState.history.length - 1]?.san,
    fen: CHESS.stateToFen(nextState),
    clocks: game.clocks,
    turn: nextState.turn
  });

  if (status.status !== 'playing') {
    clearInterval(game.clockInterval);
    endGame(game, status.winner, status.status === 'checkmate' ? 'checkmate' : status.reason || status.status);
    return;
  }

  // Execute premove if queued
  const nextTurn = nextState.turn;
  const pmKey = nextTurn;
  if (game.premoves?.[pmKey]?.length > 0) {
    const pm = game.premoves[pmKey].shift();
    setTimeout(() => {
      const legal = CHESS.legalMoves(pm.from, game.state);
      if (legal.includes(pm.to)) executeMove(game, pm.from, pm.to, pm.promo);
      else {
        game.premoves[pmKey] = [];
        const pmUserId = nextTurn === 'w' ? game.white : game.black;
        const pmWs = userSockets.get(pmUserId);
        if (pmWs) send(pmWs, 'premove_cancelled', { gameId: game.id });
      }
    }, 50);
  }
}

function endGame(game, winner, reason) {
  if (game.status !== 'playing') return;
  clearInterval(game.clockInterval);
  game.status = 'finished';
  game.winner = winner;
  game.result = reason;
  game.endTime = Date.now();

  const wUser = users.get(game.white);
  const bUser = users.get(game.black);
  const tc = game.timeControl;

  // Update stats
  if (winner === null) {
    if (wUser) wUser.draws++;
    if (bUser) bUser.draws++;
  } else if (winner === game.white) {
    if (wUser) wUser.wins++;
    if (bUser) bUser.losses++;
  } else {
    if (wUser) wUser.losses++;
    if (bUser) bUser.wins++;
  }

  // Update Glicko-2
  if (wUser && bUser) {
    const wRating = wUser.ratings[tc];
    const bRating = bUser.ratings[tc];
    const wScore = winner === game.white ? 1 : winner === null ? 0.5 : 0;
    const bScore = 1 - wScore;

    const wNew = GLICKO.update(wRating, [{ r: bRating.r, rd: bRating.rd, score: wScore }]);
    const bNew = GLICKO.update(bRating, [{ r: wRating.r, rd: wRating.rd, score: bScore }]);

    wUser.ratings[tc] = wNew;
    bUser.ratings[tc] = bNew;
    wUser.ratingHistory.push({ r: wNew.r, tc, ts: Date.now() });
    bUser.ratingHistory.push({ r: bNew.r, tc, ts: Date.now() });

    if (wUser.games) wUser.games.push({ id: game.id, tc, result: wScore === 1 ? 'win' : wScore === 0 ? 'loss' : 'draw', ratingChange: wNew.r - wRating.r, ts: Date.now() });
    if (bUser.games) bUser.games.push({ id: game.id, tc, result: bScore === 1 ? 'win' : bScore === 0 ? 'loss' : 'draw', ratingChange: bNew.r - bRating.r, ts: Date.now() });
  }

  const payload = {
    gameId: game.id, winner, reason,
    ratingChanges: {
      [game.white]: wUser ? { r: wUser.ratings[tc].r, prev: (wUser.ratingHistory.slice(-2)[0]?.r || wUser.ratings[tc].r) } : null,
      [game.black]: bUser ? { r: bUser.ratings[tc].r, prev: (bUser.ratingHistory.slice(-2)[0]?.r || bUser.ratings[tc].r) } : null
    }
  };

  broadcastGame(game.id, 'game_over', payload);

  // Tournament handling
  if (game.tourneyId) {
    const t = tournaments.get(game.tourneyId);
    if (t) handleTourneyGameEnd(t, game, winner);
  }

  // Auto-route spectators to leaderboard after 3s
  setTimeout(() => {
    for (const [ws, meta] of sockets) {
      if (meta.watchingGameId === game.id) {
        send(ws, 'suggest_navigate', { to: 'spectate' });
      }
    }
  }, 3000);
}

// ── Tournament ───────────────────────────────────────────────────────────────
function createTournament(name, type, timeControl, totalRounds) {
  const id = genId();
  const t = { id, name, type, timeControl, status: 'waiting', players: [], rounds: totalRounds, currentRound: 0, pairings: [], standings: [], gameIds: [] };
  tournaments.set(id, t);
  return t;
}

function swissPair(players, roundNum) {
  // Sort by score desc, then rating desc
  const sorted = [...players].sort((a,b) => b.score - a.score || b.r - a.r);
  const paired = new Set();
  const pairs = [];
  for (let i = 0; i < sorted.length - 1; i++) {
    if (paired.has(sorted[i].userId)) continue;
    for (let j = i+1; j < sorted.length; j++) {
      if (paired.has(sorted[j].userId)) continue;
      // Avoid repeat pairings (simplified check)
      pairs.push([sorted[i], sorted[j]]);
      paired.add(sorted[i].userId);
      paired.add(sorted[j].userId);
      break;
    }
  }
  // Bye for unpaired player
  const byePlayer = sorted.find(p => !paired.has(p.userId));
  if (byePlayer) { byePlayer.score += 1; byePlayer.bye = (byePlayer.bye || 0) + 1; }
  return pairs;
}

function startTournamentRound(t) {
  t.currentRound++;
  t.status = 'playing';
  const pairs = swissPair(t.players, t.currentRound);
  const roundPairings = [];

  for (const [a, b] of pairs) {
    const game = startGame(a.userId, b.userId, t.timeControl, t.id);
    t.gameIds.push(game.id);
    roundPairings.push({ round: t.currentRound, white: a.userId, black: b.userId, gameId: game.id, result: null });
  }
  t.pairings.push(...roundPairings);
  updateStandings(t);
  broadcastTourney(t.id, 'tourney_update', { tourney: publicTourney(t) });
  broadcast('tourney_list_update', { tourney: publicTourney(t) });
}

function handleTourneyGameEnd(t, game, winner) {
  const pairing = t.pairings.find(p => p.gameId === game.id);
  if (!pairing) return;
  pairing.result = winner === game.white ? '1-0' : winner === game.black ? '0-1' : '½-½';

  const wPlayer = t.players.find(p => p.userId === game.white);
  const bPlayer = t.players.find(p => p.userId === game.black);
  if (wPlayer && bPlayer) {
    if (winner === game.white) { wPlayer.score += 1; }
    else if (winner === game.black) { bPlayer.score += 1; }
    else { wPlayer.score += 0.5; bPlayer.score += 0.5; }
  }

  updateStandings(t);
  broadcastTourney(t.id, 'tourney_update', { tourney: publicTourney(t) });

  // Check if round is complete
  const roundPairings = t.pairings.filter(p => p.round === t.currentRound);
  const allDone = roundPairings.every(p => p.result);
  if (allDone) {
    if (t.currentRound >= t.rounds) {
      t.status = 'finished';
      broadcastTourney(t.id, 'tourney_finished', { tourney: publicTourney(t) });
    } else {
      broadcastTourney(t.id, 'tourney_round_end', { round: t.currentRound, tourney: publicTourney(t) });
      // Auto-start next round after 30s
      setTimeout(() => startTournamentRound(t), 30000);
    }
  }
}

function updateStandings(t) {
  t.standings = [...t.players]
    .sort((a,b) => {
      if (b.score !== a.score) return b.score - a.score;
      // Buchholz tiebreak
      const bBuch = t.pairings.filter(p => p.white === b.userId || p.black === b.userId)
        .reduce((sum, p) => {
          const oppId = p.white === b.userId ? p.black : p.white;
          return sum + (t.players.find(x => x.userId === oppId)?.score || 0);
        }, 0);
      const aBuch = t.pairings.filter(p => p.white === a.userId || p.black === a.userId)
        .reduce((sum, p) => {
          const oppId = p.white === a.userId ? p.black : p.white;
          return sum + (t.players.find(x => x.userId === oppId)?.score || 0);
        }, 0);
      return bBuch - aBuch;
    })
    .map((p, i) => ({ rank: i+1, userId: p.userId, username: p.username, score: p.score, r: p.r }));
}

// ── Periodic Glicko-2 rating period (weekly) ─────────────────────────────────
function runRatingPeriod() {
  const now = Date.now();
  const oneWeek = 7 * 24 * 60 * 60 * 1000;
  for (const user of users.values()) {
    const inactive = now - user.lastActive > oneWeek;
    if (inactive) {
      for (const tc of Object.keys(user.ratings)) {
        // Increase RD for inactivity
        user.ratings[tc] = GLICKO.update(user.ratings[tc], []);
      }
    }
  }
}
setInterval(runRatingPeriod, 7 * 24 * 60 * 60 * 1000);

// ── Start ────────────────────────────────────────────────────────────────────
const PORT = process.env.PORT || 3001;
server.listen(PORT, () => console.log(`Chess server running on port ${PORT}`));