# ChessVerse

A full chess platform in 3 files: `index.html`, `server.js`, `package.json`.

## Features
- Full chess rules (castling, en passant, promotion, check/checkmate/stalemate/draws)
- Click-to-move + drag-and-drop with legal move highlights
- Premoves (queue up to 3 in bullet/blitz)
- Live clocks with increment
- Glicko-2 rating system (bullet/blitz/rapid/classical separately)
- Inactivity decay (RD increases, rating preserved)
- Swiss tournament system with Buchholz tiebreaks
- Post-game Stockfish analysis (runs in browser, no server cost)
- Move classification: Best, Excellent, Good, Inaccuracy, Mistake, Blunder, Brilliant, Great, Miss
- Accuracy percentage per player
- Spectate live games
- Leaderboard per time control
- PGN export with annotations

## Setup

### 1. Install dependencies
```bash
npm install
```

### 2. Run the server
```bash
npm start
# or for dev with auto-restart:
npm run dev
```

Server runs on `http://localhost:3001`

### 3. Open the frontend
Open `index.html` in a browser — or serve it:
```bash
npx serve . -p 8080
```
Then go to `http://localhost:8080`

## Deploy to GitHub Pages + Railway

### Frontend (GitHub Pages)
1. Push `index.html` to a GitHub repo
2. Go to Settings → Pages → Deploy from branch (main)
3. Update `SERVER_HTTP` in `index.html` to your Railway URL

### Backend (Railway)
1. Push `server.js` and `package.json` to GitHub
2. Connect repo to Railway (railway.app)
3. Railway auto-detects Node.js and deploys

### Production note
The server currently uses in-memory storage — all data resets on restart.
For persistence, replace the `users` and `games` Maps with Supabase:
```bash
npm install @supabase/supabase-js
```

## File structure
```
chess/
├── index.html   # entire frontend
├── server.js    # entire backend
└── package.json # dependencies
```

## Keyboard shortcuts
- `F` — flip board
- `←` / `→` — step through analysis
- `↑` / `↓` — jump to start/end in analysis
- `Esc` — cancel selection / clear premoves
# tourney2
