'use strict';
(function () {
  // ---------------------------------------------------------------- constants
  const CACHE_PREFIX = 'byways-';
  const OFFLINE_ASSETS = 7;

  const COLORS = [
    { fill: '#e4572e', dark: '#9e3518', name: 'red' },
    { fill: '#2a9d8f', dark: '#17655c', name: 'teal' },
    { fill: '#e9a93a', dark: '#9c6c14', name: 'yellow' },
    { fill: '#7b5ea7', dark: '#4e3a6f', name: 'purple' },
    { fill: '#3a7bd5', dark: '#234f91', name: 'blue' },
    { fill: '#d6457f', dark: '#8f2752', name: 'pink' },
  ];
  const PAL = {
    bg: '#24262c',
    land: '#f4eee2',
    landOut: '#c9c1b0',
    grid: 'rgba(90,70,40,0.10)',
    water: '#94c6d6',
    waterEdge: '#7fb4c6',
    road: '#5a5b63',
    roadEdge: '#46474e',
    bridge: '#9b7b57',
    motor: '#34353b',
    motorLine: '#f2d27a',
    tree: '#d9d2bd',
  };

  const CAR_SPEED = 1.9;        // tiles per second
  const MOTOR_SPEED = 4.2;
  const GAP = 0.55;             // spacing between queued cars
  const CROSS = 0.45;           // seconds a plain junction is blocked per car
  const ROUND_CROSS = 0.1;      // same, for a roundabout
  const INTER_PENALTY = 0.35;   // routing cost of passing a plain junction
  const DWELL = 0.8;
  const PIN_LIMIT = 6;
  const OVER_FILL = 1 / 30;     // overflow timer fills in 30s
  const OVER_DRAIN = 1 / 12;
  const WEEK_LEN = 70;
  const CARS_PER_HOUSE = 2;
  const MAX_BRIDGE = 6;
  const SQRT2 = Math.SQRT2;
  const SAVE_KEY = 'byways-save-v1';
  const BEST_KEY = 'byways-best';
  const SEEN_HELP_KEY = 'byways-seen-help';

  const $ = (s) => document.querySelector(s);
  const canvas = $('#c');
  const ctx = canvas.getContext('2d');

  let G = null;
  const view = { w: 0, h: 0, dpr: 1, top: 0, bottom: 0, right: 0 };
  const cam = { x: 0, y: 0, s: 30 };
  const user = { zoom: 1, px: 0, py: 0 };
  let camSnap = true;
  let tool = 'road';
  let modal = null;
  let motorStart = -1;
  let hoverTile = -1;

  const rnd = (a, b) => a + Math.random() * (b - a);
  const rint = (a, b) => Math.floor(rnd(a, b + 1));
  const pick = (arr) => arr[Math.floor(Math.random() * arr.length)];
  const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);

  // ---------------------------------------------------------------- grid helpers
  const idx = (x, y) => y * G.W + x;
  const tx = (i) => i % G.W;
  const ty = (i) => (i / G.W) | 0;
  const inMap = (x, y) => x >= 0 && y >= 0 && x < G.W && y < G.H;
  const inB = (x, y) => x >= G.bounds.x0 && x <= G.bounds.x1 && y >= G.bounds.y0 && y <= G.bounds.y1;
  const ekey = (a, b) => (a < b ? a * 65536 + b : b * 65536 + a);
  const dkey = (a, b) => a * 65536 + b;

  function freeTile(i) {
    return !G.water[i] && !G.road[i] && !G.occ[i];
  }

  function kind(i) {
    const o = G.occ[i];
    if (o) return o.kind === 'dest' ? null : o.kind;
    if (G.road[i]) return 'road';
    if (G.water[i]) return 'water';
    return 'land';
  }

  function nodeValid(n) {
    if (G.road[n]) return true;
    const o = G.occ[n];
    return !!o && (o.kind === 'house' || o.kind === 'port');
  }

  // ---------------------------------------------------------------- new game
  function newGame() {
    const portrait = window.innerHeight >= window.innerWidth;
    const W = portrait ? 18 : 28;
    const H = portrait ? 28 : 18;
    G = blankState(W, H);
    genRiver(portrait);
    const bw = portrait ? 10 : 15;
    const bh = portrait ? 15 : 10;
    const x0 = Math.floor((W - bw) / 2);
    const y0 = Math.floor((H - bh) / 2);
    G.bounds = { x0, y0, x1: x0 + bw - 1, y1: y0 + bh - 1 };

    const d = spawnDest(0);
    G.colorsUsed = 1;
    if (d) {
      spawnHouse(0, { x: d.x + 0.5, y: d.y + 0.5, rmin: 3, rmax: 6 });
      spawnHouse(0, { x: d.x + 0.5, y: d.y + 0.5, rmin: 3, rmax: 6 });
      d.pinT = 4;
    }
    user.zoom = 1; user.px = 0; user.py = 0;
    camSnap = true;
    tool = 'road';
    motorStart = -1;
    graphChanged();
  }

  function blankState(W, H) {
    const N = W * H;
    return {
      W, H, N,
      water: new Uint8Array(N),
      road: new Uint8Array(N),
      round: new Uint8Array(N),
      deco: new Uint8Array(N),
      occ: new Array(N).fill(null),
      adj: Array.from({ length: N }, () => new Map()),
      edges: new Map(),
      queues: new Map(),
      lock: new Float64Array(N),
      houses: [],
      dests: [],
      cars: [],
      fx: [],
      res: { roads: 30, bridges: 1, rounds: 0, motors: 0 },
      bridgesUsed: 0,
      time: 0, week: 1, weekT: 0, score: 0,
      speed: 1, paused: false, over: false,
      bounds: { x0: 0, y0: 0, x1: W - 1, y1: H - 1 },
      colorsUsed: 0,
      nextHouse: 6,
      nextDest: 32,
      dispatchT: 0,
      saveT: 0,
      nextId: 1,
    };
  }

  function genRiver(portrait) {
    // River crosses the short side of the map, a little off-centre.
    const along = portrait ? G.W : G.H;
    const across = portrait ? G.H : G.W;
    let c = Math.floor(across * rnd(0.38, 0.46));
    const set = (a, b) => {
      const x = portrait ? a : b;
      const y = portrait ? b : a;
      if (inMap(x, y)) G.water[idx(x, y)] = 1;
    };
    let width = 2;
    for (let a = 0; a < along; a++) {
      if (a > 0 && Math.random() < 0.35) {
        const nc = c + (Math.random() < 0.5 ? -1 : 1);
        if (nc > across * 0.3 && nc < across * 0.55) {
          for (let w = 0; w < width; w++) set(a, nc + w);
          c = nc;
        }
      }
      if (Math.random() < 0.15) width = width === 2 ? 3 : 2;
      for (let w = 0; w < width; w++) set(a, c + w);
    }
    // A small lake on the far side, sometimes.
    if (Math.random() < 0.7) {
      const la = rint(2, along - 4);
      const lc = Math.floor(across * rnd(0.72, 0.85));
      for (let a = la; a < la + rint(2, 3); a++) for (let b = lc; b < lc + 2; b++) set(a, b);
    }
    for (let i = 0; i < G.N; i++) if (!G.water[i] && Math.random() < 0.08) G.deco[i] = 1 + rint(0, 2);
  }

  // ---------------------------------------------------------------- spawning
  function distToBlock(px, py, d) {
    const cx = clamp(px, d.x, d.x + 1);
    const cy = clamp(py, d.y, d.y + 1);
    return Math.max(Math.abs(px - cx), Math.abs(py - cy));
  }

  function spawnDest(color) {
    const B = G.bounds;
    let best = null;
    let bestScore = -Infinity;
    for (let tries = 0; tries < 500; tries++) {
      const x = rint(B.x0, B.x1 - 1);
      const y = rint(B.y0, B.y1 - 1);
      const cells = [idx(x, y), idx(x + 1, y), idx(x, y + 1), idx(x + 1, y + 1)];
      if (!cells.every(freeTile)) continue;
      let crowded = false;
      for (let yy = y - 1; yy <= y + 2 && !crowded; yy++) {
        for (let xx = x - 1; xx <= x + 2; xx++) {
          if (inMap(xx, yy) && G.occ[idx(xx, yy)]) { crowded = true; break; }
        }
      }
      if (crowded) continue;
      const ports = [
        [x, y - 1, 0, -1], [x + 1, y - 1, 0, -1], [x, y + 2, 0, 1], [x + 1, y + 2, 0, 1],
        [x - 1, y, -1, 0], [x - 1, y + 1, -1, 0], [x + 2, y, 1, 0], [x + 2, y + 1, 1, 0],
      ].filter(([px, py, dx, dy]) => {
        if (!inB(px, py) || !freeTile(idx(px, py))) return false;
        const ox = px + dx, oy = py + dy;
        return inB(ox, oy) && !G.water[idx(ox, oy)] && !G.occ[idx(ox, oy)];
      });
      if (!ports.length) continue;
      let score = rnd(0, 3);
      let nearest = 99;
      for (const d of G.dests) {
        const dd = Math.max(Math.abs(d.x - x), Math.abs(d.y - y));
        nearest = Math.min(nearest, dd + (d.color === color ? -2 : 0));
      }
      score += Math.min(nearest, 8);
      for (const h of G.houses) {
        const dd = distToBlock(tx(h.i), ty(h.i), { x, y });
        if (dd < 2) score -= 4;
      }
      if (score > bestScore) {
        bestScore = score;
        const p = pick(ports);
        best = { x, y, port: idx(p[0], p[1]) };
      }
    }
    if (!best) return null;
    const d = {
      id: G.nextId++, color, x: best.x, y: best.y, port: best.port,
      pins: 0, assigned: 0, overflow: 0, pinT: rnd(6, 9), born: G.time,
    };
    for (const c of [idx(d.x, d.y), idx(d.x + 1, d.y), idx(d.x, d.y + 1), idx(d.x + 1, d.y + 1)]) {
      G.occ[c] = { kind: 'dest', d };
      G.deco[c] = 0;
    }
    G.occ[d.port] = { kind: 'port', d };
    G.deco[d.port] = 0;
    G.dests.push(d);
    return d;
  }

  function houseSpotOK(i) {
    const x = tx(i), y = ty(i);
    if (!inB(x, y) || !freeTile(i)) return false;
    // keep a ring clear around buildings
    for (let yy = y - 1; yy <= y + 1; yy++) {
      for (let xx = x - 1; xx <= x + 1; xx++) {
        if (!inMap(xx, yy)) continue;
        const o = G.occ[idx(xx, yy)];
        if (o && (o.kind === 'dest' || o.kind === 'port')) return false;
      }
    }
    // needs a way out
    let exits = 0;
    for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
      const xx = x + dx, yy = y + dy;
      if (!inB(xx, yy)) continue;
      const j = idx(xx, yy);
      if (!G.water[j] && (!G.occ[j] || G.road[j])) exits++;
    }
    if (!exits) return false;
    // must not box in a neighbouring unconnected house
    for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
      const xx = x + dx, yy = y + dy;
      if (!inMap(xx, yy)) continue;
      const j = idx(xx, yy);
      const o = G.occ[j];
      if (o && o.kind === 'house' && G.adj[j].size === 0) {
        let ex = 0;
        for (const [ex1, ey1] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
          const ax = xx + ex1, ay = yy + ey1;
          if (!inB(ax, ay)) continue;
          const k = idx(ax, ay);
          if (k === i) continue;
          if (!G.water[k] && !G.occ[k]) ex++;
        }
        if (!ex) return false;
      }
    }
    return true;
  }

  function spawnHouse(color, near) {
    const B = G.bounds;
    const mine = G.houses.filter((h) => h.color === color);
    let spot = -1;
    for (let tries = 0; tries < 400 && spot < 0; tries++) {
      let x, y;
      if (near) {
        const r = rnd(near.rmin, near.rmax);
        const a = rnd(0, Math.PI * 2);
        x = Math.round(near.x + Math.cos(a) * r);
        y = Math.round(near.y + Math.sin(a) * r);
      } else if (mine.length && Math.random() < 0.72) {
        const h = pick(mine);
        x = tx(h.i) + rint(-2, 2);
        y = ty(h.i) + rint(-2, 2);
      } else {
        x = rint(B.x0, B.x1);
        y = rint(B.y0, B.y1);
      }
      if (!inMap(x, y)) continue;
      const i = idx(x, y);
      if (houseSpotOK(i)) spot = i;
    }
    if (spot < 0 && near) return spawnHouse(color, null);
    if (spot < 0) return null;
    const h = { id: G.nextId++, color, i: spot, born: G.time };
    G.occ[spot] = { kind: 'house', h };
    G.deco[spot] = 0;
    G.houses.push(h);
    for (let k = 0; k < CARS_PER_HOUSE; k++) addCar(h);
    return h;
  }

  function addCar(h) {
    G.cars.push({
      id: G.nextId++, house: h, color: h.color, state: 'home', leg: null,
      path: null, s: 0, t: 0, len: 1, dk: -1, dest: null, timer: 0, wx: 0, wy: 0, ang: 0,
    });
  }

  function spawnNewDest() {
    const target = Math.min(COLORS.length, 2 + Math.floor((G.week - 1) / 2));
    let color;
    if (G.colorsUsed < target) {
      color = G.colorsUsed;
    } else {
      const counts = new Array(G.colorsUsed).fill(0);
      for (const d of G.dests) counts[d.color]++;
      const min = Math.min(...counts);
      const options = counts.map((c, i) => (c === min ? i : -1)).filter((i) => i >= 0);
      color = pick(options);
    }
    const d = spawnDest(color);
    if (!d) return;
    if (color === G.colorsUsed) G.colorsUsed++;
    const n = G.houses.some((h) => h.color === color) ? 1 : 2;
    for (let k = 0; k < n; k++) spawnHouse(color, { x: d.x + 0.5, y: d.y + 0.5, rmin: 3, rmax: 7 });
  }

  function chooseHouseColor() {
    const dc = new Array(G.colorsUsed).fill(0);
    const hc = new Array(G.colorsUsed).fill(0);
    for (const d of G.dests) dc[d.color]++;
    for (const h of G.houses) hc[h.color]++;
    const w = dc.map((d, i) => (d ? Math.max(0.3, d * 3.5 - hc[i] + 1) : 0));
    let sum = w.reduce((a, b) => a + b, 0);
    let r = Math.random() * sum;
    for (let i = 0; i < w.length; i++) { r -= w[i]; if (r <= 0) return i; }
    return 0;
  }

  function expandBounds() {
    const B = G.bounds;
    B.x0 = Math.max(0, B.x0 - 1);
    B.x1 = Math.min(G.W - 1, B.x1 + 1);
    B.y0 = Math.max(0, B.y0 - 1);
    B.y1 = Math.min(G.H - 1, B.y1 + 1);
  }

  // ---------------------------------------------------------------- graph
  function addEdge(a, b, type) {
    const len = type === 'motor'
      ? Math.hypot(tx(a) - tx(b), ty(a) - ty(b))
      : (tx(a) !== tx(b) && ty(a) !== ty(b) ? SQRT2 : 1);
    const e = { a, b, type, len };
    G.adj[a].set(b, e);
    G.adj[b].set(a, e);
    G.edges.set(ekey(a, b), e);
    return e;
  }

  function removeEdge(a, b, refund = true) {
    const e = G.adj[a].get(b);
    if (!e) return;
    G.adj[a].delete(b);
    G.adj[b].delete(a);
    G.edges.delete(ekey(a, b));
    if (e.type === 'motor' && refund) G.res.motors++;
  }

  function bridgeInfo() {
    const seen = new Uint8Array(G.N);
    let count = 0, maxSize = 0;
    for (let i = 0; i < G.N; i++) {
      if (!G.water[i] || !G.road[i] || seen[i]) continue;
      count++;
      const comp = bridgeComponent(i, seen);
      maxSize = Math.max(maxSize, comp.length);
    }
    return { count, maxSize };
  }

  function bridgeComponent(start, seen = new Uint8Array(G.N)) {
    const out = [];
    const stack = [start];
    seen[start] = 1;
    while (stack.length) {
      const n = stack.pop();
      out.push(n);
      for (const m of G.adj[n].keys()) {
        if (!seen[m] && G.water[m] && G.road[m]) { seen[m] = 1; stack.push(m); }
      }
    }
    return out;
  }

  function tryConnect(p, q) {
    const px = tx(p), py = ty(p), qx = tx(q), qy = ty(q);
    const dx = qx - px, dy = qy - py;
    if (Math.max(Math.abs(dx), Math.abs(dy)) !== 1) return 'bad';
    if (!inB(px, py) || !inB(qx, qy)) return 'bounds';
    if (G.adj[p].has(q)) return 'ok';
    const kp = kind(p), kq = kind(q);
    if (!kp || !kq) return 'bad';
    const diag = dx !== 0 && dy !== 0;
    const special = (k) => k === 'house' || k === 'port';
    if (special(kp) || special(kq)) {
      if (diag) return 'bad';
      if (special(kp) && special(kq)) return 'bad';
    }
    if (kp === 'house' && G.adj[p].size > 0) return 'bad';
    if (kq === 'house' && G.adj[q].size > 0) return 'bad';
    if (diag) {
      const c1 = idx(px + dx, py), c2 = idx(px, py + dy);
      if (G.adj[c1].has(c2)) return 'bad';
    }
    const need = (kp === 'land' ? 1 : 0) + (kq === 'land' ? 1 : 0);
    if (need > G.res.roads) return 'roads';

    const setP = kp === 'land' || kp === 'water';
    const setQ = kq === 'land' || kq === 'water';
    if (setP) G.road[p] = 1;
    if (setQ) G.road[q] = 1;
    addEdge(p, q, 'road');
    if (G.water[p] || G.water[q]) {
      const info = bridgeInfo();
      if (info.count > G.res.bridges || info.maxSize > MAX_BRIDGE) {
        removeEdge(p, q, false);
        if (setP) G.road[p] = 0;
        if (setQ) G.road[q] = 0;
        return info.count > G.res.bridges ? 'bridges' : 'long';
      }
    }
    if (setP) G.deco[p] = 0;
    if (setQ) G.deco[q] = 0;
    G.res.roads -= need;
    graphChanged();
    return 'ok';
  }

  function clearRoadTile(t) {
    for (const n of [...G.adj[t].keys()]) removeEdge(t, n);
    G.road[t] = 0;
    if (!G.water[t]) G.res.roads++;
    if (G.round[t]) { G.round[t] = 0; G.res.rounds++; }
  }

  function eraseAt(i) {
    const o = G.occ[i];
    if (o && (o.kind === 'house' || o.kind === 'port')) {
      if (!G.adj[i].size) return false;
      for (const n of [...G.adj[i].keys()]) removeEdge(i, n);
      graphChanged();
      return true;
    }
    if (o || !G.road[i]) return false;
    if (G.water[i]) {
      for (const t of bridgeComponent(i)) clearRoadTile(t);
    } else {
      clearRoadTile(i);
    }
    graphChanged();
    return true;
  }

  function placeRoundabout(i) {
    if (G.res.rounds <= 0) { toast('No roundabouts left. You can win more at the end of a week.'); return false; }
    if (!G.road[i] || G.water[i] || G.round[i] || G.occ[i]) { toast('Tap a road junction to place a roundabout.'); return false; }
    G.round[i] = 1;
    G.res.rounds--;
    graphChanged();
    return true;
  }

  function placeMotorway(a, b) {
    const ka = kind(a), kb = kind(b);
    const okKind = (k) => k === 'road' || k === 'land';
    if (!okKind(ka) || !okKind(kb) || G.water[a] || G.water[b]) {
      toast('Motorways start and end on land, not on houses or buildings.');
      return false;
    }
    if (Math.max(Math.abs(tx(a) - tx(b)), Math.abs(ty(a) - ty(b))) < 2) { toast('Pick an end point further away.'); return false; }
    if (G.adj[a].has(b)) return false;
    const need = (ka === 'land' ? 1 : 0) + (kb === 'land' ? 1 : 0);
    if (need > G.res.roads) { toast('You need a road tile at each end.'); flashCount('road'); return false; }
    G.road[a] = 1; G.road[b] = 1; G.deco[a] = 0; G.deco[b] = 0;
    G.res.roads -= need;
    addEdge(a, b, 'motor');
    G.res.motors--;
    graphChanged();
    return true;
  }

  function graphChanged() {
    G.bridgesUsed = bridgeInfo().count;
    for (const c of G.cars) validateCar(c);
  }

  // ---------------------------------------------------------------- routing
  function heapPush(h, d, n) {
    h.push([d, n]);
    let i = h.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (h[p][0] <= h[i][0]) break;
      [h[p], h[i]] = [h[i], h[p]];
      i = p;
    }
  }
  function heapPop(h) {
    const top = h[0];
    const last = h.pop();
    if (h.length) {
      h[0] = last;
      let i = 0;
      for (;;) {
        const l = i * 2 + 1, r = l + 1;
        let m = i;
        if (l < h.length && h[l][0] < h[m][0]) m = l;
        if (r < h.length && h[r][0] < h[m][0]) m = r;
        if (m === i) break;
        [h[m], h[i]] = [h[i], h[m]];
        i = m;
      }
    }
    return top;
  }

  function dijkstra(src, stop = -1) {
    const dist = new Float64Array(G.N).fill(Infinity);
    const prev = new Int32Array(G.N).fill(-1);
    dist[src] = 0;
    const heap = [[0, src]];
    while (heap.length) {
      const [d, u] = heapPop(heap);
      if (d > dist[u]) continue;
      if (u === stop) break;
      if (u !== src && G.occ[u]) continue; // houses and ports are ends only
      for (const [v, e] of G.adj[u]) {
        let w = e.len / (e.type === 'motor' ? MOTOR_SPEED : CAR_SPEED);
        if (!G.occ[v] && G.adj[v].size >= 3) w += G.round[v] ? 0.08 : INTER_PENALTY;
        const nd = d + w;
        if (nd < dist[v]) { dist[v] = nd; prev[v] = u; heapPush(heap, nd, v); }
      }
    }
    return { dist, prev };
  }

  function findPath(src, dst) {
    if (src === dst) return [src];
    const { dist, prev } = dijkstra(dst, src);
    if (!isFinite(dist[src])) return null;
    const path = [];
    let n = src;
    while (n !== -1) { path.push(n); if (n === dst) break; n = prev[n]; }
    return path[path.length - 1] === dst ? path : null;
  }

  function dispatch() {
    for (const d of G.dests) {
      if (d.pins - d.assigned <= 0) continue;
      const idle = G.cars.filter((c) => c.color === d.color && c.state === 'home');
      if (!idle.length) continue;
      const { dist, prev } = dijkstra(d.port);
      let best = null, bd = Infinity;
      for (const c of idle) {
        const v = dist[c.house.i];
        if (v < bd) { bd = v; best = c; }
      }
      if (!best) continue;
      const path = [];
      let n = best.house.i;
      while (n !== -1) { path.push(n); if (n === d.port) break; n = prev[n]; }
      if (path[path.length - 1] !== d.port) continue;
      best.leg = 'out';
      best.dest = d;
      best.path = path;
      best.s = 0;
      best.state = 'wait';
      d.assigned++;
    }
  }

  // ---------------------------------------------------------------- cars
  function queueOf(k) {
    let q = G.queues.get(k);
    if (!q) { q = []; G.queues.set(k, q); }
    return q;
  }
  function edgeFree(a, b) {
    const q = G.queues.get(dkey(a, b));
    if (!q || !q.length) return true;
    return q[q.length - 1].t >= GAP;
  }
  function enterEdge(car, s) {
    const a = car.path[s], b = car.path[s + 1];
    const e = G.adj[a].get(b);
    car.s = s; car.t = 0; car.len = e.len; car.motor = e.type === 'motor';
    car.dk = dkey(a, b);
    queueOf(car.dk).push(car);
    car.state = 'drive';
  }
  function leaveEdge(car) {
    if (car.dk < 0) return;
    const q = G.queues.get(car.dk);
    if (q) {
      const i = q.indexOf(car);
      if (i >= 0) q.splice(i, 1);
      if (!q.length) G.queues.delete(car.dk);
    }
    car.dk = -1;
  }
  function isJunction(n) {
    return G.road[n] && G.adj[n].size >= 3;
  }
  function passJunction(n) {
    if (!isJunction(n)) return true;
    if (G.lock[n] > G.time) return false;
    G.lock[n] = G.time + (G.round[n] ? ROUND_CROSS : CROSS);
    return true;
  }

  function carTarget(car) {
    return car.leg === 'out' ? car.dest.port : car.house.i;
  }

  function poof(car) {
    const p = carPos(car);
    if (p) G.fx.push({ type: 'poof', x: p.x, y: p.y, t: 0 });
    leaveEdge(car);
    if (car.leg === 'out' && car.dest) car.dest.assigned--;
    car.state = 'home'; car.leg = null; car.path = null; car.dest = null;
  }

  function replanFrom(car, node) {
    let np = findPath(node, carTarget(car));
    if (!np && car.leg === 'out') {
      car.dest.assigned--;
      car.dest = null;
      car.leg = 'back';
      np = findPath(node, car.house.i);
    }
    if (!np) { poof(car); return; }
    car.path = np; car.s = 0; car.state = 'wait';
    if (np.length === 1) arrive(car);
  }

  function validateCar(car) {
    if (car.state === 'drive') {
      const a = car.path[car.s], b = car.path[car.s + 1];
      if (!G.adj[a].has(b)) {
        leaveEdge(car);
        let node = car.t > car.len / 2 ? b : a;
        if (!nodeValid(node)) node = node === a ? b : a;
        if (!nodeValid(node)) { poof(car); return; }
        car.wx = tx(node) + 0.5; car.wy = ty(node) + 0.5;
        replanFrom(car, node);
        return;
      }
      let broken = false;
      for (let k = car.s + 1; k < car.path.length - 1; k++) {
        if (!G.adj[car.path[k]].has(car.path[k + 1])) { broken = true; break; }
      }
      // also re-route if a quicker way has appeared, cheaply: only when broken
      if (broken) {
        let np = findPath(b, carTarget(car));
        if (!np && car.leg === 'out') {
          car.dest.assigned--; car.dest = null; car.leg = 'back';
          np = findPath(b, car.house.i);
        }
        if (!np) { poof(car); return; }
        car.path = [a, ...np];
        car.s = 0;
      }
    } else if (car.state === 'wait') {
      let broken = car.leg === 'out' && !car.dest;
      for (let k = 0; k < car.path.length - 1 && !broken; k++) {
        if (!G.adj[car.path[k]].has(car.path[k + 1])) broken = true;
      }
      if (broken || !nodeValid(car.path[0])) {
        if (!nodeValid(car.path[0])) { poof(car); return; }
        replanFrom(car, car.path[0]);
      }
    }
  }

  function arrive(car) {
    leaveEdge(car);
    if (car.leg === 'out') {
      const d = car.dest;
      d.pins = Math.max(0, d.pins - 1);
      d.assigned = Math.max(0, d.assigned - 1);
      G.score++;
      G.fx.push({ type: 'ring', x: tx(d.port) + 0.5, y: ty(d.port) + 0.5, t: 0, color: COLORS[d.color].fill });
      car.state = 'park';
      car.timer = DWELL;
      car.at = d.port;
    } else {
      car.state = 'home'; car.leg = null; car.path = null; car.dest = null;
    }
  }

  function updateCar(car, dt) {
    switch (car.state) {
      case 'home':
        return;
      case 'park':
        car.timer -= dt;
        if (car.timer <= 0) {
          const port = car.at;
          car.dest = null;
          car.leg = 'back';
          const p = findPath(port, car.house.i);
          if (!p) { car.timer = 0.5; car.stuck = (car.stuck || 0) + 0.5; if (car.stuck > 6) { car.stuck = 0; poof(car); } return; }
          car.stuck = 0;
          car.path = p; car.s = 0; car.state = 'wait';
        }
        return;
      case 'wait': {
        const a = car.path[0], b = car.path[1];
        if (b === undefined) { arrive(car); return; }
        if (!G.adj[a].has(b)) { validateCar(car); return; }
        if (!edgeFree(a, b)) return;
        if (!passJunction(a)) return;
        enterEdge(car, 0);
        return;
      }
      case 'drive': {
        const speed = car.motor ? MOTOR_SPEED : CAR_SPEED;
        const q = G.queues.get(car.dk);
        const qi = q ? q.indexOf(car) : -1;
        let lim = car.len;
        if (qi > 0) lim = Math.min(lim, q[qi - 1].t - GAP);
        if (car.t < lim) car.t = Math.min(lim, car.t + speed * dt);
        if (car.t >= car.len - 1e-4) {
          const s1 = car.s + 1;
          if (s1 === car.path.length - 1) { arrive(car); return; }
          const a = car.path[s1], b = car.path[s1 + 1];
          if (!G.adj[a].has(b)) { validateCar(car); return; }
          if (!edgeFree(a, b)) return;
          if (!passJunction(a)) return;
          leaveEdge(car);
          enterEdge(car, s1);
        }
        return;
      }
    }
  }

  function carPos(car) {
    if (car.state === 'drive') {
      const a = car.path[car.s], b = car.path[car.s + 1];
      const ax = tx(a) + 0.5, ay = ty(a) + 0.5, bx = tx(b) + 0.5, by = ty(b) + 0.5;
      const f = clamp(car.t / car.len, 0, 1);
      const dx = (bx - ax) / car.len, dy = (by - ay) / car.len;
      const off = car.motor ? 0.13 : 0.12;
      // keep left
      return { x: ax + (bx - ax) * f + dy * off, y: ay + (by - ay) * f - dx * off, ang: Math.atan2(dy, dx) };
    }
    if (car.state === 'wait' && car.path && !G.occ[car.path[0]]) {
      return { x: tx(car.path[0]) + 0.5, y: ty(car.path[0]) + 0.5, ang: car.ang || 0 };
    }
    return null;
  }

  // ---------------------------------------------------------------- simulation
  function pinInterval() {
    return Math.max(3, 10 * Math.pow(0.92, G.week - 1));
  }

  function step(dt) {
    G.time += dt;

    for (const d of G.dests) {
      d.pinT -= dt;
      if (d.pinT <= 0) {
        d.pins++;
        d.pinT = pinInterval() * rnd(0.7, 1.3);
      }
      if (d.pins > PIN_LIMIT) d.overflow += OVER_FILL * dt;
      else d.overflow = Math.max(0, d.overflow - OVER_DRAIN * dt);
      if (d.overflow >= 1) { gameOver(d); return; }
    }

    G.nextHouse -= dt;
    if (G.nextHouse <= 0) {
      spawnHouse(chooseHouseColor(), null);
      G.nextHouse = Math.max(3.6, 9 - 0.4 * (G.week - 1)) * rnd(0.75, 1.25);
    }
    G.nextDest -= dt;
    if (G.nextDest <= 0) {
      spawnNewDest();
      G.nextDest = rnd(50, 65);
    }

    G.dispatchT -= dt;
    if (G.dispatchT <= 0) { dispatch(); G.dispatchT = 0.25; }

    for (const c of G.cars) updateCar(c, dt);

    for (const f of G.fx) f.t += dt;
    G.fx = G.fx.filter((f) => f.t < 0.8);

    G.weekT += dt;
    if (G.weekT >= WEEK_LEN) {
      G.weekT -= WEEK_LEN;
      G.week++;
      G.res.roads += 15;
      expandBounds();
      showUpgrade();
    }

    G.saveT += dt;
    if (G.saveT > 15) { G.saveT = 0; save(); }
  }

  function gameOver(d) {
    G.over = true;
    const best = Math.max(G.score, +(localStorage.getItem(BEST_KEY) || 0));
    try { localStorage.setItem(BEST_KEY, String(best)); localStorage.removeItem(SAVE_KEY); } catch (e) { /* storage unavailable */ }
    G.overDest = d;
    // centre on the problem
    user.zoom = 1; user.px = 0; user.py = 0;
    setTimeout(() => {
      $('#overWhy').textContent = `The ${COLORS[d.color].name} building waited too long for visitors.`;
      $('#overScore').textContent = G.score;
      $('#overSub').textContent = `trips in ${G.week} ${G.week === 1 ? 'week' : 'weeks'}`;
      $('#overBest').textContent = !best ? '' : G.score >= best ? 'New best score.' : `Best: ${best} trips`;
      openScreen('sOver');
    }, 1400);
  }

  // ---------------------------------------------------------------- upgrades
  const UPGRADES = {
    bridges: { label: 'Bridge', note: 'Cross water', n: 1, icon: '<svg viewBox="0 0 48 48" fill="none" stroke-linecap="round"><path d="M4 34h40" stroke="#94c6d6" stroke-width="8"/><path d="M6 24c6-8 30-8 36 0" stroke="#9b7b57" stroke-width="4"/><path d="M6 24h36" stroke="#5a5b63" stroke-width="6"/></svg>' },
    rounds: { label: '2 roundabouts', note: 'Busy junctions flow better', n: 2, icon: '<svg viewBox="0 0 48 48" fill="none" stroke="#5a5b63" stroke-width="6" stroke-linecap="round"><path d="M24 4v12M24 32v12M4 24h12M32 24h12"/><circle cx="24" cy="24" r="9"/></svg>' },
    motors: { label: 'Motorway', note: 'Fast straight link', n: 1, icon: '<svg viewBox="0 0 48 48" fill="none" stroke-linecap="round"><path d="M8 40 40 8" stroke="#34353b" stroke-width="9"/><path d="M8 40 40 8" stroke="#f2d27a" stroke-width="1.6" stroke-dasharray="3 4"/></svg>' },
    roads: { label: '20 road tiles', note: 'More road to lay', n: 20, icon: '<svg viewBox="0 0 48 48" fill="none" stroke="#5a5b63" stroke-width="7" stroke-linecap="round" stroke-linejoin="round"><path d="M8 40V24h16V8h16"/></svg>' },
  };

  function showUpgrade() {
    const keys = Object.keys(UPGRADES);
    const a = pick(keys);
    let b = pick(keys);
    while (b === a) b = pick(keys);
    $('#upTitle').textContent = `Week ${G.week}`;
    $('#upText').textContent = 'Your town is growing. You get 15 more road tiles, and you can pick one upgrade.';
    const box = $('#choices');
    box.innerHTML = '';
    for (const k of [a, b]) {
      const u = UPGRADES[k];
      const btn = document.createElement('button');
      btn.className = 'choice';
      btn.innerHTML = `${u.icon}<span>${u.label}</span><small>${u.note}</small>`;
      btn.addEventListener('click', () => {
        G.res[k] += u.n;
        closeScreen();
        save();
      });
      box.appendChild(btn);
    }
    openScreen('sUpgrade');
  }

  // ---------------------------------------------------------------- save / load
  function save() {
    if (!G || G.over || G.demo) return;
    const roads = [], water = [], rounds = [], deco = [];
    for (let i = 0; i < G.N; i++) {
      if (G.road[i]) roads.push(i);
      if (G.water[i]) water.push(i);
      if (G.round[i]) rounds.push(i);
      if (G.deco[i]) deco.push(i, G.deco[i]);
    }
    const data = {
      v: 1, W: G.W, H: G.H, roads, water, rounds, deco,
      edges: [...G.edges.values()].map((e) => [e.a, e.b, e.type === 'motor' ? 1 : 0]),
      houses: G.houses.map((h) => [h.i, h.color]),
      dests: G.dests.map((d) => [d.x, d.y, d.port, d.color, d.pins, d.overflow, d.pinT]),
      res: G.res, time: G.time, week: G.week, weekT: G.weekT, score: G.score,
      bounds: G.bounds, colorsUsed: G.colorsUsed, nextHouse: G.nextHouse, nextDest: G.nextDest,
      speed: G.speed,
    };
    try { localStorage.setItem(SAVE_KEY, JSON.stringify(data)); } catch (e) { /* storage unavailable */ }
  }

  function load() {
    let data;
    try { data = JSON.parse(localStorage.getItem(SAVE_KEY) || 'null'); } catch (e) { data = null; }
    if (!data || data.v !== 1) return false;
    G = blankState(data.W, data.H);
    for (const i of data.water) G.water[i] = 1;
    for (const i of data.roads) G.road[i] = 1;
    for (const i of data.rounds) G.round[i] = 1;
    for (let k = 0; k < data.deco.length; k += 2) G.deco[data.deco[k]] = data.deco[k + 1];
    for (const [a, b, m] of data.edges) addEdge(a, b, m ? 'motor' : 'road');
    for (const [x, y, port, color, pins, overflow, pinT] of data.dests) {
      const d = { id: G.nextId++, color, x, y, port, pins, assigned: 0, overflow, pinT, born: -10 };
      for (const c of [idx(x, y), idx(x + 1, y), idx(x, y + 1), idx(x + 1, y + 1)]) G.occ[c] = { kind: 'dest', d };
      G.occ[port] = { kind: 'port', d };
      G.dests.push(d);
    }
    for (const [i, color] of data.houses) {
      const h = { id: G.nextId++, color, i, born: -10 };
      G.occ[i] = { kind: 'house', h };
      G.houses.push(h);
      for (let k = 0; k < CARS_PER_HOUSE; k++) addCar(h);
    }
    Object.assign(G.res, data.res);
    Object.assign(G, {
      time: data.time, week: data.week, weekT: data.weekT, score: data.score, bounds: data.bounds,
      colorsUsed: data.colorsUsed, nextHouse: data.nextHouse, nextDest: data.nextDest, speed: data.speed || 1,
    });
    user.zoom = 1; user.px = 0; user.py = 0;
    camSnap = true;
    graphChanged();
    return true;
  }

  // ---------------------------------------------------------------- camera
  function baseCam() {
    const B = G.bounds;
    const bw = B.x1 - B.x0 + 2;
    const bh = B.y1 - B.y0 + 2;
    const availH = Math.max(100, view.h - view.top - view.bottom);
    const availW = Math.max(100, view.w - view.right);
    const s = Math.min(availW / bw, availH / bh);
    return { x: (B.x0 + B.x1 + 1) / 2, y: (B.y0 + B.y1 + 1) / 2, s };
  }
  function targetCam() {
    const b = baseCam();
    const B = G.bounds;
    const s = b.s * user.zoom;
    // Only allow panning as far as zoom makes room for, so the town stays on screen.
    const slack = 1 - 1 / user.zoom;
    const hx = ((B.x1 - B.x0 + 2) / 2) * slack;
    const hy = ((B.y1 - B.y0 + 2) / 2) * slack;
    user.px = clamp(user.px, -hx, hx);
    user.py = clamp(user.py, -hy, hy);
    return { x: b.x + user.px, y: b.y + user.py, s };
  }
  function updateCamera(dt) {
    if (!G) return;
    const t = targetCam();
    if (camSnap) { cam.x = t.x; cam.y = t.y; cam.s = t.s; camSnap = false; return; }
    const k = 1 - Math.exp(-dt * 6);
    cam.x += (t.x - cam.x) * k;
    cam.y += (t.y - cam.y) * k;
    cam.s += (t.s - cam.s) * k;
  }
  function screenCenterY() { return view.top + (view.h - view.top - view.bottom) / 2; }
  function screenCenterX() { return (view.w - view.right) / 2; }
  const sx = (wx) => (wx - cam.x) * cam.s + screenCenterX();
  const sy = (wy) => (wy - cam.y) * cam.s + screenCenterY();
  const wxOf = (px) => (px - screenCenterX()) / cam.s + cam.x;
  const wyOf = (py) => (py - screenCenterY()) / cam.s + cam.y;

  // ---------------------------------------------------------------- input
  const pointers = new Map();
  let action = null;
  let pinch = null;
  let gestureLock = false;

  function tileAtWorld(wx, wy) {
    const x = Math.floor(wx), y = Math.floor(wy);
    if (!inMap(x, y)) return -1;
    return idx(x, y);
  }

  function stepToward(from, to) {
    const fx = tx(from), fy = ty(from), gx = tx(to), gy = ty(to);
    const dx = gx - fx, dy = gy - fy;
    const ax = Math.abs(dx), ay = Math.abs(dy);
    let sxv = Math.sign(dx), syv = Math.sign(dy);
    if (ax > ay * 2) syv = 0;
    else if (ay > ax * 2) sxv = 0;
    return idx(fx + sxv, fy + syv);
  }

  function lastFeedback(res) {
    if (res === 'roads') { toast('Out of road tiles. Erase some, or wait for next week.'); flashCount('road'); }
    else if (res === 'bridges') { toast('You need a bridge to cross water.'); flashCount('bridge'); }
    else if (res === 'long') toast('That bridge is too long.');
  }

  function roadMove(wx, wy, a) {
    const c = tileAtWorld(wx, wy);
    if (c < 0 || c === a.last) return;
    if (a.last < 0) {
      if (kind(c) !== null && inB(tx(c), ty(c))) a.last = c;
      return;
    }
    const cx = tx(c) + 0.5, cy = ty(c) + 0.5;
    const near = Math.hypot(wx - cx, wy - cy) < 0.46;
    const lx = tx(a.last), ly = ty(a.last);
    const cheb = Math.max(Math.abs(tx(c) - lx), Math.abs(ty(c) - ly));
    if (!near && cheb <= 1) return;
    let cur = a.last;
    let guard = 0;
    while (cur !== c && guard++ < 64) {
      const nx = stepToward(cur, c);
      const r = tryConnect(cur, nx);
      if (r !== 'ok') {
        if (!a.warned) { lastFeedback(r); if (r === 'roads' || r === 'bridges' || r === 'long') a.warned = true; }
        // let the stroke restart from a valid tile under the finger
        if (r === 'bad' && kind(nx) !== null) { cur = nx; continue; }
        break;
      }
      cur = nx;
    }
    a.last = cur;
  }

  function eraseMove(wx, wy, a) {
    const c = tileAtWorld(wx, wy);
    if (c < 0) return;
    if (a.last < 0 || a.last === c) { if (a.last !== c) eraseAt(c); a.last = c; return; }
    let cur = a.last, guard = 0;
    while (cur !== c && guard++ < 64) { cur = stepToward(cur, c); eraseAt(cur); }
    a.last = c;
  }

  function onDown(e) {
    if (!G || modal) return;
    try { canvas.setPointerCapture(e.pointerId); } catch (err) { /* not capturable */ }
    pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
    if (pointers.size === 1 && !gestureLock) {
      const wx = wxOf(e.clientX), wy = wyOf(e.clientY);
      action = { tool, sx: e.clientX, sy: e.clientY, moved: false, last: -1, warned: false };
      if (tool === 'road') {
        const c = tileAtWorld(wx, wy);
        if (c >= 0 && kind(c) !== null && inB(tx(c), ty(c))) action.last = c;
      } else if (tool === 'erase') {
        eraseMove(wx, wy, action);
      }
    } else if (pointers.size === 2) {
      action = null;
      gestureLock = true;
      startPinch();
    }
  }

  function startPinch() {
    const [p1, p2] = [...pointers.values()];
    const mx = (p1.x + p2.x) / 2, my = (p1.y + p2.y) / 2;
    pinch = { d0: Math.hypot(p1.x - p2.x, p1.y - p2.y) || 1, z0: user.zoom, wx: wxOf(mx), wy: wyOf(my) };
  }

  function onMove(e) {
    if (!pointers.has(e.pointerId)) {
      if (G && !modal && e.pointerType === 'mouse') {
        hoverTile = tileAtWorld(wxOf(e.clientX), wyOf(e.clientY));
      }
      return;
    }
    pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
    if (pinch && pointers.size >= 2) {
      const [p1, p2] = [...pointers.values()];
      const mx = (p1.x + p2.x) / 2, my = (p1.y + p2.y) / 2;
      const d = Math.hypot(p1.x - p2.x, p1.y - p2.y);
      user.zoom = clamp(pinch.z0 * d / pinch.d0, 1, 3.2);
      const b = baseCam();
      const s = b.s * user.zoom;
      const cx = pinch.wx - (mx - screenCenterX()) / s;
      const cy = pinch.wy - (my - screenCenterY()) / s;
      user.px = cx - b.x; user.py = cy - b.y;
      camSnap = true;
      return;
    }
    if (!action) return;
    if (Math.hypot(e.clientX - action.sx, e.clientY - action.sy) > 6) action.moved = true;
    const events = e.getCoalescedEvents ? e.getCoalescedEvents() : [e];
    for (const ev of (events.length ? events : [e])) {
      const wx = wxOf(ev.clientX), wy = wyOf(ev.clientY);
      if (action.tool === 'road') roadMove(wx, wy, action);
      else if (action.tool === 'erase') eraseMove(wx, wy, action);
    }
  }

  function onUp(e) {
    if (!pointers.has(e.pointerId)) return;
    pointers.delete(e.pointerId);
    if (pointers.size < 2) pinch = null;
    if (pointers.size === 0) gestureLock = false;
    if (!action) return;
    const a = action;
    action = null;
    if (a.moved || e.type === 'pointercancel') return;
    const c = tileAtWorld(wxOf(e.clientX), wyOf(e.clientY));
    if (c < 0) return;
    if (a.tool === 'round') {
      if (placeRoundabout(c) && G.res.rounds <= 0) setTool('road');
    } else if (a.tool === 'motor') {
      if (G.res.motors <= 0) { toast('No motorways left. You can win more at the end of a week.'); return; }
      if (motorStart < 0) {
        const k = kind(c);
        if ((k === 'road' || k === 'land') && !G.water[c] && inB(tx(c), ty(c))) { motorStart = c; toast('Now tap where the motorway should end.'); }
        else toast('Tap an empty tile or a road to start the motorway.');
      } else if (c === motorStart) {
        motorStart = -1;
      } else if (inB(tx(c), ty(c))) {
        if (placeMotorway(motorStart, c)) { motorStart = -1; setTool('road'); }
      }
    }
  }

  canvas.addEventListener('pointerdown', onDown);
  canvas.addEventListener('pointermove', onMove);
  canvas.addEventListener('pointerup', onUp);
  canvas.addEventListener('pointercancel', onUp);
  canvas.addEventListener('pointerleave', () => { hoverTile = -1; });
  document.addEventListener('gesturestart', (e) => e.preventDefault());
  document.addEventListener('dblclick', (e) => e.preventDefault());
  canvas.addEventListener('wheel', (e) => {
    if (!G || modal) return;
    e.preventDefault();
    const before = { x: wxOf(e.clientX), y: wyOf(e.clientY) };
    user.zoom = clamp(user.zoom * Math.exp(-e.deltaY * 0.0015), 1, 3.2);
    const b = baseCam();
    const s = b.s * user.zoom;
    user.px = before.x - (e.clientX - screenCenterX()) / s - b.x;
    user.py = before.y - (e.clientY - screenCenterY()) / s - b.y;
    camSnap = true;
  }, { passive: false });

  // ---------------------------------------------------------------- rendering
  function rr(x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  function popScale(born) {
    const t = (G.time - born) / 0.45;
    if (t >= 1) return 1;
    if (t <= 0) return 0;
    return 1 + Math.sin(t * Math.PI) * 0.25 - (1 - t) * (1 - t) * 0.9;
  }

  function render() {
    ctx.setTransform(view.dpr, 0, 0, view.dpr, 0, 0);
    ctx.fillStyle = PAL.bg;
    ctx.fillRect(0, 0, view.w, view.h);
    if (!G) return;
    const s = cam.s;
    const B = G.bounds;

    const vx0 = Math.max(0, Math.floor(wxOf(0)) - 1);
    const vx1 = Math.min(G.W - 1, Math.ceil(wxOf(view.w)) + 1);
    const vy0 = Math.max(0, Math.floor(wyOf(0)) - 1);
    const vy1 = Math.min(G.H - 1, Math.ceil(wyOf(view.h)) + 1);

    // land
    ctx.fillStyle = PAL.landOut;
    ctx.fillRect(sx(0), sy(0), G.W * s, G.H * s);
    ctx.fillStyle = PAL.land;
    ctx.fillRect(sx(B.x0), sy(B.y0), (B.x1 - B.x0 + 1) * s, (B.y1 - B.y0 + 1) * s);

    // decoration + grid
    for (let y = vy0; y <= vy1; y++) {
      for (let x = vx0; x <= vx1; x++) {
        const i = idx(x, y);
        if (G.water[i] || G.road[i] || G.occ[i]) continue;
        const cx = sx(x + 0.5), cy = sy(y + 0.5);
        if (G.deco[i]) {
          ctx.fillStyle = inB(x, y) ? PAL.tree : 'rgba(0,0,0,0.06)';
          const r = s * (0.12 + G.deco[i] * 0.04);
          ctx.beginPath(); ctx.arc(cx + (G.deco[i] - 2) * s * 0.12, cy, r, 0, Math.PI * 2); ctx.fill();
        } else if (inB(x, y)) {
          ctx.fillStyle = PAL.grid;
          ctx.fillRect(cx - 1, cy - 1, 2, 2);
        }
      }
    }

    // water
    ctx.fillStyle = PAL.water;
    for (let y = vy0; y <= vy1; y++) {
      for (let x = vx0; x <= vx1; x++) {
        if (G.water[idx(x, y)]) ctx.fillRect(sx(x) - 0.5, sy(y) - 0.5, s + 1, s + 1);
      }
    }
    // soft shoreline
    ctx.strokeStyle = PAL.waterEdge;
    ctx.lineWidth = Math.max(1, s * 0.06);
    ctx.beginPath();
    for (let y = vy0; y <= vy1; y++) {
      for (let x = vx0; x <= vx1; x++) {
        if (!G.water[idx(x, y)]) continue;
        if (y > 0 && !G.water[idx(x, y - 1)]) { ctx.moveTo(sx(x), sy(y)); ctx.lineTo(sx(x + 1), sy(y)); }
        if (y < G.H - 1 && !G.water[idx(x, y + 1)]) { ctx.moveTo(sx(x), sy(y + 1)); ctx.lineTo(sx(x + 1), sy(y + 1)); }
        if (x > 0 && !G.water[idx(x - 1, y)]) { ctx.moveTo(sx(x), sy(y)); ctx.lineTo(sx(x), sy(y + 1)); }
        if (x < G.W - 1 && !G.water[idx(x + 1, y)]) { ctx.moveTo(sx(x + 1), sy(y)); ctx.lineTo(sx(x + 1), sy(y + 1)); }
      }
    }
    ctx.stroke();

    // dim outside bounds
    ctx.fillStyle = 'rgba(36,38,44,0.42)';
    const bx0 = sx(B.x0), by0 = sy(B.y0), bx1 = sx(B.x1 + 1), by1 = sy(B.y1 + 1);
    ctx.fillRect(sx(0), sy(0), G.W * s, by0 - sy(0));
    ctx.fillRect(sx(0), by1, G.W * s, sy(G.H) - by1);
    ctx.fillRect(sx(0), by0, bx0 - sx(0), by1 - by0);
    ctx.fillRect(bx1, by0, sx(G.W) - bx1, by1 - by0);

    // roads
    const roadEdges = [];
    const motorEdges = [];
    for (const e of G.edges.values()) (e.type === 'motor' ? motorEdges : roadEdges).push(e);
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    const line = (e) => { ctx.moveTo(sx(tx(e.a) + 0.5), sy(ty(e.a) + 0.5)); ctx.lineTo(sx(tx(e.b) + 0.5), sy(ty(e.b) + 0.5)); };
    // bridge decks
    ctx.strokeStyle = PAL.bridge;
    ctx.lineWidth = s * 0.74;
    ctx.beginPath();
    for (const e of roadEdges) if (G.water[e.a] || G.water[e.b]) line(e);
    ctx.stroke();
    ctx.strokeStyle = PAL.roadEdge;
    ctx.lineWidth = s * 0.6;
    ctx.beginPath();
    for (const e of roadEdges) line(e);
    ctx.stroke();
    ctx.strokeStyle = PAL.road;
    ctx.lineWidth = s * 0.5;
    ctx.beginPath();
    for (const e of roadEdges) line(e);
    ctx.stroke();
    // lone road tiles and node caps
    ctx.fillStyle = PAL.road;
    for (let y = vy0; y <= vy1; y++) {
      for (let x = vx0; x <= vx1; x++) {
        const i = idx(x, y);
        if (G.road[i] && G.adj[i].size === 0) {
          ctx.beginPath(); ctx.arc(sx(x + 0.5), sy(y + 0.5), s * 0.27, 0, Math.PI * 2); ctx.fill();
        }
      }
    }
    // roundabouts
    for (let y = vy0; y <= vy1; y++) {
      for (let x = vx0; x <= vx1; x++) {
        const i = idx(x, y);
        if (!G.round[i]) continue;
        const cx = sx(x + 0.5), cy = sy(y + 0.5);
        ctx.fillStyle = PAL.roadEdge;
        ctx.beginPath(); ctx.arc(cx, cy, s * 0.5, 0, Math.PI * 2); ctx.fill();
        ctx.fillStyle = PAL.road;
        ctx.beginPath(); ctx.arc(cx, cy, s * 0.45, 0, Math.PI * 2); ctx.fill();
        ctx.fillStyle = '#a9c58a';
        ctx.beginPath(); ctx.arc(cx, cy, s * 0.17, 0, Math.PI * 2); ctx.fill();
      }
    }

    // cars on ordinary roads
    drawCars(false);

    // destinations
    for (const d of G.dests) drawDest(d);
    // houses
    for (const h of G.houses) drawHouse(h);

    // motorways (elevated)
    for (const e of motorEdges) {
      ctx.strokeStyle = 'rgba(0,0,0,0.18)';
      ctx.lineWidth = s * 0.78;
      ctx.beginPath();
      ctx.moveTo(sx(tx(e.a) + 0.5) + s * 0.08, sy(ty(e.a) + 0.5) + s * 0.12);
      ctx.lineTo(sx(tx(e.b) + 0.5) + s * 0.08, sy(ty(e.b) + 0.5) + s * 0.12);
      ctx.stroke();
      ctx.strokeStyle = PAL.motor;
      ctx.lineWidth = s * 0.66;
      ctx.beginPath(); line(e); ctx.stroke();
      ctx.strokeStyle = PAL.motorLine;
      ctx.lineWidth = Math.max(1, s * 0.05);
      ctx.setLineDash([s * 0.2, s * 0.25]);
      ctx.beginPath(); line(e); ctx.stroke();
      ctx.setLineDash([]);
      for (const n of [e.a, e.b]) {
        ctx.fillStyle = PAL.motor;
        ctx.beginPath(); ctx.arc(sx(tx(n) + 0.5), sy(ty(n) + 0.5), s * 0.36, 0, Math.PI * 2); ctx.fill();
      }
    }
    drawCars(true);

    // effects
    for (const f of G.fx) {
      const k = f.t / 0.8;
      if (f.type === 'ring') {
        ctx.strokeStyle = f.color;
        ctx.globalAlpha = 1 - k;
        ctx.lineWidth = s * 0.1;
        ctx.beginPath(); ctx.arc(sx(f.x), sy(f.y), s * (0.3 + k * 0.6), 0, Math.PI * 2); ctx.stroke();
        ctx.globalAlpha = 1;
      } else if (f.type === 'poof') {
        ctx.fillStyle = 'rgba(120,120,120,' + (0.5 * (1 - k)) + ')';
        ctx.beginPath(); ctx.arc(sx(f.x), sy(f.y), s * (0.15 + k * 0.4), 0, Math.PI * 2); ctx.fill();
      }
    }

    // tool hints
    if (tool === 'motor' && motorStart >= 0) {
      const pulse = 0.5 + 0.5 * Math.sin(performance.now() / 180);
      ctx.strokeStyle = PAL.motorLine;
      ctx.lineWidth = s * 0.12;
      ctx.beginPath(); ctx.arc(sx(tx(motorStart) + 0.5), sy(ty(motorStart) + 0.5), s * (0.42 + pulse * 0.1), 0, Math.PI * 2); ctx.stroke();
    }
    if (action && action.tool === 'road' && action.last >= 0) {
      ctx.strokeStyle = 'rgba(36,38,44,0.35)';
      ctx.lineWidth = Math.max(1.5, s * 0.06);
      ctx.beginPath(); ctx.arc(sx(tx(action.last) + 0.5), sy(ty(action.last) + 0.5), s * 0.46, 0, Math.PI * 2); ctx.stroke();
    }
    if (hoverTile >= 0 && !action && (tool === 'round' || tool === 'motor' || tool === 'erase')) {
      ctx.strokeStyle = 'rgba(36,38,44,0.3)';
      ctx.lineWidth = 1.5;
      ctx.strokeRect(sx(tx(hoverTile)) + 1, sy(ty(hoverTile)) + 1, s - 2, s - 2);
    }

    if (G.over && G.overDest) {
      const d = G.overDest;
      const pulse = 0.5 + 0.5 * Math.sin(performance.now() / 150);
      ctx.strokeStyle = COLORS[d.color].fill;
      ctx.lineWidth = s * 0.15;
      ctx.globalAlpha = 0.5 + pulse * 0.5;
      ctx.beginPath(); ctx.arc(sx(d.x + 1), sy(d.y + 1), s * (1.8 + pulse * 0.3), 0, Math.PI * 2); ctx.stroke();
      ctx.globalAlpha = 1;
    }
  }

  function drawCars(motor) {
    const s = cam.s;
    for (const c of G.cars) {
      if (!!c.motor !== motor && c.state === 'drive') continue;
      if (motor && c.state !== 'drive') continue;
      const p = carPos(c);
      if (!p) continue;
      c.ang = p.ang;
      const col = COLORS[c.color];
      ctx.save();
      ctx.translate(sx(p.x), sy(p.y));
      ctx.rotate(p.ang);
      const L = s * 0.36, Wd = s * 0.21;
      ctx.fillStyle = col.dark;
      rr(-L / 2 - 1, -Wd / 2 - 1, L + 2, Wd + 2, Wd * 0.4);
      ctx.fill();
      ctx.fillStyle = col.fill;
      rr(-L / 2, -Wd / 2, L, Wd, Wd * 0.35);
      ctx.fill();
      ctx.fillStyle = 'rgba(255,255,255,0.55)';
      ctx.fillRect(L * 0.08, -Wd * 0.32, L * 0.16, Wd * 0.64);
      ctx.restore();
    }
  }

  function drawHouse(h) {
    const s = cam.s;
    const x = tx(h.i), y = ty(h.i);
    const k = popScale(h.born);
    if (k <= 0) return;
    const col = COLORS[h.color];
    const cx = sx(x + 0.5), cy = sy(y + 0.5);
    const size = s * 0.66 * k;
    ctx.fillStyle = 'rgba(0,0,0,0.14)';
    rr(cx - size / 2 + s * 0.05, cy - size / 2 + s * 0.08, size, size, size * 0.22);
    ctx.fill();
    ctx.fillStyle = col.fill;
    rr(cx - size / 2, cy - size / 2, size, size, size * 0.22);
    ctx.fill();
    // roof ridge
    ctx.strokeStyle = col.dark;
    ctx.lineWidth = Math.max(1, s * 0.06);
    ctx.beginPath();
    ctx.moveTo(cx - size * 0.28, cy - size * 0.02);
    ctx.lineTo(cx, cy - size * 0.26);
    ctx.lineTo(cx + size * 0.28, cy - size * 0.02);
    ctx.stroke();
    // cars at home
    let home = 0;
    for (const c of G.cars) if (c.house === h && c.state === 'home') home++;
    ctx.fillStyle = '#fff';
    for (let n = 0; n < home; n++) {
      ctx.beginPath();
      ctx.arc(cx + (n - (home - 1) / 2) * size * 0.26, cy + size * 0.2, s * 0.055, 0, Math.PI * 2);
      ctx.fill();
    }
    if (!G.adj[h.i].size) {
      // unconnected: gentle pulse ring
      const pulse = 0.5 + 0.5 * Math.sin(G.time * 4 + h.id);
      ctx.strokeStyle = col.fill;
      ctx.globalAlpha = 0.25 + 0.35 * pulse;
      ctx.lineWidth = Math.max(1, s * 0.05);
      ctx.beginPath(); ctx.arc(cx, cy, s * 0.55, 0, Math.PI * 2); ctx.stroke();
      ctx.globalAlpha = 1;
    }
  }

  function drawDest(d) {
    const s = cam.s;
    const k = popScale(d.born);
    if (k <= 0) return;
    const col = COLORS[d.color];
    const cx = sx(d.x + 1), cy = sy(d.y + 1);
    const w = s * 1.76 * k;
    // port lot
    const px = sx(tx(d.port) + 0.5), py = sy(ty(d.port) + 0.5);
    ctx.fillStyle = col.dark;
    ctx.beginPath(); ctx.moveTo(cx, cy); ctx.lineTo(px, py); ctx.lineWidth = s * 0.5; ctx.strokeStyle = col.dark; ctx.stroke();
    rr(px - s * 0.36, py - s * 0.36, s * 0.72, s * 0.72, s * 0.14);
    ctx.fill();
    ctx.fillStyle = 'rgba(255,255,255,0.8)';
    ctx.font = `700 ${Math.round(s * 0.42)}px ui-rounded, -apple-system, system-ui, sans-serif`;
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText('P', px, py + s * 0.02);

    const over = d.pins > PIN_LIMIT;
    const shake = over ? Math.sin(G.time * 30) * s * 0.03 : 0;
    ctx.fillStyle = 'rgba(0,0,0,0.16)';
    rr(cx - w / 2 + s * 0.08, cy - w / 2 + s * 0.12, w, w, s * 0.28);
    ctx.fill();
    ctx.fillStyle = col.fill;
    rr(cx - w / 2 + shake, cy - w / 2, w, w, s * 0.28);
    ctx.fill();
    ctx.strokeStyle = col.dark;
    ctx.lineWidth = Math.max(1, s * 0.06);
    rr(cx - w / 2 + shake + s * 0.18, cy - w / 2 + s * 0.18, w - s * 0.36, w - s * 0.36, s * 0.16);
    ctx.stroke();

    // pins
    const n = Math.min(d.pins, 12);
    const cols = 4;
    const gap = w * 0.2;
    for (let i = 0; i < n; i++) {
      const r = Math.floor(i / cols), c = i % cols;
      const px2 = cx - gap * 1.5 + c * gap + shake;
      const py2 = cy - gap * 0.9 + r * gap * 0.9;
      ctx.fillStyle = i >= PIN_LIMIT ? '#24262c' : '#fff';
      ctx.beginPath(); ctx.arc(px2, py2, s * 0.085, 0, Math.PI * 2); ctx.fill();
    }

    if (d.overflow > 0.001) {
      const R = s * 1.35;
      ctx.lineCap = 'round';
      ctx.strokeStyle = 'rgba(36,38,44,0.25)';
      ctx.lineWidth = s * 0.16;
      ctx.beginPath(); ctx.arc(cx, cy, R, 0, Math.PI * 2); ctx.stroke();
      ctx.strokeStyle = col.dark;
      ctx.beginPath(); ctx.arc(cx, cy, R, -Math.PI / 2, -Math.PI / 2 + Math.PI * 2 * Math.min(1, d.overflow)); ctx.stroke();
    }
  }

  // ---------------------------------------------------------------- HUD + screens
  const el = {
    top: $('#top'), bottom: $('#bottom'), score: $('#score'), weekLabel: $('#weekLabel'), weekBar: $('#weekBar'),
    cRoads: $('#cRoads'), cRounds: $('#cRounds'), cMotors: $('#cMotors'), cBridges: $('#cBridges'),
    btnPause: $('#btnPause'), btnSpeed: $('#btnSpeed'), toast: $('#toast'),
  };
  const ICON_PAUSE = '<svg viewBox="0 0 24 24" fill="currentColor"><rect x="6" y="5" width="4" height="14" rx="1.2"/><rect x="14" y="5" width="4" height="14" rx="1.2"/></svg>';
  const ICON_PLAY = '<svg viewBox="0 0 24 24" fill="currentColor"><path d="M8 5.5v13a1 1 0 0 0 1.5.86l10.2-6.5a1 1 0 0 0 0-1.72L9.5 4.64A1 1 0 0 0 8 5.5z"/></svg>';

  let hudCache = '';
  function updateHud() {
    if (!G) return;
    const key = [G.score, G.week, Math.floor(G.weekT), G.res.roads, G.res.rounds, G.res.motors, G.res.bridges - G.bridgesUsed, G.paused, G.speed, tool].join('|');
    el.weekBar.style.width = (G.weekT / WEEK_LEN * 100).toFixed(1) + '%';
    if (key === hudCache) return;
    hudCache = key;
    el.score.textContent = G.score;
    el.weekLabel.textContent = `Week ${G.week}`;
    el.cRoads.textContent = G.res.roads;
    el.cRoads.classList.toggle('zero', G.res.roads === 0);
    el.cRounds.textContent = G.res.rounds;
    el.cRounds.classList.toggle('zero', G.res.rounds === 0);
    el.cMotors.textContent = G.res.motors;
    el.cMotors.classList.toggle('zero', G.res.motors === 0);
    el.cBridges.textContent = Math.max(0, G.res.bridges - G.bridgesUsed);
    el.btnPause.innerHTML = G.paused ? ICON_PLAY : ICON_PAUSE;
    el.btnPause.setAttribute('aria-label', G.paused ? 'Play' : 'Pause');
    el.btnSpeed.textContent = G.speed === 1 ? '1×' : '2×';
    document.querySelectorAll('.tool').forEach((b) => b.classList.toggle('active', b.dataset.tool === tool));
  }

  let toastTimer = 0;
  function toast(msg) {
    el.toast.textContent = msg;
    el.toast.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => el.toast.classList.remove('show'), 2200);
  }
  function flashCount(which) {
    const target = which === 'bridge' ? $('#bridgeBadge') : document.querySelector('.tool[data-tool="road"]');
    target.classList.remove('flash');
    void target.offsetWidth;
    target.classList.add('flash');
  }

  function setTool(t) {
    tool = t;
    motorStart = -1;
    hudCache = '';
  }

  document.querySelectorAll('.tool').forEach((b) => b.addEventListener('click', () => {
    const t = b.dataset.tool;
    if (t === 'round' && G.res.rounds <= 0) { toast('No roundabouts yet. You can pick them at the end of a week.'); return; }
    if (t === 'motor' && G.res.motors <= 0) { toast('No motorways yet. You can pick them at the end of a week.'); return; }
    setTool(t);
    if (t === 'round') toast('Tap a junction to add a roundabout.');
    if (t === 'motor') toast('Tap where the motorway should start.');
    if (t === 'erase') toast('Drag over roads to remove them. You get the tiles back.');
  }));

  el.btnPause.addEventListener('click', () => { if (!G) return; G.paused = !G.paused; hudCache = ''; if (G.paused) toast('Paused. You can still draw roads.'); });
  el.btnSpeed.addEventListener('click', () => { if (!G) return; G.speed = G.speed === 1 ? 2 : 1; hudCache = ''; });
  $('#btnMenu').addEventListener('click', () => { if (!G) return; save(); openScreen('sMenu'); });
  $('#btnResume').addEventListener('click', () => closeScreen());
  $('#btnRestart').addEventListener('click', () => { closeScreen(); startNew(); });
  $('#btnHowMenu').addEventListener('click', () => openScreen('sHelp', 'sMenu'));
  $('#btnHowTitle').addEventListener('click', () => openScreen('sHelp', 'sTitle'));
  $('#btnHelpDone').addEventListener('click', () => {
    try { localStorage.setItem(SEEN_HELP_KEY, '1'); } catch (e) { /* storage unavailable */ }
    if (helpReturn) openScreen(helpReturn); else closeScreen();
  });
  $('#btnNew').addEventListener('click', () => { closeScreen(); startNew(); });
  $('#btnContinue').addEventListener('click', () => { if (load()) { closeScreen(); showHud(true); } else startNew(); });
  $('#btnAgain').addEventListener('click', () => { closeScreen(); startNew(); });

  let helpReturn = null;
  function openScreen(id, returnTo) {
    document.querySelectorAll('.screen').forEach((s) => s.classList.remove('show'));
    $('#' + id).classList.add('show');
    modal = id;
    helpReturn = id === 'sHelp' ? (returnTo || null) : helpReturn;
    if (id === 'sTitle' || id === 'sMenu') refreshOffline();
    pointers.clear(); action = null; pinch = null; gestureLock = false;
  }
  function closeScreen() {
    document.querySelectorAll('.screen').forEach((s) => s.classList.remove('show'));
    modal = null;
  }
  function showHud(on) {
    el.top.hidden = !on;
    el.bottom.hidden = !on;
    measure();
    camSnap = true;
  }

  function startNew() {
    try { localStorage.removeItem(SAVE_KEY); } catch (e) { /* storage unavailable */ }
    showHud(true);
    newGame();
    save();
    let seen = false;
    try { seen = !!localStorage.getItem(SEEN_HELP_KEY); } catch (e) { /* storage unavailable */ }
    if (!seen) openScreen('sHelp');
  }

  function showTitle() {
    let hasSave = false;
    try { hasSave = !!localStorage.getItem(SAVE_KEY); } catch (e) { /* storage unavailable */ }
    $('#btnContinue').hidden = !hasSave;
    $('#btnNew').className = hasSave ? 'btn secondary' : 'btn';
    let best = 0;
    try { best = +(localStorage.getItem(BEST_KEY) || 0); } catch (e) { /* storage unavailable */ }
    $('#bestLine').textContent = best ? `Best: ${best} trips` : '';
    openScreen('sTitle');
  }

  // ---------------------------------------------------------------- offline status
  let offlineReady = false;
  function setOffline(state, text) {
    for (const id of ['#offline', '#offline2']) {
      const box = $(id);
      box.classList.toggle('ready', state === 'ready');
      box.querySelector('span').textContent = text;
    }
  }
  async function refreshOffline() {
    if (!('serviceWorker' in navigator) || !window.caches) {
      setOffline('no', 'Offline play needs Safari and a secure (https) address.');
      return;
    }
    try {
      offlineReady = false;
      for (const name of await caches.keys()) {
        if (!name.startsWith(CACHE_PREFIX)) continue;
        const keys = await (await caches.open(name)).keys();
        if (keys.length >= OFFLINE_ASSETS) offlineReady = true;
      }
      if (offlineReady) setOffline('ready', 'Saved for offline play');
      else setOffline('wait', 'Saving for offline play…');
    } catch (e) {
      setOffline('no', 'Offline play isn’t available here.');
    }
  }
  if ('serviceWorker' in navigator) {
    window.addEventListener('load', () => {
      navigator.serviceWorker.register('sw.js').then(() => navigator.serviceWorker.ready).then(() => {
        let tries = 0;
        const poll = () => { refreshOffline(); if (!offlineReady && tries++ < 20) setTimeout(poll, 700); };
        poll();
      }).catch(() => setOffline('no', 'Offline play couldn’t be set up.'));
    });
  }

  // ---------------------------------------------------------------- lifecycle
  function measure() {
    view.dpr = Math.min(3, window.devicePixelRatio || 1);
    view.w = window.innerWidth;
    view.h = window.innerHeight;
    canvas.width = Math.round(view.w * view.dpr);
    canvas.height = Math.round(view.h * view.dpr);
    view.top = el.top.hidden ? 0 : el.top.getBoundingClientRect().bottom;
    view.bottom = 0;
    view.right = 0;
    if (!el.bottom.hidden) {
      const bar = el.bottom.querySelector('.toolbar').getBoundingClientRect();
      const sideways = getComputedStyle(el.bottom).flexDirection === 'column';
      if (sideways) view.right = view.w - bar.left + 6;
      else view.bottom = view.h - bar.top + 6;
    }
  }
  window.addEventListener('resize', () => { measure(); camSnap = true; });

  document.addEventListener('visibilitychange', () => {
    if (document.hidden && G && !G.over) {
      save();
      if (!modal) { G.paused = true; hudCache = ''; }
    }
  });
  window.addEventListener('pagehide', () => save());

  let last = performance.now();
  let acc = 0;
  function frame(now) {
    const dt = Math.min(0.1, (now - last) / 1000);
    last = now;
    if (G && !G.paused && !G.over && !modal) {
      acc += dt * G.speed;
      const h = 1 / 60;
      let n = 0;
      while (acc >= h && n++ < 12) {
        step(h);
        acc -= h;
        if (G.over || modal) { acc = 0; break; }
      }
    } else {
      acc = 0;
    }
    updateCamera(dt);
    render();
    updateHud();
    requestAnimationFrame(frame);
  }

  measure();
  // Show a live map behind the title screen.
  newGame();
  G.demo = true;
  showTitle();
  requestAnimationFrame(frame);

  // exposed for testing in the browser console
  window.__byways = { get G() { return G; }, cam, step, tryConnect, idx, findPath, save, load, sx, sy };
})();
