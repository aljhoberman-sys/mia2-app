(() => {
'use strict';

const $ = id => document.getElementById(id);
const PALETTE = ['#534AB7', '#0F6E56', '#D85A30', '#185FA5', '#BA7517', '#993556'];
const HOP = 0.01;                 // seconds per envelope point
const RULER_H = 26, HEAD_H = 26, NOTES_H = 32;
const TOP_FRAC = 0.92;            // tallest point sits at this fraction of the plot height
const MAX_PX = 120;               // most zoomed-in: pixels per second
const H = 340, MH = 78;
const MINI_SMOOTH = 10;          // seconds of smoothing in the mini-map, independent of the slider

const S = {
  pieces: [], notes: [], total: 0,
  pxPerSec: 1, scroll: 0, playhead: 0,
  playing: false, dimmed: false,
  smoothSec: 3.5, scaleMode: 'program', dB: false, notesMode: false,
  globalPeak: 1, globalMiniPeak: 1,
  pending: [],      // pieces named by an opened session, still waiting for their audio
  undo: null,       // last removed piece, restorable for a short while
};

const canvas = $('chart'), g = canvas.getContext('2d');
const mini = $('mini'), m = mini.getContext('2d');
let W = 0, dpr = 1, atFit = true, drag = null, nextId = 1;
let audio = null, sources = [], t0 = 0, c0 = 0, raf = 0, drawQueued = false;
let editingNote = null, editingPiece = null;

const cl = (v, a, b) => Math.min(b, Math.max(a, v));
const timeToX = t => (t - S.scroll) * S.pxPerSec;
const xToTime = x => S.scroll + x / S.pxPerSec;
const byId = id => S.pieces.find(p => p.id === id);
const css = n => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
const fmt = s => { s = Math.max(0, Math.round(s)); return Math.floor(s / 60) + ':' + String(s % 60).padStart(2, '0'); };
const status = msg => { $('statusText').textContent = msg || ''; };
// a reopened session's missing audio is listed in a banner above the chart, with ways to find it
function showMissing() {
  const n = S.pending.length, files = n === 1 ? '1 audio file' : n + ' audio files';
  $('missing').hidden = !n;
  if (n) $('missingText').textContent = (S.pending.every(q => q.piece)
    ? 'The chart is complete. To play it, add ' + (n === 1 ? 'this audio file: ' : 'these ' + n + ' audio files: ') : 'Waiting for ' + files + ': ')
    + S.pending.map(q => q.file).join(', ');
  showPlayable();
}
const refreshStatus = () => { showMissing(); status(''); };
const baseName = n => n.replace(/\.[^.]+$/, '').toLowerCase();

/* Remembered file locations (Chrome and Edge only): the picker gives a handle to each file,
   and handles can be kept in IndexedDB so a saved session can find its audio again. */
const handleOf = new WeakMap();   // File -> FileSystemFileHandle
const claimOf = new WeakMap();    // File -> pending session piece it was reconnected for
const canRemember = !!window.showOpenFilePicker;

const idb = () => new Promise((res, rej) => {
  const r = indexedDB.open('mia2', 1);
  r.onupgradeneeded = () => r.result.createObjectStore('handles');
  r.onsuccess = () => res(r.result);
  r.onerror = () => rej(r.error);
});
async function idbPut(key, val) {
  const db = await idb();
  return new Promise((res, rej) => {
    const t = db.transaction('handles', 'readwrite');
    t.objectStore('handles').put(val, key);
    t.oncomplete = () => res(); t.onerror = () => rej(t.error);
  });
}
async function idbGet(key) {
  const db = await idb();
  return new Promise((res, rej) => {
    const rq = db.transaction('handles').objectStore('handles').get(key);
    rq.onsuccess = () => res(rq.result); rq.onerror = () => rej(rq.error);
  });
}

// small × on each title bar; null when the piece is too narrow on screen
function closeBox(p) {
  const x1 = Math.min(timeToX(p.start + p.dur), W), x0 = Math.max(timeToX(p.start), 0);
  if (x1 - x0 < 60) return null;
  return { x: x1 - 22, y: RULER_H + 4, w: 18, h: HEAD_H - 6 };
}
const minPx = () => (S.total ? W / S.total : 1);

/* ---------- analysis ---------- */

/* A-weighting (IEC 61672) as first-order sections, bilinear transform with prewarped poles.
   Bonde's MIA profiles match an A-weighted level much better than flat RMS: the bass drum
   and drones that fill the quiet gaps count for little, so the dips between phrases go deep. */
function aWeightSections(sr) {
  const K = 2 * sr, w = f => K * Math.tan(Math.PI * f / sr);
  const hp = f => { const p = w(f); return { b0: K / (K + p), b1: -K / (K + p), a1: (p - K) / (K + p) }; };
  const lp = f => { const p = w(f); return { b0: p / (K + p), b1: p / (K + p), a1: (p - K) / (K + p) }; };
  const secs = [hp(20.598997), hp(20.598997), hp(107.65265), hp(737.86223), lp(12194.217), lp(12194.217)];
  // scale to 0 dB at 1 kHz
  const z = { re: Math.cos(2 * Math.PI * 1000 / sr), im: -Math.sin(2 * Math.PI * 1000 / sr) };
  let g = 1;
  for (const s of secs) {
    const nr = s.b0 + s.b1 * z.re, ni = s.b1 * z.im, dr = 1 + s.a1 * z.re, di = s.a1 * z.im;
    g *= Math.hypot(nr, ni) / Math.hypot(dr, di);
  }
  secs[0].b0 /= g; secs[0].b1 /= g;
  return secs;
}

function aWeight(x, secs) {
  const y = Float32Array.from(x);
  for (const { b0, b1, a1 } of secs) {
    let x1 = 0, y1 = 0;
    for (let i = 0; i < y.length; i++) {
      const v = b0 * y[i] + b1 * x1 - a1 * y1;
      x1 = y[i]; y1 = v; y[i] = v;
    }
  }
  return y;
}

function envelope(buf) {
  const sr = buf.sampleRate, n = buf.length, blk = Math.round(sr * HOP), cnt = Math.ceil(n / blk);
  const out = new Float32Array(cnt);
  const secs = aWeightSections(sr), chs = [];
  for (let c = 0; c < buf.numberOfChannels; c++) chs.push(aWeight(buf.getChannelData(c), secs));
  for (let i = 0; i < cnt; i++) {
    const a = i * blk, b = Math.min(n, a + blk);
    let s = 0;
    for (const d of chs) for (let j = a; j < b; j++) s += d[j] * d[j];
    out[i] = Math.sqrt(s / (Math.max(1, b - a) * chs.length));
  }
  return out;
}

// slider 0..100 runs from 20 s (Gentle) to 0.1 s (Precise); the default of about 3.5 s
// matches the smoothing in Bonde's MIA profiles
const smoothSec = v => 0.1 * Math.pow(200, (100 - v) / 100);
const smoothSlider = sec => cl(100 - 100 * Math.log(sec / 0.1) / Math.log(200), 0, 100);
// smoothing is kept in seconds, rounded to what the number box shows, so a typed value is reproduced exactly
const roundSec = sec => cl(Math.round(sec * 10) / 10, 0.1, 20);
function showSmooth() { $('smooth').value = smoothSlider(S.smoothSec); $('smoothNum').value = S.smoothSec.toFixed(1); }

// moving average over `sec` seconds; returns the smoothed envelope and its peak
function boxSmooth(e, sec) {
  const w = Math.max(1, Math.round(sec / HOP)), half = w >> 1, n = e.length, P = new Float64Array(n + 1);
  for (let i = 0; i < n; i++) P[i + 1] = P[i] + e[i];
  const sm = new Float32Array(n);
  let pk = 1e-9;
  for (let i = 0; i < n; i++) {
    const a = Math.max(0, i - half), b = Math.min(n, i + half + 1);
    sm[i] = (P[b] - P[a]) / (b - a);
    if (sm[i] > pk) pk = sm[i];
  }
  return { sm, pk };
}

function recompute() {
  const sec = S.smoothSec;
  let gp = 1e-9, gm = 1e-9;
  for (const p of S.pieces) {
    ({ sm: p.sm, pk: p.peak } = boxSmooth(p.env, sec));
    // the mini-map is a whole-program overview: Bonde's program mini-maps match ~10 s smoothing
    if (!p.miniSm) ({ sm: p.miniSm, pk: p.miniPeak } = boxSmooth(p.env, MINI_SMOOTH));
    gp = Math.max(gp, p.peak); gm = Math.max(gm, p.miniPeak);
  }
  S.globalPeak = gp; S.globalMiniPeak = gm;
}

function yval(p, v, mini) {
  const r = v / (S.scaleMode === 'own' ? (mini ? p.miniPeak : p.peak) : (mini ? S.globalMiniPeak : S.globalPeak));
  return S.dB ? cl((20 * Math.log10(Math.max(r, 1e-6)) + 60) / 60, 0, 1) : cl(r, 0, 1);
}

function layout() {
  let t = 0;
  for (const p of S.pieces) { p.start = t; t += p.dur; }
  S.total = t;
}

/* ---------- drawing ---------- */

function buildPath(p, xa, xb, x2t, top, h, mini) {
  const src = mini ? p.miniSm : p.sm, n = src.length, line = new Path2D(), base = top + h;
  let first = true, lastX = xa;
  for (let x = xa; x <= xb; x++) {
    const ta = x2t(x) - p.start, tb = x2t(x + 1) - p.start;
    let i0 = cl(Math.floor(ta / HOP), 0, n - 1);
    const i1 = cl(Math.ceil(tb / HOP), i0, n - 1);
    const st = Math.max(1, Math.floor((i1 - i0) / 8));
    let mx = 0;
    for (let i = i0; i <= i1; i += st) if (src[i] > mx) mx = src[i];
    const y = base - yval(p, mx, mini) * h * TOP_FRAC;
    if (first) { line.moveTo(x, y); first = false; } else line.lineTo(x, y);
    lastX = x;
  }
  const fill = new Path2D(line);
  fill.lineTo(lastX, base); fill.lineTo(xa, base); fill.closePath();
  return { line, fill };
}

function paint(ctx, b, color, dimmed, playX, height, lw) {
  const stroke = alpha => {
    ctx.globalAlpha = alpha * 0.12; ctx.fillStyle = color; ctx.fill(b.fill);
    ctx.globalAlpha = alpha; ctx.strokeStyle = color; ctx.lineWidth = lw; ctx.lineJoin = 'round'; ctx.stroke(b.line);
  };
  if (!dimmed) { stroke(1); ctx.globalAlpha = 1; return; }
  stroke(0.25);
  ctx.save(); ctx.beginPath(); ctx.rect(0, 0, Math.max(0, playX), height); ctx.clip();
  stroke(1); ctx.restore(); ctx.globalAlpha = 1;
}

function rulerStep() {
  const steps = [1, 2, 5, 10, 15, 30, 60, 120, 300, 600, 1200];
  return steps.find(s => s * S.pxPerSec >= 80) || 1200;
}

function draw() {
  drawQueued = false;
  if (!W) return;
  const T = { bg: css('--panel'), fg: css('--fg'), muted: css('--muted'), line: css('--line'), soft: css('--soft'), accent: css('--accent') };
  g.setTransform(dpr, 0, 0, dpr, 0, 0);
  g.fillStyle = T.bg; g.fillRect(0, 0, W, H);
  const top = RULER_H + HEAD_H + 6, bottom = H - NOTES_H, plotH = bottom - top;
  g.font = '12px -apple-system, "Segoe UI", Roboto, sans-serif';

  if (!S.pieces.length) {
    g.fillStyle = T.muted; g.textAlign = 'center'; g.font = '15px -apple-system, "Segoe UI", Roboto, sans-serif';
    if (S.pending.length) {
      g.fillText('Session loaded. Use Find matching files above, or drop these files here:', W / 2, H / 2 - 20);
      S.pending.slice(0, 6).forEach((q, i) => g.fillText(q.file, W / 2, H / 2 + 6 + i * 22));
    } else {
      g.fillText('Drop audio files here, or use Add music', W / 2, H / 2);
    }
    g.textAlign = 'left';
    drawMini(T);
    return;
  }

  const vs = S.scroll, ve = xToTime(W);

  // ruler
  g.fillStyle = T.soft; g.fillRect(0, 0, W, RULER_H);
  g.strokeStyle = T.line; g.lineWidth = 1;
  g.beginPath(); g.moveTo(0, RULER_H + 0.5); g.lineTo(W, RULER_H + 0.5); g.stroke();
  const step = rulerStep();
  g.fillStyle = T.muted; g.textBaseline = 'middle';
  for (let t = Math.ceil(vs / step) * step; t <= ve; t += step) {
    const x = Math.round(timeToX(t)) + 0.5;
    g.strokeStyle = T.line; g.beginPath(); g.moveTo(x, RULER_H - 7); g.lineTo(x, RULER_H); g.stroke();
    g.fillText(fmt(t), x + 4, RULER_H / 2);
  }

  // baseline and separators
  g.strokeStyle = T.line;
  g.beginPath(); g.moveTo(0, bottom + 0.5); g.lineTo(W, bottom + 0.5); g.stroke();

  const playX = timeToX(S.playhead);
  for (const p of S.pieces) {
    const x0 = timeToX(p.start), x1 = timeToX(p.start + p.dur);
    if (x1 < 0 || x0 > W) continue;

    // header band
    g.globalAlpha = 0.18; g.fillStyle = p.color; g.fillRect(x0, RULER_H + 1, x1 - x0, HEAD_H); g.globalAlpha = 1;
    g.fillStyle = p.color; g.fillRect(x0, RULER_H + 1, x1 - x0, 3);
    const cb = closeBox(p);
    g.save(); g.beginPath(); g.rect(x0, RULER_H, x1 - x0 - (cb ? 24 : 0), HEAD_H); g.clip();
    g.fillStyle = T.fg; g.font = '500 13px -apple-system, "Segoe UI", Roboto, sans-serif';
    const tx = Math.max(x0 + 8, 6);
    g.fillText(p.title + '  ' + fmt(p.dur), Math.min(tx, x1 - 20), RULER_H + HEAD_H / 2 + 3);
    g.restore();
    if (cb) {
      g.strokeStyle = T.muted; g.lineWidth = 1.5;
      const cx = cb.x + cb.w / 2, cy = cb.y + cb.h / 2;
      g.beginPath(); g.moveTo(cx - 4, cy - 4); g.lineTo(cx + 4, cy + 4); g.moveTo(cx + 4, cy - 4); g.lineTo(cx - 4, cy + 4); g.stroke();
    }
    if (drag && drag.type === 'piece' && drag.p === p) {
      g.strokeStyle = p.color; g.lineWidth = 2; g.strokeRect(x0 + 1, RULER_H + 1, x1 - x0 - 2, HEAD_H + 1);
    }

    // separator
    g.strokeStyle = T.line; g.lineWidth = 1;
    g.beginPath(); g.moveTo(Math.round(x0) + 0.5, RULER_H); g.lineTo(Math.round(x0) + 0.5, H); g.stroke();

    // contour
    const a = Math.max(vs, p.start), b = Math.min(ve, p.start + p.dur);
    if (b > a) {
      const built = buildPath(p, Math.round(timeToX(a)), Math.round(timeToX(b)), xToTime, top, plotH);
      paint(g, built, p.color, S.dimmed, playX, H, 1.6);
    }
  }

  // notes
  const laneTop = bottom + 2;
  g.font = '12px -apple-system, "Segoe UI", Roboto, sans-serif';
  for (const n of S.notes) {
    const p = byId(n.pieceId);
    if (!p) { n.box = null; continue; }
    const x = timeToX(p.start + n.offset);
    const label = n.text ? (n.text.length > 30 ? n.text.slice(0, 29) + '…' : n.text) : '…';
    const w = g.measureText(label).width + 22;
    if (x < -w || x > W + 10) { n.box = null; continue; }
    g.strokeStyle = T.muted; g.globalAlpha = 0.5; g.setLineDash([2, 4]);
    g.beginPath(); g.moveTo(x + 0.5, top); g.lineTo(x + 0.5, laneTop); g.stroke();
    g.setLineDash([]); g.globalAlpha = 1;
    g.fillStyle = T.soft; g.strokeStyle = T.line;
    g.beginPath(); g.roundRect(x, laneTop + 2, w, NOTES_H - 8, 4); g.fill(); g.stroke();
    g.fillStyle = p.color; g.fillRect(x, laneTop + 2, 4, NOTES_H - 8);
    g.fillStyle = T.fg; g.fillText(label, x + 12, laneTop + NOTES_H / 2 - 1);
    n.box = { x, y: laneTop + 2, w, h: NOTES_H - 8 };
  }

  // playhead
  if (playX >= -1 && playX <= W + 1) {
    g.strokeStyle = T.fg; g.lineWidth = 1.5;
    g.beginPath(); g.moveTo(playX, RULER_H - 2); g.lineTo(playX, bottom); g.stroke();
    g.fillStyle = T.fg;
    g.beginPath(); g.moveTo(playX - 6, 2); g.lineTo(playX + 6, 2); g.lineTo(playX, 12); g.closePath(); g.fill();
  }
  drawMini(T);
}

function drawMini(T) {
  m.setTransform(dpr, 0, 0, dpr, 0, 0);
  m.fillStyle = T.bg; m.fillRect(0, 0, W, MH);
  if (!S.pieces.length) return;
  const top = 18, h = MH - top - 6;
  const x2t = x => (x / W) * S.total, t2x = t => (t / S.total) * W;
  const playX = t2x(S.playhead);
  m.font = '11px -apple-system, "Segoe UI", Roboto, sans-serif'; m.textBaseline = 'alphabetic';

  // view window
  const vx0 = t2x(S.scroll), vx1 = t2x(S.scroll + W / S.pxPerSec);
  m.fillStyle = T.accent; m.globalAlpha = 0.14; m.fillRect(vx0, 0, Math.max(2, vx1 - vx0), MH); m.globalAlpha = 1;
  m.strokeStyle = T.accent; m.lineWidth = 1; m.strokeRect(vx0 + 0.5, 0.5, Math.max(2, vx1 - vx0) - 1, MH - 1);

  for (const p of S.pieces) {
    const xa = Math.round(t2x(p.start)), xb = Math.round(t2x(p.start + p.dur));
    const built = buildPath(p, xa, xb, x2t, top, h, true);
    paint(m, built, p.color, S.dimmed, playX, MH, 1.2);
    m.strokeStyle = T.line; m.beginPath(); m.moveTo(xa + 0.5, 0); m.lineTo(xa + 0.5, MH); m.stroke();
    m.save(); m.beginPath(); m.rect(xa, 0, xb - xa, 16); m.clip();
    m.fillStyle = T.muted; m.fillText(p.title, xa + 4, 12); m.restore();
  }
  m.strokeStyle = T.fg; m.lineWidth = 1.2;
  m.beginPath(); m.moveTo(playX, 0); m.lineTo(playX, MH); m.stroke();
}

function redraw() {
  if (!drawQueued) { drawQueued = true; requestAnimationFrame(draw); }
}

function updateTime() {
  $('time').textContent = fmt(S.playhead) + ' / ' + fmt(S.total);
}

/* ---------- view: scroll and zoom ---------- */

function clampScroll() {
  S.scroll = cl(S.scroll, 0, Math.max(0, S.total - W / S.pxPerSec));
}

function syncZoom() {
  const mn = minPx();
  $('zoom').value = MAX_PX > mn ? cl(100 * Math.log(S.pxPerSec / mn) / Math.log(MAX_PX / mn), 0, 100) : 0;
  // minutes of music across the chart
  $('zoomNum').value = S.total ? +(W / S.pxPerSec / 60).toFixed(W / S.pxPerSec < 600 ? 2 : 1) : '';
}

function fit() {
  S.pxPerSec = minPx(); S.scroll = 0; atFit = true;
  syncZoom(); redraw();
}

function setZoom(px, anchorX) {
  const mn = minPx(), tAnchor = xToTime(anchorX);
  S.pxPerSec = cl(px, mn, Math.max(mn, MAX_PX));
  S.scroll = tAnchor - anchorX / S.pxPerSec;
  atFit = S.pxPerSec <= mn * 1.001;
  clampScroll(); syncZoom(); redraw();
}

function follow() {
  const x = timeToX(S.playhead), vw = W / S.pxPerSec;
  if (x > W * 0.92 || x < 0) { S.scroll = S.playhead - vw * 0.08; clampScroll(); }
}

/* ---------- playback ---------- */

function ensureAudio() {
  if (!audio) audio = new (window.AudioContext || window.webkitAudioContext)();
  return audio;
}

function stopSources() {
  for (const s of sources) { try { s.stop(); } catch (e) { /* already stopped */ } }
  sources = [];
}

function nowTime() {
  return S.playing ? Math.min(S.total, t0 + Math.max(0, audio.currentTime - c0)) : S.playhead;
}

function startAt(t) {
  stopSources();
  const ac = ensureAudio();
  const now = ac.currentTime + 0.05;
  for (const p of S.pieces) {
    if (t >= p.start + p.dur || !p.buffer) continue;
    const src = ac.createBufferSource();
    src.buffer = p.buffer; src.connect(ac.destination);
    src.start(now + Math.max(0, p.start - t), Math.max(0, t - p.start));
    sources.push(src);
  }
  c0 = now; t0 = t; S.playing = true; S.dimmed = true;
  $('play').textContent = 'Pause';
  tick();
}

function tick() {
  cancelAnimationFrame(raf);
  const step = () => {
    if (!S.playing) return;
    S.playhead = nowTime();
    if (S.playhead >= S.total) { pause(); return; }
    follow(); draw(); updateTime();
    raf = requestAnimationFrame(step);
  };
  raf = requestAnimationFrame(step);
}

function play() {
  if (!S.pieces.length) { status('Add some music first.'); return; }
  if (silent()) { status('Playback needs the audio files. Use Find matching files above the chart.'); return; }
  ensureAudio().resume();
  if (S.playhead >= S.total - 0.05) S.playhead = 0;
  startAt(S.playhead);
}

function pause() {
  if (S.playing) S.playhead = nowTime();
  S.playing = false; stopSources(); cancelAnimationFrame(raf);
  $('play').textContent = 'Play';
  redraw(); updateTime();
}

function stop() { pause(); S.dimmed = false; redraw(); }

function seek(t) {
  S.playhead = cl(t, 0, S.total);
  if (S.playing) startAt(S.playhead); else redraw();
  updateTime();
}

/* ---------- program: adding, ordering, editing ---------- */

async function addFiles(files, index) {
  const ac = ensureAudio();
  let at = index == null ? S.pieces.length : index;
  files = [...files];
  const failed = [];
  // decoding can't report its own progress, so the bar moves in steps: read, decoded, ready
  const fill = $('loadingFill');
  const progress = (i, f, frac) => {
    if ($('loading').hidden) {
      // start an empty bar without animating down from the last batch
      fill.style.transition = 'none'; fill.style.width = '0'; fill.offsetWidth; fill.style.transition = '';
      $('loading').hidden = false;
    }
    $('loadingText').textContent = (files.length > 1 ? 'Loading ' + (i + 1) + ' of ' + files.length + ': ' : 'Loading ') + f.name;
    fill.style.width = (100 * (i + frac) / files.length) + '%';
  };
  // a short timeout (not requestAnimationFrame, which stalls in background tabs) lets the bar repaint
  const paint = () => new Promise(r => setTimeout(r, 16));
  for (const [i, f] of files.entries()) {
    try {
      progress(i, f, 0.02);
      const data = await f.arrayBuffer();
      progress(i, f, 0.15);
      const buffer = await ac.decodeAudioData(data);
      progress(i, f, 0.85);
      await paint();
      // an opened session claims files by exact name first, then by name without extension
      const claimed = claimOf.get(f);
      const pend = (claimed && S.pending.includes(claimed) ? claimed : null)
        || S.pending.find(q => q.file.toLowerCase() === f.name.toLowerCase())
        || S.pending.find(q => baseName(q.file) === baseName(f.name));
      if (pend && pend.piece) {
        // already on the chart from its saved curve: the audio only makes it playable
        Object.assign(pend.piece, { buffer, src: f, file: f.name, handle: handleOf.get(f) || null });
        S.pending = S.pending.filter(q => q !== pend);
        if (Math.abs(buffer.duration - pend.piece.dur) > 2) {
          status(f.name + ' is ' + fmt(buffer.duration) + ' long but the session had ' + fmt(pend.piece.dur) + '. It may be a different recording.');
        } else refreshStatus();
        progress(i, f, 1);
        await paint();
        continue;
      }
      const id = pend ? pend.id : nextId++;
      const piece = {
        id, file: f.name, handle: handleOf.get(f) || null, title: pend ? pend.title : f.name.replace(/\.[^.]+$/, ''),
        color: pend ? pend.color : PALETTE[(id - 1) % PALETTE.length],
        buffer, src: f, dur: buffer.duration, env: envelope(buffer), sm: null, peak: 1, start: 0,
        sessionIdx: pend ? pend.sessionIdx : undefined,
      };
      if (S.playing) pause();
      if (pend) {
        S.pending = S.pending.filter(q => q !== pend);
        S.pieces.splice(S.pieces.filter(q => q.sessionIdx !== undefined && q.sessionIdx < pend.sessionIdx).length, 0, piece);
        if (Math.abs(buffer.duration - pend.dur) > 2) {
          status(f.name + ' is ' + fmt(buffer.duration) + ' long but the session had ' + fmt(pend.dur) + '. It may be a different recording.');
        }
      } else {
        S.pieces.splice(at++, 0, piece);
      }
      layout(); recompute(); fit(); updateTime();
      if (!pend || Math.abs(buffer.duration - pend.dur) <= 2) refreshStatus();
      progress(i, f, 1);
      await paint();
    } catch (err) {
      failed.push(f.name);
    }
  }
  $('loading').hidden = true;
  if (failed.length) status('Couldn’t open ' + failed.join(', ') + '. Try MP3, WAV, M4A, FLAC or OGG.');
}

function pieceAt(t) {
  return S.pieces.find(p => t >= p.start && t < p.start + p.dur) || S.pieces[S.pieces.length - 1];
}

function reorder(p, centerTime) {
  const others = S.pieces.filter(q => q !== p);
  let cum = 0, idx = 0;
  for (const o of others) { if (centerTime > cum + o.dur / 2) idx++; cum += o.dur; }
  if (S.pieces.indexOf(p) === idx) return;
  if (S.playing) pause();
  others.splice(idx, 0, p);
  S.pieces = others;
  layout(); redraw();
}

let undoTimer = 0;

function removePiece(p) {
  if (S.playing) pause();
  S.undo = { piece: p, index: S.pieces.indexOf(p), notes: S.notes.filter(n => n.pieceId === p.id),
    pending: S.pending.filter(q => q.piece === p) };
  S.pieces = S.pieces.filter(q => q !== p);
  S.pending = S.pending.filter(q => q.piece !== p);
  S.notes = S.notes.filter(n => n.pieceId !== p.id);
  layout(); recompute(); S.playhead = Math.min(S.playhead, S.total);
  fit(); updateTime(); showMissing();
  status('Removed “' + p.title + '”.');
  $('undo').hidden = false;
  clearTimeout(undoTimer);
  undoTimer = setTimeout(() => { S.undo = null; $('undo').hidden = true; refreshStatus(); }, 20000);
}

function undoRemove() {
  const u = S.undo;
  if (!u) return;
  S.undo = null; $('undo').hidden = true; clearTimeout(undoTimer);
  if (S.playing) pause();
  S.pieces.splice(Math.min(u.index, S.pieces.length), 0, u.piece);
  S.notes.push(...u.notes);
  S.pending.push(...u.pending);
  layout(); recompute(); fit(); updateTime(); refreshStatus();
}

/* ---------- sessions ---------- */

// the raw envelope goes into the session file as base64 of its 32-bit floats, so a reopened
// session draws exactly the same chart without the audio
function curveToText(env) {
  const bytes = new Uint8Array(env.buffer, env.byteOffset, env.byteLength);
  let s = '';
  for (let i = 0; i < bytes.length; i += 0x8000) s += String.fromCharCode.apply(null, bytes.subarray(i, i + 0x8000));
  return btoa(s);
}
function curveFromText(text) {
  const s = atob(text), bytes = new Uint8Array(s.length);
  for (let i = 0; i < s.length; i++) bytes[i] = s.charCodeAt(i);
  return new Float32Array(bytes.buffer, 0, bytes.length >> 2);
}
// a saved curve is usable only if it was made the same way this page makes one
function savedCurve(c) {
  if (!c || c.hop !== HOP || c.weighting !== 'A' || c.encoding !== 'f32-base64' || typeof c.data !== 'string') return null;
  try { const env = curveFromText(c.data); return env.length ? env : null; } catch (e) { return null; }
}

// pieces still without audio: either drawn from a saved curve (playable once found) or not drawn at all
const silent = () => S.pieces.some(p => !p.buffer);
function showPlayable() {
  $('play').disabled = silent();
  $('play').title = silent() ? 'Playback needs the audio files. Use Find matching files above the chart.' : '';
}

/* A session saved with audio is a plain .zip: session.json plus the original audio files under audio/.
   Entries are stored uncompressed (audio doesn't shrink), so any unzip tool can open it too. */
const CRC = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; }
  return t;
})();
function crc32(bytes) {
  let c = 0xFFFFFFFF;
  for (let i = 0; i < bytes.length; i++) c = CRC[(c ^ bytes[i]) & 0xFF] ^ (c >>> 8);
  return (c ^ 0xFFFFFFFF) >>> 0;
}

async function makeZip(entries) {          // entries: [{ name, blob }]
  const parts = [], central = [], enc = new TextEncoder();
  const now = new Date();
  const time = (now.getHours() << 11) | (now.getMinutes() << 5) | (now.getSeconds() >> 1);
  const date = ((now.getFullYear() - 1980) << 9) | ((now.getMonth() + 1) << 5) | now.getDate();
  let offset = 0;
  for (const e of entries) {
    const name = enc.encode(e.name), size = e.blob.size, crc = crc32(new Uint8Array(await e.blob.arrayBuffer()));
    const head = new DataView(new ArrayBuffer(30));
    [[0, 0x04034b50, 4], [4, 20, 2], [6, 0x0800, 2], [8, 0, 2], [10, time, 2], [12, date, 2], [14, crc, 4],
      [18, size, 4], [22, size, 4], [26, name.length, 2], [28, 0, 2]].forEach(([o, v, n]) => n === 4 ? head.setUint32(o, v, true) : head.setUint16(o, v, true));
    const dir = new DataView(new ArrayBuffer(46));
    [[0, 0x02014b50, 4], [4, 20, 2], [6, 20, 2], [8, 0x0800, 2], [10, 0, 2], [12, time, 2], [14, date, 2], [16, crc, 4],
      [20, size, 4], [24, size, 4], [28, name.length, 2], [30, 0, 2], [32, 0, 2], [34, 0, 2], [36, 0, 2], [38, 0, 4], [42, offset, 4]]
      .forEach(([o, v, n]) => n === 4 ? dir.setUint32(o, v, true) : dir.setUint16(o, v, true));
    parts.push(head, name, e.blob); central.push(dir, name);
    offset += 30 + name.length + size;
  }
  const cdSize = central.reduce((s, b) => s + b.byteLength, 0);
  const end = new DataView(new ArrayBuffer(22));
  [[0, 0x06054b50, 4], [4, 0, 2], [6, 0, 2], [8, entries.length, 2], [10, entries.length, 2], [12, cdSize, 4], [16, offset, 4], [20, 0, 2]]
    .forEach(([o, v, n]) => n === 4 ? end.setUint32(o, v, true) : end.setUint16(o, v, true));
  return new Blob([...parts, ...central, end], { type: 'application/zip' });
}

// returns Map name -> Blob; reads stored entries, and deflated ones where the browser can
async function readZip(file) {
  const tail = new DataView(await file.slice(Math.max(0, file.size - 65557)).arrayBuffer());
  let e = -1;
  for (let i = tail.byteLength - 22; i >= 0; i--) if (tail.getUint32(i, true) === 0x06054b50) { e = i; break; }
  if (e < 0) throw new Error('not a zip');
  const count = tail.getUint16(e + 10, true), cdSize = tail.getUint32(e + 12, true), cdOff = tail.getUint32(e + 16, true);
  const cd = new DataView(await file.slice(cdOff, cdOff + cdSize).arrayBuffer()), dec = new TextDecoder();
  const out = new Map();
  for (let i = 0, p = 0; i < count; i++) {
    const method = cd.getUint16(p + 10, true), comp = cd.getUint32(p + 20, true);
    const nl = cd.getUint16(p + 28, true), xl = cd.getUint16(p + 30, true), cl = cd.getUint16(p + 32, true), at = cd.getUint32(p + 42, true);
    const name = dec.decode(new Uint8Array(cd.buffer, p + 46, nl));
    p += 46 + nl + xl + cl;
    const lh = new DataView(await file.slice(at, at + 30).arrayBuffer());
    const start = at + 30 + lh.getUint16(26, true) + lh.getUint16(28, true);
    let blob = file.slice(start, start + comp);
    if (method === 8 && window.DecompressionStream) blob = await new Response(blob.stream().pipeThrough(new DecompressionStream('deflate-raw'))).blob();
    else if (method !== 0) continue;
    out.set(name, blob);
  }
  return out;
}

const download = (blob, name) => {
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob); a.download = name; a.click();
  setTimeout(() => URL.revokeObjectURL(a.href), 1000);
};

async function saveSession(withAudio) {
  if (S.pending.some(q => !q.piece)) { status('Add the remaining audio files before saving.'); return; }
  if (!S.pieces.length) { status('Nothing to save yet.'); return; }
  if (withAudio && S.pieces.some(p => !p.src)) {
    status('Saving with audio needs every piece’s audio. Add the missing files first, or use Save session.');
    return;
  }
  if (!S.sessionId) S.sessionId = crypto.randomUUID();
  let remembered = 0;
  if (canRemember && !withAudio) {
    for (const p of S.pieces) {
      if (!p.handle) continue;
      try { await idbPut(S.sessionId + ':' + p.id, p.handle); remembered++; } catch (e) { /* storage unavailable */ }
    }
  }
  // audio names inside the zip; two pieces from same-named files in different folders get a number
  const used = new Set();
  const audioName = p => {
    let n = p.file;
    for (let k = 2; used.has(n.toLowerCase()); k++) n = p.file.replace(/(\.[^.]+)?$/, ' (' + k + ')$1');
    used.add(n.toLowerCase());
    return 'audio/' + n;
  };
  const data = {
    app: 'MIA 2', version: 2, sessionId: S.sessionId, savedAt: new Date().toISOString(),
    settings: { smoothSec: S.smoothSec, scale: S.scaleMode, dB: S.dB },
    pieces: S.pieces.map(p => ({
      id: p.id, file: p.file, title: p.title, color: p.color, dur: +p.dur.toFixed(3),
      curve: { hop: HOP, weighting: 'A', encoding: 'f32-base64', data: curveToText(p.env) },
      ...(withAudio ? { audio: audioName(p) } : {}),
    })),
    notes: S.notes.filter(n => byId(n.pieceId)).map(n => ({ pieceId: n.pieceId, offset: +n.offset.toFixed(3), text: n.text })),
  };
  const json = new Blob([JSON.stringify(data, null, 2)], { type: 'application/json' });
  const stamp = 'mia-session-' + new Date().toISOString().slice(0, 10);
  if (!withAudio) {
    download(json, stamp + '.json');
    status('Session saved. It holds the chart, order, titles, colors and notes, but not the audio.'
      + (remembered ? ' This browser also remembered where ' + remembered + ' of the files are.' : ''));
    return;
  }
  status('Packing the audio…');
  let zip;
  try {
    zip = await makeZip([{ name: 'session.json', blob: json }, ...S.pieces.map((p, i) => ({ name: data.pieces[i].audio, blob: p.src }))]);
  } catch (e) {
    status('Couldn’t read one of the audio files to pack it. It may have been moved; add it again and retry.');
    return;
  }
  if (zip.size >= 0xFFFFFFFF) { status('That’s more than 4 GB of audio, too much for one session file.'); return; }
  download(zip, stamp + '.zip');
  status('Session saved with its audio (' + Math.round(zip.size / 1e6) + ' MB). Open it on any computer to get everything back, playback included.');
}

// look up remembered file locations for pending session pieces; interactive = called from a click
async function reconnect(interactive) {
  if (!canRemember || !S.sessionId || !S.pending.length) { $('reconnect').hidden = true; showMissing(); return; }
  const ready = [];
  let needPermission = 0;
  for (const q of [...S.pending]) {
    let h = null;
    try { h = await idbGet(S.sessionId + ':' + q.id); } catch (e) { /* storage unavailable */ }
    if (!h) continue;
    let perm = 'prompt';
    try { perm = await h.queryPermission({ mode: 'read' }); } catch (e) { /* unsupported */ }
    if (perm !== 'granted' && interactive) {
      try { perm = await h.requestPermission({ mode: 'read' }); } catch (e) { /* declined */ }
    }
    if (perm === 'granted') {
      try { const f = await h.getFile(); handleOf.set(f, h); claimOf.set(f, q); ready.push(f); } catch (e) { /* moved or deleted */ }
    } else needPermission++;
  }
  if (ready.length) await addFiles(ready);
  // Chrome asks again for each file after a reload unless "Allow on every visit" was chosen
  $('reconnect').hidden = !needPermission;
  $('reconnect').textContent = needPermission === 1 ? 'Reconnect 1 saved file' : 'Reconnect ' + needPermission + ' saved files';
  showMissing();
}

const AUDIO_EXT = /\.(mp3|wav|m4a|flac|ogg|aac|aif+)$/i;

// pair each pending piece with a file of the same name (exact first, then ignoring the extension)
function matchPending(entries) {
  const byName = new Map(), byBase = new Map();
  for (const e of entries) {
    const n = e.name.toLowerCase();
    if (!byName.has(n)) byName.set(n, e);
    if (!byBase.has(baseName(n))) byBase.set(baseName(n), e);
  }
  return S.pending.map(q => ({ q, e: byName.get(q.file.toLowerCase()) || byBase.get(baseName(q.file)) })).filter(m => m.e);
}

// walk a picked folder and its subfolders for audio files, stopping once every name is found
async function audioIn(dir, wanted, depth = 0, out = [], seen = { n: 0 }) {
  for await (const h of dir.values()) {
    if (++seen.n > 50000 || wanted.size === 0) break;
    if (h.kind === 'file' && AUDIO_EXT.test(h.name)) {
      out.push(h);
      wanted.delete(h.name.toLowerCase()); wanted.delete(baseName(h.name));
    } else if (h.kind === 'directory' && depth < 6 && !h.name.startsWith('.')) {
      await audioIn(h, wanted, depth + 1, out, seen);
    }
  }
  return out;
}

async function addMatches(matches, searched) {
  const total = S.pending.length;
  if (!matches.length) {
    status('None of the missing files are in ' + searched + '. Try the folder they were in when you made the session.');
    return;
  }
  const files = [];
  for (const { q, e } of matches) {
    const f = e.getFile ? await e.getFile() : e;
    if (e.getFile) handleOf.set(f, e);
    claimOf.set(f, q); files.push(f);
  }
  await addFiles(files);
  const left = S.pending.length;
  status('Found ' + matches.length + ' of ' + total + ' in ' + searched + '.'
    + (left ? ' Still missing ' + left + '; try another folder.' : ''));
}

async function findFiles() {
  if (!S.pending.length) return;
  if (!window.showDirectoryPicker) { $('folder').click(); return; }
  let dir;
  try {
    // the id makes Chrome reopen the picker in the last folder used
    dir = await window.showDirectoryPicker({ id: 'mia-audio', mode: 'read' });
  } catch (err) {
    if (err.name !== 'AbortError') $('folder').click();
    return;
  }
  status('Searching ' + dir.name + '…');
  const wanted = new Set(S.pending.flatMap(q => [q.file.toLowerCase(), baseName(q.file)]));
  let found = [];
  try { found = await audioIn(dir, wanted); } catch (e) { /* unreadable subfolder */ }
  await addMatches(matchPending(found), '“' + dir.name + '”');
}

async function openSession(file) {
  let data, bundle = null;
  try {
    // a session saved with audio is a zip (starts with "PK"); otherwise plain JSON
    const magic = new Uint8Array(await file.slice(0, 2).arrayBuffer());
    if (magic[0] === 0x50 && magic[1] === 0x4B) {
      bundle = await readZip(file);
      data = JSON.parse(await bundle.get('session.json').text());
    } else data = JSON.parse(await file.text());
  } catch (e) { data = null; }
  if (!data || data.app !== 'MIA 2' || !Array.isArray(data.pieces) || !data.pieces.length) {
    status('That doesn’t look like a MIA 2 session file.');
    return;
  }
  if (S.pieces.length && !confirm('Replace the current program with this session?')) return;
  if (S.playing) pause();
  S.pieces = []; S.notes = []; S.undo = null; $('undo').hidden = true;
  S.pending = data.pieces.map((p, i) => ({ id: p.id, file: p.file, title: p.title, color: p.color, dur: p.dur, sessionIdx: i }));
  // sessions saved with curves draw at once; older ones (and unreadable curves) wait for their audio as before
  S.pending.forEach((q, i) => {
    const env = savedCurve(data.pieces[i].curve);
    if (!env) return;
    q.piece = { id: q.id, file: q.file, handle: null, title: q.title, color: q.color, buffer: null,
      dur: +q.dur || env.length * HOP, env, sm: null, peak: 1, start: 0, sessionIdx: i };
    S.pieces.push(q.piece);
  });
  nextId = Math.max(nextId, ...data.pieces.map(p => p.id)) + 1;
  S.notes = (data.notes || []).map(n => ({ id: nextId++, pieceId: n.pieceId, offset: n.offset, text: n.text, box: null }));
  const st = data.settings || {};
  // sessions saved before smoothSec existed used a 0.05..3 s slider
  S.smoothSec = roundSec(st.smoothSec ? +st.smoothSec
    : st.smooth != null ? 0.05 * Math.pow(60, (100 - cl(+st.smooth, 0, 100)) / 100) : 3.5);
  S.scaleMode = st.scale === 'own' ? 'own' : 'program'; S.dB = !!st.dB;
  showSmooth(); $('scale').value = S.scaleMode; $('ydb').value = S.dB ? 'db' : 'lin';
  S.sessionId = data.sessionId || null;
  S.playhead = 0; layout(); recompute(); fit(); updateTime(); refreshStatus();
  if (bundle) {
    const files = [];
    S.pending.forEach((q, i) => {
      const b = data.pieces[i].audio && bundle.get(data.pieces[i].audio);
      if (!b) return;
      const f = new File([b], q.file);
      claimOf.set(f, q); files.push(f);
    });
    await addFiles(files);
  }
  await reconnect(false);
}

function place(pop, x, y) {
  pop.hidden = false;
  const w = pop.offsetWidth || 240;
  pop.style.left = cl(x, 4, Math.max(4, W - w - 4)) + 'px';
  pop.style.top = y + 'px';
}

function openPiece(p, x) {
  closePops();
  editingPiece = p;
  $('pTitle').value = p.title; $('pColor').value = p.color;
  place($('piecePop'), x, RULER_H + HEAD_H + 6);
  setTimeout(() => { $('pTitle').focus(); $('pTitle').select(); }, 0);
}

function openNote(n) {
  closePops();
  editingNote = n;
  $('nText').value = n.text;
  const p = byId(n.pieceId), x = timeToX(p.start + n.offset);
  place($('notePop'), x, H - NOTES_H - 92);
  setTimeout(() => $('nText').focus(), 0);   // the pointer release would otherwise take focus back
}

function closePops() {
  if (editingNote && !editingNote.text) S.notes = S.notes.filter(n => n !== editingNote);
  editingNote = null; editingPiece = null;
  $('piecePop').hidden = true; $('notePop').hidden = true;
  redraw();
}

function addNote(t) {
  const p = pieceAt(t);
  if (!p) return;
  const n = { id: nextId++, pieceId: p.id, offset: cl(t - p.start, 0, p.dur), text: '', box: null };
  S.notes.push(n);
  redraw(); openNote(n);
}

/* ---------- pointer input ---------- */

function pos(e) {
  const r = canvas.getBoundingClientRect();
  return { x: e.clientX - r.left, y: e.clientY - r.top };
}

function noteAt(x, y) {
  return S.notes.find(n => n.box && x >= n.box.x && x <= n.box.x + n.box.w && y >= n.box.y && y <= n.box.y + n.box.h);
}

canvas.addEventListener('pointerdown', e => {
  if (!S.pieces.length) return;
  const { x, y } = pos(e), t = xToTime(x);
  canvas.setPointerCapture(e.pointerId);
  if (y < RULER_H) { drag = { type: 'scrub' }; seek(t); return; }
  if (y < RULER_H + HEAD_H) {
    const p = pieceAt(t);
    if (!p) return;
    const cb = closeBox(p);
    if (cb && x >= cb.x && x <= cb.x + cb.w && y >= cb.y && y <= cb.y + cb.h) { removePiece(p); return; }
    drag = { type: 'piece', p, grab: t - p.start, x0: x, moved: false };
    return;
  }
  const nb = noteAt(x, y);
  if (nb) { openNote(nb); return; }
  if (S.notesMode) { addNote(t); return; }
  drag = { type: 'pan', x0: x, scroll0: S.scroll, moved: false };
});

canvas.addEventListener('pointermove', e => {
  const { x, y } = pos(e);
  if (!drag) {
    canvas.style.cursor = y < RULER_H ? 'col-resize' : y < RULER_H + HEAD_H ? 'grab' : S.notesMode ? 'crosshair' : noteAt(x, y) ? 'pointer' : 'default';
    return;
  }
  if (drag.type === 'scrub') seek(xToTime(x));
  else if (drag.type === 'piece') {
    if (Math.abs(x - drag.x0) > 3) drag.moved = true;
    if (drag.moved) { canvas.style.cursor = 'grabbing'; reorder(drag.p, xToTime(x) - drag.grab + drag.p.dur / 2); }
  } else if (drag.type === 'pan') {
    if (Math.abs(x - drag.x0) > 4) drag.moved = true;
    if (drag.moved) { S.scroll = drag.scroll0 - (x - drag.x0) / S.pxPerSec; clampScroll(); redraw(); }
  }
});

const endDrag = e => {
  if (drag && drag.type === 'pan' && !drag.moved) seek(xToTime(pos(e).x));
  drag = null; redraw();
};
canvas.addEventListener('pointerup', endDrag);
canvas.addEventListener('pointercancel', () => { drag = null; redraw(); });

canvas.addEventListener('dblclick', e => {
  const { x, y } = pos(e);
  if (y >= RULER_H && y < RULER_H + HEAD_H && S.pieces.length) openPiece(pieceAt(xToTime(x)), x);
});

canvas.addEventListener('wheel', e => {
  if (!S.pieces.length) return;
  e.preventDefault();
  const { x } = pos(e);
  if (e.ctrlKey || e.metaKey || e.altKey) {
    setZoom(S.pxPerSec * Math.exp(-e.deltaY * (e.ctrlKey ? 0.01 : 0.002)), x);
  } else {
    const d = Math.abs(e.deltaX) > Math.abs(e.deltaY) ? e.deltaX : e.deltaY;
    S.scroll += d / S.pxPerSec; clampScroll(); redraw();
  }
}, { passive: false });

// mini-map: drag the window to scroll, click elsewhere to jump
mini.addEventListener('pointerdown', e => {
  if (!S.pieces.length) return;
  const r = mini.getBoundingClientRect(), x = e.clientX - r.left, t = (x / W) * S.total;
  mini.setPointerCapture(e.pointerId);
  const vw = W / S.pxPerSec;
  if (t >= S.scroll && t <= S.scroll + vw) drag = { type: 'mini', off: t - S.scroll };
  else { seek(t); S.scroll = t - vw / 2; clampScroll(); redraw(); }
});
mini.addEventListener('pointermove', e => {
  if (!drag || drag.type !== 'mini') return;
  const r = mini.getBoundingClientRect(), t = ((e.clientX - r.left) / W) * S.total;
  S.scroll = t - drag.off; clampScroll(); redraw();
});
mini.addEventListener('pointerup', () => { drag = null; });

/* ---------- toolbar and page wiring ---------- */

$('add').onclick = async () => {
  if (!canRemember) { $('file').click(); return; }
  try {
    // the picker hands back file handles, which lets a saved session find these files again
    const handles = await window.showOpenFilePicker({
      multiple: true,
      types: [{ description: 'Audio', accept: { 'audio/*': ['.mp3', '.wav', '.m4a', '.flac', '.ogg', '.aac', '.aif', '.aiff'] } }],
    });
    const files = [];
    for (const h of handles) { const f = await h.getFile(); handleOf.set(f, h); files.push(f); }
    addFiles(files);
  } catch (err) {
    if (err.name !== 'AbortError') $('file').click();
  }
};
$('reconnect').onclick = () => reconnect(true);
$('findFiles').onclick = findFiles;
$('folder').onchange = async e => {
  const files = [...e.target.files].filter(f => AUDIO_EXT.test(f.name));
  e.target.value = '';
  await addMatches(matchPending(files), 'that folder');
};
$('openSession').onclick = () => $('sessionFile').click();
$('sessionFile').onchange = e => { if (e.target.files[0]) openSession(e.target.files[0]); e.target.value = ''; };
$('saveSession').onclick = () => saveSession(false);
$('saveAudio').onclick = () => saveSession(true);
$('undo').onclick = undoRemove;
$('file').onchange = e => { addFiles([...e.target.files]); e.target.value = ''; };
$('play').onclick = () => (S.playing ? pause() : play());
$('stop').onclick = stop;
$('fit').onclick = fit;
showSmooth(); $('scale').value = S.scaleMode;
$('smooth').oninput = e => { S.smoothSec = roundSec(smoothSec(+e.target.value)); $('smoothNum').value = S.smoothSec.toFixed(1); recompute(); redraw(); };
$('smoothNum').onchange = e => {
  const v = parseFloat(e.target.value);
  if (v > 0) { S.smoothSec = roundSec(v); recompute(); redraw(); }
  showSmooth();
};
$('zoom').oninput = e => {
  const mn = minPx(), px = mn * Math.pow(Math.max(1, MAX_PX / mn), e.target.value / 100);
  setZoom(px, S.playing ? Math.min(W - 40, Math.max(40, timeToX(S.playhead))) : W / 2);
};
$('zoomNum').onchange = e => {
  const v = parseFloat(e.target.value);
  if (v > 0 && S.total) setZoom(W / (v * 60), S.playing ? Math.min(W - 40, Math.max(40, timeToX(S.playhead))) : W / 2);
  else syncZoom();
};
$('notes').onclick = e => {
  S.notesMode = !S.notesMode;
  e.currentTarget.setAttribute('aria-pressed', String(S.notesMode));
  status(S.notesMode ? 'Notes mode: click the chart to add a note. Click a note to edit it.' : '');
};
$('scale').onchange = e => { S.scaleMode = e.target.value; redraw(); };
$('ydb').onchange = e => { S.dB = e.target.value === 'db'; redraw(); };
$('print').onclick = () => window.print();
$('save').onclick = () => {
  if (!S.pieces.length) { status('Nothing to save yet.'); return; }
  draw();
  const o = document.createElement('canvas');
  o.width = canvas.width; o.height = canvas.height + mini.height;
  const oc = o.getContext('2d');
  oc.fillStyle = css('--panel'); oc.fillRect(0, 0, o.width, o.height);
  oc.drawImage(canvas, 0, 0); oc.drawImage(mini, 0, canvas.height);
  o.toBlob(b => {
    const a = document.createElement('a');
    a.href = URL.createObjectURL(b); a.download = 'mia-chart.png'; a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 1000);
  });
};

$('pTitle').oninput = e => { if (editingPiece) { editingPiece.title = e.target.value; redraw(); } };
$('pColor').oninput = e => { if (editingPiece) { editingPiece.color = e.target.value; redraw(); } };
$('pRemove').onclick = () => { const p = editingPiece; closePops(); if (p) removePiece(p); };
$('pDone').onclick = closePops;
$('nText').oninput = e => { if (editingNote) { editingNote.text = e.target.value; redraw(); } };
$('nText').onkeydown = e => { if (e.key === 'Enter' || e.key === 'Escape') closePops(); };
$('pTitle').onkeydown = e => { if (e.key === 'Enter' || e.key === 'Escape') closePops(); };
$('nDelete').onclick = () => { S.notes = S.notes.filter(n => n !== editingNote); editingNote = null; closePops(); };
$('nDone').onclick = closePops;

window.addEventListener('dragover', e => e.preventDefault());
window.addEventListener('drop', async e => {
  e.preventDefault();
  // the drop's items are only readable during this event, so take files and handles now
  const dropped = [...e.dataTransfer.items].filter(i => i.kind === 'file').map(i => ({
    file: i.getAsFile(),
    handle: i.getAsFileSystemHandle ? i.getAsFileSystemHandle().catch(() => null) : null,
  })).filter(d => d.file);
  const sess = dropped.find(d => /\.(json|zip)$/i.test(d.file.name));
  if (sess) { openSession(sess.file); return; }
  const audioDrops = dropped.filter(d => d.file.type.startsWith('audio/') || /\.(mp3|wav|m4a|flac|ogg|aac|aif+)$/i.test(d.file.name));
  if (!audioDrops.length) return;
  for (const d of audioDrops) {
    const h = d.handle && await d.handle;
    if (h && h.kind === 'file') handleOf.set(d.file, h);
  }
  const files = audioDrops.map(d => d.file);
  let idx = null;
  const r = canvas.getBoundingClientRect();
  if (S.pieces.length && e.clientY >= r.top && e.clientY <= r.bottom) {
    const t = xToTime(e.clientX - r.left), p = pieceAt(t);
    idx = S.pieces.indexOf(p) + (t > p.start + p.dur / 2 ? 1 : 0);
  }
  addFiles(files, idx);
});

window.addEventListener('keydown', e => {
  if (/^(INPUT|SELECT|TEXTAREA)$/.test(e.target.tagName)) return;
  if ((e.metaKey || e.ctrlKey) && e.code === 'KeyZ' && S.undo) { e.preventDefault(); undoRemove(); }
  else if (e.code === 'Space') { e.preventDefault(); S.playing ? pause() : play(); }
  else if (e.code === 'ArrowLeft') seek(S.playhead - 5);
  else if (e.code === 'ArrowRight') seek(S.playhead + 5);
  else if (e.code === 'Home') { seek(0); S.scroll = 0; redraw(); }
});

function resize() {
  const w = Math.max(320, Math.floor(canvas.parentElement.getBoundingClientRect().width));
  const ratio = window.devicePixelRatio || 1;
  if (w === W && ratio === dpr) return;
  W = w; dpr = ratio;
  for (const [cv, h] of [[canvas, H], [mini, MH]]) {
    cv.width = Math.round(W * dpr); cv.height = Math.round(h * dpr);
    cv.style.width = W + 'px'; cv.style.height = h + 'px';
  }
  if (atFit) fit(); else { clampScroll(); syncZoom(); }
  redraw();
}

new ResizeObserver(resize).observe($('stage'));
window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', redraw);
resize();
updateTime();

window.MIA = { S, addFiles, seek, play, pause, saveSession, openSession, removePiece, undoRemove, handleOf };
})();
