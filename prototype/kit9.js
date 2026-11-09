// =====================================================================
//  Shared engine for Acts 9 to 12 (act9.js ... act12.js)
// =====================================================================
// Every act from 9 on describes itself to makeAct(spec) and gets the full engine interface the game
// expects (the same one ACT8 has: apply, isSolved, makeEquation, makeHand, isCorrect, whyWrong, animFor,
// label/text/kind/icon, autoTarget, onDrag, render, prompt, buildFight...). It registers through
// registerAct() in index.html, so index.html needs no new clause when an act is added.
//
// An act's spec:
//   act, sk (state kind key, e.g. 'k9'), key (what generators return, e.g. 'r9'), tag (card flag, 'a9')
//   moves(e)            the legal moves: [{ op, refs?, both?, ...params }]. The first one is the canonical
//                       next move (par). A move with refs is a ◎ card dropped on one of those parts.
//   ok(e, m, c, ref)    does card c do move m (its payload: the value, form or choice the player picked)?
//   apply(r, m, c, ref) applies move m with card c to r (a clone), returns the new state
//   CARD[op](c)         { label, text, kind, icon } for a card
//   BOTH, COPY          sets of ops: ⇔ both-sides cards / copy-only moves ("Do the math" skips them)
//   PARAMS              payload keys copied from a move onto its card
//   specials(e)         { rule: [cards], traps: [cards] }: rule decoys at every level, Expert traps
//   family(e)           the stage's other cards, from which wrong ones are drawn
//   places(e, op)       where a ◎ card of that kind could go when it isn't legal anywhere
//   why(e, card, ref, S, next, long)   the wrong-move reason (S(short, long) picks the length)
//   render(e, el, H)    draws the state into #equation; graph(e) optionally draws the graph panel
//   anim[op](c, s, ns, ref, H)          the animation of each operation
//   answer(e, html), textOf(e), promptKey(e), PR, HOME (op -> skill)
//   gens, hard (cases for elites), skills, enemies, actInfo, icons, css, elite, boss, bossLast()
'use strict';
(function () {
  const A4 = window.ACT4;
  if (!A4 || !A4.kit || typeof registerAct !== 'function') return;
  const K = A4.kit;
  const { TOK, EQTOK, refOf, kickClass, clone, fNeg, fSub, fDiv, fEq, fz, fv } = K;
  const P = t => `<p>${t}</p>`;
  const isTutorial = K.isTutorial, lvl = K.lvl;
  const chance = p => Math.random() < p;
  const qid = () => Math.random().toString(36).slice(2, 8);
  const FN = v => (v === undefined || v === null ? v : typeof v === 'number' ? F(v) : v);

  // ================================================================ numbers and text
  const SUPD = '⁰¹²³⁴⁵⁶⁷⁸⁹';
  const supT = n => (n < 0 ? '⁻' : '') + String(Math.abs(n)).split('').map(d => SUPD[+d]).join('');
  // Exponents are written in <sup class="nonum">, so "Do the math" doesn't ask for them.
  const supH = h => `<sup class="nonum e9">${h}</sup>`;
  const XV = (v = 'x') => `<i class="xv">${v}</i>`;
  const numH = (f, html) => (html ? fracHtml(FN(f)) : fracText(FN(f)));
  const parenF = (f, html) => { f = FN(f); return f.n < 0 || f.d > 1 ? `(${numH(f, html)})` : numH(f, html); };
  // A number as a decimal when it ends (1/4 -> 0.25), else as a fraction.
  function decT(f) {
    f = FN(f); let d = f.d; while (d % 2 === 0) d /= 2; while (d % 5 === 0) d /= 5;
    if (d !== 1) return fracText(f);
    const v = f.n / f.d, s = String(+v.toFixed(6));
    return s.startsWith('-') ? MINUS + s.slice(1) : s;
  }
  const isDec = f => { let d = FN(f).d; while (d % 2 === 0) d /= 2; while (d % 5 === 0) d /= 5; return d === 1; };
  const frH = (top, bot, cls = '') => `<span class="frac f9 ${cls}"><span>${top}</span><span>${bot}</span></span>`;
  const sgnJoin = (terms, html) => terms.length ? terms.map((t, i) => (i ? (t.neg ? ` ${MINUS} ` : ' + ') : t.neg ? MINUS : '') + t.s).join('') : '0';

  // ---------------------------------------------------------------- polynomials (dense, index = power)
  const ptrim = p => { const q = p.map(FN); while (q.length > 1 && fz(q[q.length - 1])) q.pop(); return q.length ? q : [F(0)]; };
  const pdeg = p => ptrim(p).length - 1;
  const pco = (p, i) => (p[i] ? FN(p[i]) : F(0));
  const padd = (a, b) => ptrim(Array.from({ length: Math.max(a.length, b.length) }, (_, i) => fAdd(pco(a, i), pco(b, i))));
  const pscale = (p, k) => ptrim(p.map(c => fMul(FN(c), FN(k))));
  const psub = (a, b) => padd(a, pscale(b, F(-1)));
  const pmul = (a, b) => { const out = Array.from({ length: a.length + b.length - 1 }, () => F(0)); a.forEach((x, i) => b.forEach((y, j) => { out[i + j] = fAdd(out[i + j], fMul(FN(x), FN(y))); })); return ptrim(out); };
  const peval = (p, v) => p.reduce((acc, c, i) => fAdd(acc, fMul(FN(c), fpow(FN(v), i))), F(0));
  const pEq = (a, b) => { a = ptrim(a); b = ptrim(b); return a.length === b.length && a.every((c, i) => fEq(c, b[i])); };
  const P1 = (a, b) => ptrim([FN(b), FN(a)]);          // a·x + b
  const fpow = (f, n) => { let r = F(1); for (let i = 0; i < Math.abs(n); i++) r = fMul(r, f); return n < 0 ? fDiv(F(1), r) : r; };
  // c₀ + c₁x + c₂x² written from the top power down: "2x² − 5x + 3"
  function ptext(p, html, v = 'x') {
    const X = html ? XV(v) : v, ts = [];
    for (let i = p.length - 1; i >= 0; i--) {
      const c = FN(p[i]); if (fz(c)) continue;
      const a = fAbs(c), body = i === 0 ? '' : X + (i === 1 ? '' : html ? supH(i) : supT(i));
      ts.push({ neg: c.n < 0, s: (fIs(a, 1) && body ? '' : numH(a, html)) + body });
    }
    return sgnJoin(ts, html);
  }
  const pterms = p => ptrim(p).filter(c => !fz(c)).length;

  // ---------------------------------------------------------------- number line (SVG)
  // nl: { lo, hi, pts: [{ x, open, lab, cls }], shade: [[a, b]] (null = ±∞), tests: [{ x, ok }], targets: bool,
  //       ivs: the intervals between critical points (for targets) }
  function numberLine(nl) {
    const W = 300, H = 62, pad = 18, span = nl.hi - nl.lo;
    const X = x => +(pad + (W - 2 * pad) * (Math.max(nl.lo, Math.min(nl.hi, x)) - nl.lo) / span).toFixed(2);
    let s = `<svg class="nl9" viewBox="0 0 ${W} ${H}" width="${W}" height="${H}">`;
    s += `<line class="nlAx9" x1="4" y1="30" x2="${W - 4}" y2="30"/><path class="nlAx9" d="M${W - 10} 25L${W - 3} 30L${W - 10} 35M10 25L3 30L10 35" fill="none"/>`;
    const step = span <= 14 ? 1 : span <= 30 ? 2 : 5;
    for (let t = Math.ceil(nl.lo / step) * step; t <= nl.hi; t += step) s += `<line class="nlTk9" x1="${X(t)}" y1="25" x2="${X(t)}" y2="35"/>` + (nl.labels !== false && t % (step * 2) === 0 ? `<text class="nlNum9" x="${X(t)}" y="50">${numText(t)}</text>` : '');
    for (const [a, b] of nl.shade || []) s += `<line class="nlSh9" x1="${a === null ? 4 : X(a)}" y1="30" x2="${b === null ? W - 4 : X(b)}" y2="30"/>`;
    if (nl.ivs && nl.targets) nl.ivs.forEach((iv, i) => {
      const a = iv[0] === null ? 4 : X(iv[0]), b = iv[1] === null ? W - 4 : X(iv[1]);
      s += `<rect class="tg9 nlIv9 ${iv.cls || ''}" data-ref="I${i}" x="${a + 3}" y="8" width="${Math.max(6, b - a - 6)}" height="40" rx="6"/>`;
    });
    for (const t of nl.tests || []) s += `<g class="nlT9 ${t.ok === true ? 'ok' : t.ok === false ? 'no' : ''}"><circle cx="${X(t.x)}" cy="16" r="5"/><text x="${X(t.x)}" y="11" class="nlTl9">${t.ok === true ? '✓' : t.ok === false ? '✗' : '?'}</text></g>`;
    for (const p of nl.pts || []) {
      s += `<circle class="nlPt9 ${p.open ? 'open' : 'closed'} ${p.cls || ''}" cx="${X(p.x)}" cy="30" r="6"/>`;
      if (p.lab !== undefined) s += `<text class="nlPl9" x="${X(p.x)}" y="60">${p.lab}</text>`;
    }
    return s + '</svg>';
  }
  const nlWindow = xs => { const lo = Math.floor(Math.min(...xs, 0)) - 2, hi = Math.ceil(Math.max(...xs, 0)) + 2; const w = Math.max(hi - lo, 8); const c = (lo + hi) / 2; return { lo: Math.floor(c - w / 2), hi: Math.ceil(c + w / 2) }; };

  // ---------------------------------------------------------------- graph panel curves
  // Draws Act 4's graph panel (axes, grid, dots, lines) and adds curves: { f: x => y } or { pts: [[x, y]] }.
  function drawCurves(gs) {
    K.drawGraph({ win: gs.win, pts: [], lines: gs.lines || [], marks: gs.marks || [], labels: false, targets: false, qid: gs.qid || '' });
    const svg = $('graph').querySelector('svg'); if (!svg) return;
    const sig = (gs.qid || '') + JSON.stringify(gs.win) + JSON.stringify(gs.curves.map(c => c.key || c.cls));
    if (svg.dataset.c9 === sig) return;            // already drawn: don't restart the animation
    svg.dataset.c9 = sig;
    const keep = new Set(gs.curves.map(c => (gs.qid || '') + (c.key || c.cls)));
    svg.querySelectorAll('.gC9').forEach(n => { if (!keep.has(n.dataset.k) || n.dataset.w !== JSON.stringify(gs.win)) n.remove(); });
    const Wd = 260, pad = 12, { x0, x1, y0, y1 } = gs.win, span = Math.max(x1 - x0, y1 - y0), s = (Wd - 2 * pad) / span;
    const cx = (x0 + x1) / 2, cy = (y0 + y1) / 2, vx0 = cx - span / 2, vx1 = cx + span / 2, vy0 = cy - span / 2, vy1 = cy + span / 2;
    const Xs = x => (Wd / 2 + (x - cx) * s).toFixed(2), Ys = y => (Wd / 2 - (y - cy) * s).toFixed(2);
    const firstDot = svg.querySelector('.gDot');
    if (!svg.querySelector('#clip9')) { const NS = 'http://www.w3.org/2000/svg', cp = document.createElementNS(NS, 'clipPath'), rc = document.createElementNS(NS, 'rect'); cp.id = 'clip9'; [['x', 0], ['y', 0], ['width', Wd], ['height', Wd]].forEach(([k, v]) => rc.setAttribute(k, v)); cp.appendChild(rc); svg.appendChild(cp); }
    for (const c of gs.curves) {
      const k = (gs.qid || '') + (c.key || c.cls);
      if ([...svg.querySelectorAll('.gC9')].some(n => n.dataset.k === k && n.dataset.w === JSON.stringify(gs.win))) continue;
      let d = '', pen = false;
      const pts = c.pts || Array.from({ length: 241 }, (_, i) => { const x = vx0 + (vx1 - vx0) * i / 240; return [x, c.f(x)]; });
      for (const [x, y] of pts) {
        if (!Number.isFinite(y) || y < vy0 - 3 || y > vy1 + 3) { pen = false; continue; }
        d += (pen ? 'L' : 'M') + Xs(x) + ' ' + Ys(y) + ' '; pen = true;
      }
      const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
      path.setAttribute('d', d); path.setAttribute('class', 'gC9 ' + (c.cls || '')); path.setAttribute('pathLength', '1'); path.setAttribute('clip-path', 'url(#clip9)'); path.dataset.k = k; path.dataset.w = JSON.stringify(gs.win);
      svg.insertBefore(path, firstDot || null);
    }
  }
  const square = (cx, cy, r) => ({ x0: Math.floor(cx - r), x1: Math.ceil(cx + r), y0: Math.floor(cy - r), y1: Math.ceil(cy + r) });

  // ---------------------------------------------------------------- shared animation helpers
  const tk = ref => $('equation').querySelector(`[data-ref="${ref}"]`);
  const H = {
    tk,
    async written(html, anchors, cap, cls = 'lift4') {
      if (cap) caption(cap);
      const n = note(html, anchors.filter(Boolean)); n.classList.add(cls, 'n9');
      await quick(150); await hold();
      return n;
    },
    async both(html, refs, cap) {   // the same operation written under each side
      if (cap) caption(cap);
      const ns = refs.map(tk).filter(Boolean).map(a => { const n = note(html, [a]); n.classList.add('lift4', 'n9'); return n; });
      await quick(150); await hold();
      ns.forEach(dropNote);
    },
    fly(html, from, toEl, ms = 480) {
      if (!from || !toEl) return quick(1);
      const dest = toEl.getBoundingClientRect();
      const chip = document.createElement('div'); chip.className = 'fly4 fly9'; chip.innerHTML = html;
      chip.style.left = (from.left + from.width / 2) + 'px'; chip.style.top = (from.top + from.height / 2) + 'px';
      document.body.appendChild(chip); void chip.offsetWidth;
      chip.style.transform = `translate(${dest.left + dest.width / 2 - from.left - from.width / 2}px, ${dest.top + dest.height / 2 - from.top - from.height / 2}px)`;
      return quick(ms).then(() => chip.remove());
    },
    mark(refs, cls = 'hot9') { refs.map(tk).forEach(t => t && t.classList.add(cls)); },
    cls(refs, cls) { refs.map(tk).forEach(t => t && t.classList.add(cls)); },
  };

  // ================================================================ the engine
  function makeAct(spec) {
    const tag = spec.tag, sk = spec.sk, flag = 'act' + spec.act;
    const BOTH = spec.BOTH || new Set(), COPY = spec.COPY || new Set(), PARAMS = spec.PARAMS || [];
    const C = (op, o = {}) => ({ op, [tag]: true, scope: BOTH.has(op) ? 'both' : 'part', ...(COPY.has(op) ? { copy: true } : {}), ...o });
    const trap = (name, like, label, text, why, icon, scope = 'part') => ({ op: 'trap', [tag]: true, trap: name, like, scope, label, text, why, icon });
    const moveCard = m => { const c = C(m.op); for (const k of PARAMS) if (m[k] !== undefined) c[k] = clone(m[k]); return c; };
    const movesOf = e => (e && e[sk] ? spec.moves(e) : []);
    const okP = (e, m, c, ref) => (spec.ok ? spec.ok(e, m, c, ref) : true);
    function legalMove(e, c, ref) {
      if (!c || !c[tag] || c.op === 'trap') return null;
      return movesOf(e).find(m => m.op === c.op && (m.both || !m.refs || m.refs.includes(ref)) && okP(e, m, c, ref)) || null;
    }
    const correct = (e, c, target) => !!legalMove(e, c, refOf(target));
    function applyA(e, c, ref) {
      const r = clone(e);
      const m = legalMove(e, c, ref) || movesOf(e).find(o => o.op === (c && c.op) && okP(e, o, c, o.refs ? o.refs[0] : null)) || movesOf(e).find(o => o.op === (c && c.op));
      if (!m || !c || c.op === 'trap') return r;
      const at = ref && m.refs && m.refs.includes(ref) ? ref : m.refs ? m.refs[0] : null;
      return spec.apply(r, m, c, at);
    }
    const isSolved = e => !movesOf(e).length;
    const canon = e => { const m = movesOf(e)[0]; return m ? { ...moveCard(m), ref: m.refs ? m.refs[0] : null } : null; };
    const skillFor = (m, main) => { const home = (spec.HOME || {})[m.op] || main; return home === main || isUnlocked(home) ? home : main; };
    function pathOf(e, main) {
      const path = []; let s = e;
      for (let i = 0; i < 80; i++) { const m = canon(s); if (!m) break; path.push({ state: s, move: m, skill: skillFor(m, main) }); s = applyA(s, m, m.ref); }
      return { path, end: s };
    }
    function makeEquation(state, enemy) {
      const main = state.skill, { path, end } = pathOf(state, main);
      return { start: state, end, path, main, skills: [...new Set(path.map(p => p.skill))], enemy, act2: true, [flag]: true, answer: F(0), answerText: spec.answer(end, false) };
    }
    function refreshPath(cur) { cur.path = cur.path.slice(0, cur.step).concat(pathOf(cur.state, cur.main).path); }
    // A card that one more move would accept is also right: it isn't dealt as a wrong card.
    const alsoRight = (e, c) => c.op !== 'trap' && movesOf(e).some(m => m.op === c.op && okP(e, m, c, m.refs ? m.refs[0] : null) && (!m.refs || m.refs.length)
      || (m.refs && m.op === c.op && m.refs.some(r => okP(e, m, c, r))));
    const DECOYS = [1, 1, 2, 2];
    function makeHand(e, correctCard, size) {
      const tut = isTutorial(), L = lvl();
      const hand = [correctCard], seen = new Set([cardLabel(correctCard)]);
      const add = c => {
        if (!c || hand.length >= size) return;
        const k = cardLabel(c); if (seen.has(k)) return;
        if (alsoRight(e, c)) return;
        seen.add(k); hand.push(c);
      };
      const sp = spec.specials ? spec.specials(e) : { rule: [], traps: [] };
      if (!tut && L >= 3) (sp.traps || []).slice(0, 1).forEach(add);
      if (!tut) (sp.rule || []).slice(0, DECOYS[L]).forEach(add);
      shuffle(spec.family(e)).forEach(add);
      (spec.filler ? spec.filler(e) : []).forEach(add);
      return shuffle(hand);
    }
    // ---------------------------------------------------------------- card faces
    const info = c => (c && c[tag] && c.op !== 'trap' && spec.CARD[c.op] ? spec.CARD[c.op](c) : null);
    const label = c => (c && c[tag] && c.op === 'trap' ? `<span class="clong l9">${c.label}</span>` : info(c) ? `<span class="clong l9">${info(c).label}</span>` : null);
    const text = c => (c && c[tag] && c.op === 'trap' ? c.text : info(c) ? info(c).text : null);
    const kind = c => (c && c[tag] && c.op === 'trap' ? 'Trap: ' + c.trap : info(c) ? info(c).kind : null);
    const icon = c => (c && c[tag] && c.op === 'trap' ? c.icon : info(c) ? info(c).icon : null);
    const targetSel = c => (c && c[tag] && (c.scope || 'both') === 'part' ? (spec.sel && spec.sel(c)) || '#equation [data-ref].tok, #equation [data-ref].tg9' : null);
    function places(e, c) {
      const op = c.op === 'trap' ? c.like : c.op;
      if (!op) return [];
      const legal = movesOf(e).filter(m => m.op === op && m.refs);
      if (legal.length && c.op !== 'trap') {
        const fit = legal.filter(m => m.refs.some(r => okP(e, m, c, r)));
        return [...new Set((fit.length ? fit : legal).flatMap(m => m.refs))];
      }
      return spec.places ? spec.places(e, op) : [];
    }
    function autoTarget(c) {
      if (!cur || !cur[flag] || !c[tag]) return 'pass';
      const ps = places(cur.state, c);
      if (ps.length >= 2) return undefined;
      if (!ps.length) return null;
      return tk(ps[0]) || ps[0];
    }
    function onDrag(c, on) {
      document.querySelectorAll('.ok9').forEach(el => el.classList.remove('ok9'));
      if (!on || !cur || !cur[flag]) return;
      const hl = difficulty.highlight === 'on' || isTutorial() || (difficulty.highlight === 'afterWrong' && cur.wrong > 0);
      if (!hl || !targetSel(c)) return;
      for (const el of document.querySelectorAll('#equation [data-ref]')) if (correct(cur.state, c, el)) el.classList.add('ok9');
    }
    // ---------------------------------------------------------------- wrong moves
    const S = long => (short, more) => (long ? P(more || short) : short);
    const opName = m => { const f = spec.CARD[m.op]; try { return f ? f(moveCard(m)).kind : m.op; } catch (er) { return m.op; } };
    function why(e, card, target, long) {
      const ref = refOf(target), ms = movesOf(e), want = ms[0], s = S(long);
      if (card.op === 'trap') return long ? card.why : 'That\'s a trap: it isn\'t true. Tap Why? to see why.';
      if (!card[tag]) return s('That card doesn\'t fit here.');
      const next = want ? ` Next: ${opName(want)}.` : '';
      const same = ms.filter(m => m.op === card.op);
      if (same.length && ref && same.some(m => m.refs && m.refs.some(r => okP(e, m, card, r))) && same.every(m => !m.refs || !m.refs.includes(ref) || !okP(e, m, card, ref)))
        return s('Right card, wrong place.', 'That card is right, but not there. Drop it on the part it changes.');
      return spec.why(e, card, ref, s, next, long) || s('That card doesn\'t fit here.', `That isn't the move here.${next}`);
    }
    const isCorrect = (cur, card, target) => correct(cur.state, card, target);
    const whyWrong = (cur, card, target) => why(cur.state, card, target, false);
    if (typeof registerWhy === 'function') registerWhy(({ state, card, ref }) => (state && state[sk] && card ? why(state, card, ref, true) : null));
    // ---------------------------------------------------------------- rendering
    function fit() {
      const el = $('equation'); if (!el.classList.contains('ex9')) return;
      el.style.removeProperty('--eqSize');
      const base = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--eqSize')) || 56;
      let size = Math.round(base * (el.querySelector('.col9') ? 0.72 : 0.86) * (spec.scale || 1));
      el.style.setProperty('--eqSize', size + 'px');
      const graph = $('arena').classList.contains('g4') && innerWidth > 640;
      const maxH = Math.max(90, ($('arena').clientHeight || 400) * (innerWidth <= 640 ? 0.46 : 0.58));
      for (let i = 0; i < 16; i++) {
        const availW = ($('arena').clientWidth || innerWidth) * (graph ? 0.56 : 0.92), needW = Math.max(el.scrollWidth, el.getBoundingClientRect().width);
        const needH = Math.max(0, ...[...el.children].map(k => k.offsetHeight || 0));
        const f = Math.min(availW && needW > availW ? availW / needW : 1, needH > maxH ? maxH / needH : 1);
        if (f >= 0.99) break;
        size = Math.max(11, Math.floor(size * Math.min(0.97, f)));
        el.style.setProperty('--eqSize', size + 'px');
        if (size <= 11) break;
      }
    }
    function render(e) {
      const el = $('equation'); if (typeof clearNotes === 'function') clearNotes();
      el.innerHTML = ''; el.classList.add('a4', 'ex9');
      if (spec.graph) spec.graph(e);
      spec.render(e, el, R);
      fit();
    }
    function clear() {
      const el = $('equation'); if (el && !(cur && cur[flag])) el.classList.remove('ex9');
      document.querySelectorAll('.fly9').forEach(n => n.remove());
    }
    const fontPx = () => parseFloat(getComputedStyle($('equation')).fontSize);
    function prefit(s, ns) {
      render(ns); const after = fontPx(); render(s); const before = fontPx();
      if (before > after + 0.5) { const el = $('equation'), c = parseFloat(el.style.getPropertyValue('--eqSize')) || 56; el.style.setProperty('--eqSize', Math.floor(c * after / before) + 'px'); }
    }
    addEventListener('resize', () => { if (!cur || !cur[flag] || (typeof animating !== 'undefined' && animating)) return; fit(); });
    // ---------------------------------------------------------------- prompts
    const lastPr = {};
    function prompt(s) {
      const key = spec.promptKey(s), all = spec.PR[key] || ['Solve.'];
      const fresh = all.filter(t => t !== lastPr[key]);
      return (lastPr[key] = pick(fresh.length ? fresh : all));
    }
    // ---------------------------------------------------------------- animations
    async function result(ns, refs, cap) { render(ns); refs.forEach(r => kickClass(tk(r), 'pop')); if (cap) caption(cap); await quick(300); await hold(); }
    const Hx = { ...H, result, render, moveAt: (s, c, ref) => legalMove(s, c, ref) || movesOf(s).find(m => m.op === c.op) };
    function animFor() {
      return async (c, s, ns, ref) => {
        const f = spec.anim[c.op];
        if (f) return f(c, s, ns, ref, Hx);
        caption(cardText(c)); await quick(200); await result(ns, [], '');
      };
    }
    // ---------------------------------------------------------------- fights
    function okPath(st, maxLen) {
      if (isSolved(st)) return false;
      const { path } = pathOf(st, st.skill);
      return path.length <= maxLen;
    }
    function buildFight(node, list) {
      const mine = list.filter(id => (SKILL[id].act || 1) === spec.act);
      if (!mine.length) mine.push(spec.skills[0].id);
      if (node.type === 'elite') {
        const two = mine.slice(-2);
        const phases = (two.length > 1 ? two : [two[0], two[0]]).map(id => () => spec.gens[id](pick(spec.hard[id] || SKILL[id].cases)));
        return { phases, handSize: difficulty.hand, enemy: spec.elite };
      }
      const phases = mine.map(id => () => spec.gens[id](pick(SKILL[id].cases)));
      phases.push(() => spec.bossLast(mine));
      return { phases, handSize: difficulty.hand, enemy: spec.boss };
    }
    const E = { apply: applyA, isSolved, makeEquation, refreshPath, render, prefit, clear, makeHand, isCorrect, whyWrong, animFor,
      applyDifficulty: g => g, label, text, kind, icon, slot: () => null, targetSel, onDrag, autoTarget, buildFight, prompt,
      gens: spec.gens, eqText: spec.textOf,
      _canon: canon, _correct: correct, _moves: movesOf, _legal: legalMove, _places: places, _hand: makeHand, _family: spec.family, _specials: spec.specials, _path: pathOf, _why: why };
    const R = { TOK, EQTOK, sym, rowEl, colEl, W9, tag };
    return { E, C, trap, moveCard, okPath, movesOf, legalMove, pathOf, render, isSolved };
  }
  const W9 = h => `<span class="w9">${h}</span>`;
  const sym = (html, cls = '') => { const d = document.createElement('div'); d.className = 'tok a4 s9 ' + cls; d.innerHTML = W9(html); return d; };
  const rowEl = els => { const r = document.createElement('span'); r.className = 'row4 row9'; els.filter(Boolean).forEach(x => r.appendChild(x)); return r; };
  const colEl = (rows, cls = '') => { const c = document.createElement('div'); c.className = 'col9 ' + cls; rows.filter(Boolean).forEach(r => c.appendChild(r)); return c; };

  // Installs an act: its skills, enemies, act entry, icons and CSS, and registers the engine.
  function install(spec, A) {
    SKILLS.push(...spec.skills);
    for (const s of SKILLS) SKILL[s.id] = s;
    progress = loadProgress();     // the save was first read before these skills existed
    Object.assign(ENEMIES, spec.enemies);
    ACTS[spec.act] = spec.actInfo;
    Object.assign(CARD_ICONS, spec.icons || {});
    if (spec.css) { const css = document.createElement('style'); css.textContent = spec.css; document.head.appendChild(css); }
    if (typeof ENGINES === 'object') ENGINES[spec.key] = { text: spec.textOf };
    window['ACT' + spec.act] = A.E;
    registerAct({ act: spec.act, key: spec.key, sk: spec.sk, flag: 'act' + spec.act, E: A.E });
  }
  // "Act 10, The Hall of Mirrors, is open." / "...opens when the last Act 9 stage reaches 80 mastery."
  function nextActText(act) {
    const n = SKILLS.find(k => k.act === act + 1);
    if (!n || !ACTS[act + 1]) return `Act ${act + 1} is still to be built, so run Act ${act} again to keep your skills sharp.`;
    return isUnlocked(n.id) ? `Act ${act + 1}, ${ACTS[act + 1].name}, is open.` : `Act ${act + 1}, ${ACTS[act + 1].name}, opens when the last Act ${act} stage reaches 80 mastery.`;
  }
  const svgI = body => `<svg viewBox="0 0 24 24" width="1em" height="1em" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round">${body}</svg>`;

  // Styles shared by every late act.
  const css = document.createElement('style');
  css.textContent = `
    #equation.ex9 { flex-wrap:nowrap; gap:0; max-width:100%; align-items:center; }
    .tok.a4.s9 { padding:4px 3px; min-width:0; color:var(--muted); border-color:transparent !important; background:none !important; }
    .tok.a4.t9 { padding:4px 6px; white-space:nowrap; min-height:0; }
    .w9 { display:inline-block; white-space:nowrap; }
    sup.e9 { font-size:.55em; vertical-align:.8em; line-height:0; margin-left:.04em; }
    .frac.f9 { font-size:.8em; }
    .frac.f9 > span { padding:0 .2em; white-space:nowrap; }
    .col9 { display:flex; flex-direction:column; align-items:center; gap:.18em; }
    .col9 .row4 { flex-wrap:nowrap; justify-content:center; align-items:center; }
    .tok.a4.s9.lab9 { font-size:.42em; color:var(--muted); white-space:nowrap; }
    .tok.a4.s9.fin9 { font-size:.6em; color:var(--good) !important; white-space:nowrap; }
    .tok.a4.s9.bad9 { font-size:.55em; color:var(--bad) !important; white-space:nowrap; }
    .tok.a4.s9.info9 { font-size:.45em; color:#ffc46b !important; white-space:nowrap; }
    .tok.a4.small9 { font-size:.62em; }
    .tok.a4.tiny9 { font-size:.48em; }
    .tok.a4.hot9 { background:#ffffff14; border-color:var(--accent); }
    .tok.a4.crack9 { animation: crack8 .6s ease-in forwards; color:var(--bad); }
    .tok.a4.keep9 { animation: pop .4s; color:var(--good); border-color:var(--good); }
    .tok.a4.fade9 { opacity:.25; transition: opacity .35s; }
    .tok.a4.slide9 { transform: translateY(-.3em) scale(.8); opacity:.2; transition: transform .35s, opacity .35s; }
    .tok.ok9, .tg9.ok9 { border-color: var(--good) !important; background:#06d6a022 !important; }
    .tg9.ok9 { fill:#06d6a033 !important; stroke: var(--good) !important; }
    .unote.n9 { font-size:max(.42em, 14px); }
    .card .clong.l9 { white-space:normal; display:block; line-height:1.1; }
    .card .clong.l9 sup { font-size:.75em; }
    .card .clong.l9 .frac { font-size:.72em; display:inline-flex; vertical-align:middle; }
    .card .clong.l9 svg.nl9 { width:100%; height:auto; max-height:2.6em; }
    .stamp9 { font-size:.42em; color:#ffc46b; border:2px solid #ffc46b88; border-radius:6px; padding:1px 6px; white-space:nowrap; }
    svg.nl9 { display:block; width:min(300px, 70vw); height:auto; overflow:visible; }
    .nlAx9 { stroke:var(--muted); stroke-width:2; }
    .nlTk9 { stroke:var(--muted); stroke-width:1.5; }
    .nlNum9, .nlPl9 { fill:var(--muted); font-size:11px; text-anchor:middle; font-family:inherit; }
    .nlPl9 { fill:#ffc46b; font-size:12px; }
    .nlSh9 { stroke:#06d6a0; stroke-width:6; stroke-linecap:round; opacity:.85; }
    .nlPt9 { stroke:#ffc46b; stroke-width:2.5; }
    .nlPt9.closed { fill:#ffc46b; } .nlPt9.open { fill:var(--panel, #1b1530); }
    .nlIv9 { fill:#ffffff08; stroke:#ffffff30; stroke-dasharray:3 3; }
    .nlIv9.hover { fill:#7bdff233; stroke:#7bdff2; }
    .nlIv9.done9 { fill:none; stroke:none; pointer-events:none; }
    .nlT9 circle { fill:#7bdff2; } .nlT9.ok circle { fill:#06d6a0; } .nlT9.no circle { fill:#ef476f; }
    .nlTl9 { font-size:10px; fill:#fff; text-anchor:middle; }
    #graph .gC9 { fill:none; stroke:#ffd166; stroke-width:2.5; stroke-dasharray:1; stroke-dashoffset:1; animation: para7 1s ease-out forwards; }
    #graph .gC9.ghost9 { stroke:#ffffff55; stroke-dasharray:4 4; animation:none; stroke-width:2; }
    #graph .gC9.alt9 { stroke:#7bdff2; }
    #graph .gC9.mir9 { stroke:#ffffff66; stroke-dasharray:3 4; animation:none; stroke-width:1.5; }
    @keyframes para7 { to { stroke-dashoffset:0; } }
    @media (max-width: 640px) { .tok.a4.t9 { padding:2px 3px; } }
  `;
  document.head.appendChild(css);

  window.KIT9 = { makeAct, install, nextActText, svgI, K, P, FN, chance, qid, isTutorial, lvl, supT, supH, XV, numH, parenF, decT, isDec, frH, sgnJoin,
    ptrim, pdeg, pco, padd, pscale, psub, pmul, peval, pEq, P1, fpow, ptext, pterms, numberLine, nlWindow, drawCurves, square, H,
    W9, sym, rowEl, colEl, TOK, EQTOK, refOf, kickClass, clone, fNeg, fSub, fDiv, fEq, fz, fv };
})();
