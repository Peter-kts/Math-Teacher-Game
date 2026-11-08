// =====================================================================
//  Act 4: The Map Room (expressions, functions and lines), and stage 9 (formulas, part of Act 2)
// =====================================================================
// Stage 9   Formulas                 solve d = rt for t, 2x + 3y = 12 for y        (Act 2)
// Stage 14  Order of operations      evaluate 3x² − 4 when x = 2
// Stage 15  Function notation        f(x) = 2x + 3: find f(4); solve f(x) = 11
// Stage 16  Slope                    the line through (1, 2) and (4, 8)
// Stage 17  Equations of lines       slope 3 through (2, 5); intercepts of 2x + 3y = 12
//
// Every state has a kind, `k4`:
//   eval     an expression tree to work out: { tree, val, vn, lhs, fn }   (stage 14, f(4) in stage 15, m = ... in 16)
//   formula  a literal equation solved for one letter: { L, R, v }        (stage 9, standard form, point-slope form)
//   fin      f(x) = 11 or f(x) > 7: { fn, rel, rhs, work }                 (stage 15)
//   slope    m = ?: { src, pts, m, work }                                   (stage 16)
//   line     y = mx + b to write: { q, m, b, pts, ref, work, done, then }  (stage 17)
//   icept    both intercepts of ax + by = c: { a, b, c, found, work }      (stage 17)
// A state can hold `work`: a smaller problem it is in the middle of. Work is an eval, a formula, or an
// equation or inequality in one letter, which Act 2's engine (=) or Act 3's (< ≤ > ≥) solves as usual;
// this file passes the cards through to them. The graph panel (#graph, drawGraph) is read-only: points
// and the given line are drop targets for the cards that use them.
//
// index.html picks this engine for generators that return { fn } (cur.act4); ENGINES.fn plugs it into
// the shared variety system.
'use strict';
(function () {
  const A2 = window.ACT2, A3 = window.ACT3;
  if (!A2 || !A3) return;
  const clone = o => JSON.parse(JSON.stringify(o));
  const toF = v => (typeof v === 'number' ? F(v) : v);
  const fNeg = a => F(-a.n, a.d);
  const fSub = (a, b) => fAdd(a, fNeg(b));
  const fDiv = (a, b) => F(a.n * b.d, a.d * b.n);
  const fEq = (a, b) => !!a && !!b && a.n === b.n && a.d === b.d;
  const fz = a => a.n === 0;
  const fv = a => a.n / a.d;
  const isTutorial = () => typeof fight !== 'undefined' && fight && fight.node && fight.node.type === 'tutorial';
  const lvl = tut => (tut || isTutorial() ? 0 : difficulty.level);
  const known = id => isUnlocked(id) && (progress.tutorialsDone.includes(id) || SKILL[id].stage <= 3 || (typeof fight !== 'undefined' && fight && fight.node && fight.node.skill === id));
  const P = t => `<p>${t}</p>`;
  const XI = v => `<i class="xv">${v}</i>`;
  const kickClass = (el, cls) => { if (!el) return; el.classList.remove(cls); void el.offsetWidth; el.classList.add(cls); };
  const pmText = (f, first) => (f.n < 0 ? (first ? MINUS : MINUS + ' ') : first ? '' : '+ ') + fracText(fAbs(f));
  const ptText = p => `(${fracText(p.x)}, ${fracText(p.y)})`;

  // ================================================================ expression trees (eval)
  const num = v => ({ t: 'num', v: toF(v) });
  const vr = (name = 'x') => ({ t: 'var', name });
  const add = (a, b) => ({ t: 'add', a, b }), sub = (a, b) => ({ t: 'sub', a, b });
  const mul = (a, b) => ({ t: 'mul', a, b }), dv = (a, b) => ({ t: 'div', a, b });
  const pw = (a, e = 2) => ({ t: 'pow', a, e }), par = a => ({ t: 'par', a }), ng = a => ({ t: 'neg', a });
  const call = (name, arg) => ({ t: 'call', name, arg: toF(arg) });
  // a ± n, written with the right sign (a + (−3) is written a − 3)
  const pm = (a, n) => { n = toF(n); return n.n < 0 ? sub(a, num(fNeg(n))) : add(a, num(n)); };
  const pmT = (a, t, neg) => (neg ? sub(a, t) : add(a, t));
  const OPS = ['add', 'sub', 'mul', 'div', 'pow'];
  const kids = n => (n.t === 'pow' || n.t === 'par' || n.t === 'neg' ? [['a', n.a]] : n.a && n.b ? [['a', n.a], ['b', n.b]] : []);
  function at(n, path) { for (const c of path) { if (!n) return null; n = n[c]; } return n || null; }
  function setAt(root, path, node) {
    if (!path) return node;
    const r = clone(root); let p = r;
    for (const c of path.slice(0, -1)) p = p[c];
    p[path.slice(-1)] = node;
    return r;
  }
  function walk(n, path, fn) { fn(n, path); for (const [k, c] of kids(n)) walk(c, path + k, fn); }
  const hasVar = n => { let f = false; walk(n, '', m => { if (m.t === 'var') f = true; }); return f; };
  const varPaths = n => { const out = []; walk(n, '', (m, p) => { if (m.t === 'var') out.push(p); }); return out; };
  const hasPowVar = n => { let f = false; walk(n, '', m => { if (m.t === 'pow' && m.a.t === 'var') f = true; }); return f; };
  // Brackets around a single number fade on their own, and a minus in front of a number joins it.
  function norm(n) {
    if (n.t === 'par' || n.t === 'neg' || n.t === 'pow') n = { ...n, a: norm(n.a) };
    else if (n.a && n.b) n = { ...n, a: norm(n.a), b: norm(n.b) };
    if (n.t === 'par' && n.a.t === 'num') return n.a;
    if (n.t === 'neg' && n.a.t === 'num') return num(fNeg(n.a.v));
    return n;
  }
  const isNum = n => n && n.t === 'num';
  const isRedex = n => !!n && OPS.includes(n.t) && kids(n).every(([, c]) => isNum(c));
  const FAMILY = { add: 'addsub', sub: 'addsub', mul: 'muldiv', div: 'muldiv', pow: 'pow' };
  function evalNode(n) {
    const a = n.a.v, b = n.b && n.b.v;
    switch (n.t) {
      case 'add': return fAdd(a, b);
      case 'sub': return fSub(a, b);
      case 'mul': return fMul(a, b);
      case 'div': return fDiv(a, b);
      default: { let r = F(1); for (let i = 0; i < n.e; i++) r = fMul(r, a); return r; }
    }
  }
  function subst(n, name, v) {
    if (n.t === 'var' && n.name === name) return num(v);
    const r = { ...n };
    for (const [k, c] of kids(n)) r[k] = subst(c, name, v);
    return r;
  }
  // Works a tree out completely (for generators). null if it divides by 0.
  function evaluate(n, name, v) {
    let t = norm(subst(n, name, v));
    for (let i = 0; i < 60 && !isNum(t); i++) {
      let p = null; walk(t, '', (m, q) => { if (p === null && isRedex(m)) p = q; });
      if (p === null) return null;
      const node = at(t, p); if (node.t === 'div' && fz(node.b.v)) return null;
      t = norm(setAt(t, p, num(evalNode(node))));
    }
    return isNum(t) ? t.v : null;
  }
  const redexes = tree => { const out = []; walk(tree, '', (m, p) => { if (isRedex(m)) out.push(p); }); return out; };
  // How many operations an evaluation takes (for checking sizes).
  const opCount = n => { let k = 0; walk(n, '', m => { if (OPS.includes(m.t)) k++; }); return k; };

  // Plain text of a tree, with the same rules as the on-screen layout.
  const leftLeaf = n => { while ((n.t === 'mul' || n.t === 'add' || n.t === 'sub' || n.t === 'pow') && n.a) n = n.a; return n; };
  const implicitMul = n => n.t === 'mul' && isNum(n.a) && n.a.v.n > 0 && (leftLeaf(n.b).t === 'var' || n.b.t === 'par' || (n.b.t === 'pow' && n.b.a.t === 'par'));
  function treeText(n, wrapNeg = false) {
    switch (n.t) {
      case 'num': return n.v.n < 0 && wrapNeg ? `(${fracText(n.v)})` : fracText(n.v);
      case 'var': return n.name;
      case 'call': return `${n.name}(${fracText(n.arg)})`;
      case 'add': return `${treeText(n.a)} + ${treeText(n.b, true)}`;
      case 'sub': return `${treeText(n.a)} ${MINUS} ${treeText(n.b, true)}`;
      case 'mul': return implicitMul(n) ? `${treeText(n.a)}${treeText(n.b, true)}` : `${treeText(n.a)} · ${treeText(n.b, true)}`;
      case 'div': return `(${treeText(n.a)})/(${treeText(n.b)})`.replace(/^\((\w+)\)\//, '$1/').replace(/\/\((\w+)\)$/, '/$1');
      case 'pow': return `${treeText(n.a, true)}${n.e === 3 ? '³' : '²'}`;
      case 'par': return `(${treeText(n.a)})`;
      case 'neg': return `${MINUS}${treeText(n.a, true)}`;
    }
    return '?';
  }

  // ---------------------------------------------------------------- eval states
  // val: the value to plug in (null when there's no letter); lhs: what's written in front ("m", "f(4)").
  const evalState = (tree, val, vn = 'x', extra = {}) => ({ k4: 'eval', tree, val: val === null ? null : toF(val), vn, lhs: null, orig: treeText(tree), ...extra });
  const evalSolved = e => !!e.undef || isNum(e.tree);
  function evalCanon(e) {
    if (evalSolved(e)) return null;
    if (e.tree.t === 'call') return { op: 'plugf', scope: 'part', v: e.tree.arg, fname: e.tree.name, ref: 'e' };
    if (hasVar(e.tree)) return { op: 'plug', scope: 'part', v: e.val, vn: e.vn, ref: 'e' + varPaths(e.tree)[0] };
    const rs = redexes(e.tree);
    for (const p of rs) { const n = at(e.tree, p); if (n.t === 'div' && fz(n.b.v)) return { op: 'undef', scope: 'part', ref: 'e' + p }; }
    const p = rs[0], n = at(e.tree, p), parent = p ? at(e.tree, p.slice(0, -1)) : null;
    if (parent && parent.t === 'par') return { op: 'paren', scope: 'part', ref: 'e' + p.slice(0, -1) };
    return { op: FAMILY[n.t], scope: 'part', ref: 'e' + p };
  }
  const pathOfRef = ref => (typeof ref === 'string' && ref[0] === 'e' ? ref.slice(1) : null);
  function evalApply(e, c, ref) {
    const r = clone(e), p = pathOfRef(ref) || '';
    if (c.op === 'plugf') { r.tree = norm(subst(e.fn.rule, e.fn.vn, e.tree.arg)); return r; }
    if (c.op === 'plug') { r.tree = norm(subst(e.tree, e.vn, e.val)); return r; }
    if (c.op === 'undef') { r.undef = true; return r; }
    let node = at(e.tree, p);
    if (c.op === 'paren') node = node.a;
    if (!isRedex(node)) return r;
    const target = c.op === 'paren' ? p : p;
    r.tree = norm(c.op === 'paren' ? setAt(e.tree, target, num(evalNode(node))) : setAt(e.tree, p, num(evalNode(node))));
    return r;
  }
  function evalCorrect(e, c, ref) {
    if (c.op === 'trap' || evalSolved(e)) return false;
    const p = pathOfRef(ref);
    if (e.tree.t === 'call') return c.op === 'plugf' && fEq(c.v, e.tree.arg) && p !== null;
    if (hasVar(e.tree)) { const n = p !== null ? at(e.tree, p) : null; return c.op === 'plug' && !c.nobr && fEq(c.v, e.val) && !!n && n.t === 'var'; }
    if (p === null) return false;
    const node = at(e.tree, p); if (!node) return false;
    if (c.op === 'undef') return node.t === 'div' && isRedex(node) && fz(node.b.v);
    if (c.op === 'paren') return node.t === 'par' && isRedex(node.a) && !(node.a.t === 'div' && fz(node.a.b.v));
    if (!isRedex(node) || (node.t === 'div' && fz(node.b.v))) return false;
    return FAMILY[node.t] === c.op;
  }
  const evalAnswer = e => (e.undef ? 'undefined' : fracText(e.tree.v));

  // ================================================================ formulas (literal equations)
  // A term is k · (letters) / (letters): { k: F, lit: 'rt', den: '' }. Letters are kept sorted.
  // A group is m(items): { g: true, m: term, items: [term] }.
  const sortL = s => [...(s || '')].sort().join('');
  const T = (k, lit = '', den = '') => ({ k: toF(k), lit: sortL(lit), den: sortL(den) });
  const GR = (m, items) => ({ g: true, m, items });
  const keyT = t => t.lit + '/' + t.den;
  function cancelL(lit, den) {
    const a = [...lit], b = [...den];
    for (let i = a.length - 1; i >= 0; i--) { const j = b.indexOf(a[i]); if (j >= 0) { a.splice(i, 1); b.splice(j, 1); } }
    return [a.join(''), b.join('')];
  }
  function tMul(t, f) { const [lit, den] = cancelL(sortL(t.lit + f.lit), sortL(t.den + f.den)); return { k: fMul(t.k, f.k), lit, den }; }
  const tInv = f => ({ k: F(f.k.d, f.k.n), lit: f.den, den: f.lit });
  const hasV = (t, v) => (t.g ? t.items.some(i => hasV(i, v)) || t.m.lit.includes(v) : t.lit.includes(v));
  const isOne = t => !t.g && fIs(t.k, 1) && !t.lit && !t.den;
  function fAddTerm(side, t) {
    const i = side.findIndex(o => !o.g && keyT(o) === keyT(t));
    if (i >= 0) { const k = fAdd(side[i].k, t.k); if (fz(k)) side.splice(i, 1); else side[i] = { ...side[i], k }; return; }
    if (t.lit || t.den) { const j = side.findIndex(o => !o.g && !o.lit && !o.den); if (j >= 0) { side.splice(j, 0, { ...t }); return; } }
    side.push({ ...t });
  }
  function fScaleSide(side, f) {
    const out = [];
    for (const o of side) {
      if (!o.g) { out.push(tMul(o, f)); continue; }
      const m = tMul(o.m, f);
      if (isOne(m)) out.push(...o.items); else out.push({ ...o, m });
    }
    return out;
  }
  function fApply(e, c, ref) {
    const r = clone(e);
    if (c.op === '+' || c.op === '-') { const t = { ...c.t, k: c.op === '+' ? c.t.k : fNeg(c.t.k) }; fAddTerm(r.L, t); fAddTerm(r.R, t); }
    else if (c.op === '*' || c.op === '/') { const f = c.op === '*' ? c.t : tInv(c.t); r.L = fScaleSide(r.L, f); r.R = fScaleSide(r.R, f); }
    else if (c.op === 'dist') { const s = ref[0], i = +ref.slice(1), g = r[s][i]; r[s].splice(i, 1, ...g.items.map(o => tMul(o, g.m))); }
    else if (c.op === 'comb') {
      const s = ref[0], i = +ref.slice(1), key = keyT(r[s][i]); let k = F(0); const out = []; let at_ = -1;
      r[s].forEach(o => { if (!o.g && keyT(o) === key) { k = fAdd(k, o.k); if (at_ < 0) { at_ = out.length; out.push(null); } } else out.push(o); });
      if (fz(k)) out.splice(at_, 1); else out[at_] = { ...r[s][i], k };
      r[s] = out;
    }
    return r;
  }
  function fLegalPart(e, c, ref) {
    if (typeof ref !== 'string' || !/^[LR]\d+$/.test(ref)) return false;
    const side = e[ref[0]], it = side[+ref.slice(1)];
    if (!it) return false;
    if (c.op === 'dist') return !!it.g;
    if (c.op === 'comb') return !it.g && side.filter(o => !o.g && keyT(o) === keyT(it)).length >= 2;
    return false;
  }
  const isV = (t, v) => !t.g && fIs(t.k, 1) && t.lit === v && !t.den;
  function fSolved(e) {
    for (const [a, b] of [[e.L, e.R], [e.R, e.L]]) if (a.length === 1 && isV(a[0], e.v) && !b.some(o => o.g || hasV(o, e.v))) return true;
    return false;
  }
  const fT = (op, t) => ({ op, f4: true, t });
  function numMove(k) {      // Act 1's rule for the number in front of the letter
    if (k.d === 1) return k.n === -1 ? fT('*', T(-1)) : fT('/', T(k.n));
    if (Math.abs(k.n) === 1) return fT('*', T(k.n * k.d));
    return fT('*', T(F(Math.sign(k.n) * k.d, Math.abs(k.n))));
  }
  // The expected move: clear parentheses, combine, move the other terms off the letter's side (+ and −
  // first), then undo what multiplies the letter (a fraction first, then the rest in one card).
  function fCanon(e) {
    if (fSolved(e)) return null;
    const v = e.v;
    for (const s of ['L', 'R']) { const i = e[s].findIndex(o => o.g); if (i >= 0) return { op: 'dist', f4: true, scope: 'part', ref: s + i }; }
    for (const s of ['L', 'R']) {
      const side = e[s];
      for (let i = 0; i < side.length; i++) for (let j = i + 1; j < side.length; j++) if (keyT(side[i]) === keyT(side[j])) return { op: 'comb', f4: true, scope: 'part', ref: s + i };
    }
    // Playtest fix: a move that cancels the letter everywhere (2l − 2l, or ÷ w) left no side holding it,
    // and side[0] was undefined. Such a state can't be solved for the letter, so it is a dead end.
    if (![...e.L, ...e.R].some(o => hasV(o, v))) return DEAD;
    const ts = e.L.some(o => hasV(o, v)) ? 'L' : 'R', side = e[ts];
    const extra = side.find(o => !hasV(o, v));
    if (extra) return fT(extra.k.n > 0 ? '-' : '+', { ...extra, k: fAbs(extra.k) });
    const tt = side[0], rest = tt.lit.replace(v, '');
    if (tt.den) return fT('*', T(1, tt.den));
    if (!rest) return numMove(tt.k);
    if (tt.k.d > 1) return fT('*', T(tt.k.d));
    return fT('/', T(tt.k, rest));
  }
  const DEAD = { dead: true };
  function fPath(e) { const out = []; let s = e; while (out.length < 20) { const m = fCanon(s); if (!m) break; if (m.dead) { while (out.length < 99) out.push({ state: s, move: null }); break; } out.push({ state: s, move: m }); s = fApply(s, m, m.ref); } return { path: out, end: s }; }
  const fSteps = e => fPath(e).path.length;
  // Shrinking what multiplies the letter (÷2 on 2rt = d) is real progress too, so it is never dealt as a wrong card.
  function fShrinks(e, c) {
    if (c.op !== '*' && c.op !== '/') return false;
    const size = st => { const ts = st.L.some(o => hasV(o, st.v)) ? st.L : st.R; if (ts.length !== 1 || ts[0].g) return Infinity; const t = ts[0]; return Math.abs(t.k.n) * t.k.d + t.lit.length + t.den.length; };
    return size(fApply(e, c)) < size(e);
  }
  function fCorrect(e, c, ref) {
    if (!c.f4) return false;
    if ((c.op === 'comb' || c.op === 'dist') && !fLegalPart(e, c, ref)) return false;
    const a = fApply(e, c, ref);
    return fSteps(a) < fSteps(e) || fShrinks(e, c);
  }
  // ---------------------------------------------------------------- formula text
  // Playtest fix: repeated letters (×5hw on 5hlw) showed as "hh"; they now show as powers, h².
  const SUP = ['', '', '²', '³', '⁴', '⁵', '⁶'];
  const litRuns = lit => { const out = []; for (const ch of lit) { const r = out[out.length - 1]; if (r && r.ch === ch) r.n++; else out.push({ ch, n: 1 }); } return out; };
  const litText = lit => litRuns(lit).map(r => r.ch + (r.n === 1 ? '' : SUP[r.n] || '^' + r.n)).join('');
  const litHtml = (lit, v) => litRuns(lit).map(r => (r.ch === v ? XI(r.ch) : `<i class="lv">${r.ch}</i>`) + (SUP[r.n] || '')).join('');
  function tBody(t, v, html) {
    const k = fAbs(t.k), topNum = k.n === 1 && t.lit ? '' : String(k.n);
    const top = topNum + (html ? litHtml(t.lit, v) : litText(t.lit)), bot = (k.d === 1 ? '' : String(k.d)) + (html ? litHtml(t.den, v) : litText(t.den));
    if (!bot) return top;
    // playtest fix: plain text V/5hw read as (V/5)·h·w; a denominator of more than one factor gets brackets
    return html ? `<span class="frac"><span>${top}</span><span>${bot}</span></span>` : `${top}/${/^\d+$|^[A-Za-z]$/.test(bot) ? bot : '(' + bot + ')'}`;
  }
  function fTermStr(o, first, html, v) {
    const neg = (o.g ? o.m.k : o.k).n < 0, sign = neg ? (first ? MINUS : MINUS + ' ') : first ? '' : '+ ';
    if (!o.g) return sign + tBody(o, v, html);
    const m = { ...o.m, k: fAbs(o.m.k) }, mm = isOne(m) ? '' : tBody(m, v, html);
    return `${sign}${mm}(${o.items.map((t, j) => fTermStr(t, j === 0, html, v)).join(' ')})`;
  }
  const fSide = (side, html, v) => (side.length ? side.map((o, i) => fTermStr(o, i === 0, html, v)).join(' ') : '0');
  const fText = e => `${fSide(e.L, false, e.v)} = ${fSide(e.R, false, e.v)}`;
  const fHtml = e => `<span class="whyEq"><span>${fSide(e.L, true, e.v)}</span><span>=</span><span>${fSide(e.R, true, e.v)}</span></span>`;
  const signedT = t => fTermStr(t, true, false, '');
  function fCardLabel(c) {
    if (c.op === 'comb') return '<span class="clong">Combine</span>';
    if (c.op === 'dist') return '<span class="clong">Distribute</span>';
    const b = tBody({ ...c.t, k: fAbs(c.t.k) }, '', false), neg = c.t.k.n < 0;
    if (c.op === '+' || c.op === '-') return (c.op === '+' ? '+' : MINUS) + b;
    return (c.op === '/' ? DIV : TIMES) + (neg ? `(${MINUS}${b})` : b);
  }
  function fCardText(c) {
    if (c.op === 'comb') return 'Combine like terms';
    if (c.op === 'dist') return 'Multiply into the parentheses';
    const b = signedT(c.t);
    return { '+': `Add ${b} to both sides`, '-': `Subtract ${b} from both sides`, '*': `Multiply both sides by ${b}`, '/': `Divide both sides by ${b}` }[c.op];
  }
  // The term of a solved y = ... formula that holds x (for Read the slope), as its ref.
  function xTermRef(e) {
    const s = e.L.length === 1 && isV(e.L[0], e.v) ? 'R' : 'L';
    const i = e[s].findIndex(o => !o.g && o.lit === 'x' && !o.den);
    return i >= 0 ? s + i : null;
  }
  function slopeOfFormula(e) {   // y = mx + b: { m, b }
    const s = e.L.length === 1 && isV(e.L[0], e.v) ? e.R : e.L;
    const xt = s.find(o => o.lit === 'x' && !o.den), c = s.find(o => !o.lit && !o.den);
    return { m: xt ? xt.k : F(0), b: c ? c.k : F(0) };
  }

  // ================================================================ work (the smaller problem a state is in the middle of)
  // a2: an equation in one letter (Act 2's model, with e.v the letter); a3: an inequality in one letter.
  const wKind = w => (w.k4 ? w.k4 : w.rel && w.rel !== '=' ? 'a3' : 'a2');
  const a3Move = w => { const p = A3.makeEquation(w).path; return p.length ? p[0].move : null; };
  function wCanon(w) {
    switch (wKind(w)) {
      case 'eval': return evalCanon(w);
      case 'formula': return fCanon(w);
      case 'a3': return a3Move(w);
      default: return A2.canon(w);
    }
  }
  function wApply(w, c, ref) {
    switch (wKind(w)) {
      case 'eval': return evalApply(w, c, ref);
      case 'formula': return fApply(w, c, ref);
      case 'a3': return A3.apply(w, c, ref);
      default: return A2.apply(w, c, ref);
    }
  }
  function wSolved(w) {
    switch (wKind(w)) {
      case 'eval': return evalSolved(w);
      case 'formula': return fSolved(w);
      case 'a3': return A3.isSolved(w);
      default: return A2.isSolved(w);
    }
  }
  function wCorrect(w, c, target) {
    const ref = refOf(target);
    switch (wKind(w)) {
      case 'eval': return evalCorrect(w, c, ref);
      case 'formula': return fCorrect(w, c, ref);
      case 'a3': return A3.isCorrect({ state: w }, c, target);
      default: return A2.isCorrect({ state: w }, c, target);
    }
  }
  // The value an equation in one letter ends on (x = 4, or 3 = b).
  function a2Value(w) {
    let s = w; for (let i = 0; i < 20 && !A2.isSolved(s); i++) { const m = A2.canon(s); if (!m) break; s = A2.apply(s, m, m.ref); }
    const other = s.L.length === 1 && s.L[0].t === 'x' ? s.R : s.L, c = other.find(it => it.t === 'n');
    return c ? c.k : F(0);
  }
  const refOf = t => (t && t.dataset ? t.dataset.ref : t) || null;
  const roleOfT = t => (t && t.dataset ? t.dataset.role : null);
  // Act 2 items from a linear rule tree: 2x + 3, 3(x − 2), 9 − 2x, x/4 + 1.
  function toItems(n, sign = 1) {
    const s = F(sign);
    switch (n.t) {
      case 'num': return [{ t: 'n', k: fMul(n.v, s) }];
      case 'var': return [{ t: 'x', k: s }];
      case 'add': return [...toItems(n.a, sign), ...toItems(n.b, sign)];
      case 'sub': return [...toItems(n.a, sign), ...toItems(n.b, -sign)];
      case 'neg': return toItems(n.a, -sign);
      case 'par': return toItems(n.a, sign);
      case 'mul':
        if (isNum(n.a) && n.b.t === 'var') return [{ t: 'x', k: fMul(n.a.v, s) }];
        if (isNum(n.a) && n.b.t === 'par') return [{ t: 'g', m: fMul(n.a.v, s), items: toItems(n.b.a, 1) }];
        break;
      case 'div':
        if (n.a.t === 'var' && isNum(n.b)) return [{ t: 'x', k: fMul(F(1, n.b.v.n), s) }];
        break;
    }
    throw new Error('rule is not linear');
  }

  // ================================================================ the state kinds
  const lineTextOf = (m, b) => {
    const mt = fz(m) ? '' : fIs(m, 1) ? 'x' : fIs(m, -1) ? MINUS + 'x' : fracText(m) + 'x';
    if (!mt) return fracText(b);
    return fz(b) ? mt : `${mt} ${b.n < 0 ? MINUS : '+'} ${fracText(fAbs(b))}`;
  };
  // A line as an eval rule: m·x + b
  function lineRule(m, b, vn = 'x') {
    let t = fIs(m, 1) ? vr(vn) : fIs(m, -1) ? ng(vr(vn)) : mul(num(m), vr(vn));
    if (m.d > 1) t = mul(num(m), vr(vn));
    return fz(b) ? t : pm(t, b);
  }
  // m = (y2 − y1)/(x2 − x1), from point i to point j
  function riseRun(a, b) { return dv(sub(num(b.y), num(a.y)), sub(num(b.x), num(a.x))); }
  const slopeEval = (a, b) => ({ ...evalState(riseRun(a, b), null, 'x'), lhs: 'm', from: a, to: b });
  const twoPtSlope = (a, b) => (fEq(a.x, b.x) ? null : fDiv(fSub(b.y, a.y), fSub(b.x, a.x)));

  function canon4(e) {
    switch (e.k4) {
      case 'eval': return evalCanon(e);
      case 'formula': return fCanon(e);
      case 'fin': return e.work ? (wSolved(e.work) ? null : wCanon(e.work)) : { op: 'writeout', scope: 'part', fname: e.fn.name, ref: 'F' };
      case 'slope': {
        if (e.m !== null) return null;
        if (e.src === 'slopeint' || e.src === 'standard') return fSolved(e.work) ? { op: 'read', scope: 'part', ref: xTermRef(e.work) } : fCanon(e.work);
        return e.work ? evalCanon(e.work) : { op: 'rise', scope: 'part', ref: 'P0' };
      }
      case 'line': {
        if (e.done) return null;
        if (e.work) return wCanon(e.work);
        if (e.m === null) return e.q === 'parallel' ? { op: 'same', scope: 'part', ref: 'Q' } : e.q === 'perp' ? { op: 'perp', scope: 'part', ref: 'Q', v: fDiv(F(-1), e.ref.m) } : { op: 'rise', scope: 'part', ref: 'P0' };
        if (e.b === null) return { op: e.q === 'ptslope' ? 'ptslope' : 'plugpt', scope: 'part', ref: 'P0' };
        return { op: 'write', scope: 'part', ref: 'T' };
      }
      case 'icept': {
        if (e.work) return wCanon(e.work);
        if (e.found.y === null) return { op: 'setx' };
        if (e.found.x === null) return { op: 'sety' };
        return null;
      }
    }
    return null;
  }
  const isSolved4 = e => canon4(e) === null;

  function apply4(e, c, ref) {
    let r = clone(e);
    switch (e.k4) {
      case 'eval': return evalApply(e, c, ref);
      case 'formula': return fApply(e, c, ref);
      case 'fin':
        if (c.op === 'writeout' && !e.work) {
          const items = toItems(e.fn.rule), rhs = [{ t: 'n', k: e.rhs }];
          r.work = e.rel === '=' ? { L: items, R: rhs, result: null, v: e.fn.vn } : { L: items, R: rhs, result: null, rel: e.rel, v: e.fn.vn, skill: 'funcs' };
        } else if (e.work) r.work = wApply(e.work, c, ref);
        break;
      case 'slope':
        if (c.op === 'read') r.m = slopeOfFormula(e.work).m;
        else if (e.src === 'slopeint' || e.src === 'standard') r.work = fApply(e.work, c, ref);
        else if (c.op === 'rise' && !e.work) {
          const i = ref === 'P1' ? 1 : 0, a = e.pts[i], b = e.pts[1 - i];
          r.work = slopeEval(a, b); r.graph.marks = [{ t: 'tri', a, b }];
        } else if (e.work) {
          r.work = evalApply(e.work, c, ref);
          if (evalSolved(r.work)) r.m = r.work.undef ? 'undef' : r.work.tree.v;
        }
        break;
      case 'line':
        if (e.work) {
          r.work = wApply(e.work, c, ref);
          if (wSolved(r.work)) {
            const w = r.work, k = wKind(w);
            if (k === 'eval') { r.m = w.tree.v; r.work = null; r.graph.marks = []; }
            else if (k === 'formula') { const s = slopeOfFormula(w); r.m = s.m; r.b = s.b; r.done = true; r.work = null; r.graph.lines.push({ m: r.m, b: r.b, res: true }); }
            else { r.b = a2Value(w); r.work = null; }
          }
        } else if (c.op === 'rise') {
          const i = ref === 'P1' ? 1 : 0, a = e.pts[i], b = e.pts[1 - i];
          r.work = slopeEval(a, b); r.graph.marks = [{ t: 'tri', a, b }];
        } else if (c.op === 'same') r.m = e.ref.m;
        else if (c.op === 'perp') r.m = c.v || fDiv(F(-1), e.ref.m);   // the slope the player picked
        else if (c.op === 'plugpt') {
          const p = e.pts[ref === 'P1' ? 1 : 0], mx = fMul(e.m, p.x);
          r.work = { L: [{ t: 'n', k: p.y }], R: fz(mx) ? [{ t: 'x', k: F(1) }] : [{ t: 'n', k: mx }, { t: 'x', k: F(1) }], result: null, v: 'b' };
          if (A2.isSolved(r.work)) { r.b = a2Value(r.work); r.work = null; }
        } else if (c.op === 'ptslope') {
          const p = e.pts[ref === 'P1' ? 1 : 0];
          const L = [T(1, 'y')]; if (!fz(p.y)) L.push(T(fNeg(p.y)));
          const R = fz(p.x) ? [T(e.m, 'x')] : [GR(T(e.m), [T(1, 'x'), T(fNeg(p.x))])];
          r.work = { k4: 'formula', L, R, v: 'y' };
          if (fIs(e.m, 1) && !fz(p.x)) r.work.R = [T(1, 'x'), T(fNeg(p.x))];
          if (fSolved(r.work)) { const s = slopeOfFormula(r.work); r.b = s.b; r.done = true; r.work = null; r.graph.lines.push({ m: r.m, b: r.b, res: true }); }
        } else if (c.op === 'write') { r.done = true; r.graph.lines.push({ m: e.m, b: e.b, res: true }); }
        if (r.done && r.then) return thenState(r);
        break;
      case 'icept':
        if (e.work) {
          r.work = wApply(e.work, c, ref);
          if (A2.isSolved(r.work)) { r.found[r.which] = a2Value(r.work); r.work = null; r.graph.marks.push(r.which === 'y' ? { t: 'ic', x: F(0), y: r.found.y } : { t: 'ic', x: r.found.x, y: F(0) }); }
        } else if (c.op === 'setx' || c.op === 'sety') {
          r.which = c.op === 'setx' ? 'y' : 'x';
          const k = c.op === 'setx' ? e.b : e.a;
          r.work = { L: [{ t: 'x', k }], R: [{ t: 'n', k: e.c }], result: null, v: r.which };
          if (A2.isSolved(r.work)) { r.found[r.which] = a2Value(r.work); r.work = null; r.graph.marks.push(r.which === 'y' ? { t: 'ic', x: F(0), y: r.found.y } : { t: 'ic', x: r.found.x, y: F(0) }); }
        }
        if (r.found.x !== null && r.found.y !== null && !r.graph.lines.some(l => l.res)) r.graph.lines.push({ m: fDiv(fNeg(e.a), e.b), b: fDiv(e.c, e.b), res: true });
        break;
    }
    return r;
  }
  // Elite and boss questions go on once the line is written: f(3) = ?, or where does it reach y = 15?
  function thenState(r) {
    const fn = { name: 'f', vn: 'x', rule: lineRule(r.m, r.b) };
    const keep = { graph: r.graph, skill: r.skill, lineDone: { m: r.m, b: r.b } };
    if (r.then.q === 'out') return { ...evalState(call('f', r.then.input), null, 'x', { fn, lhs: `f(${fracText(r.then.input)})`, ...keep }) };
    return { k4: 'fin', fn, rel: '=', rhs: r.then.y, work: null, ...keep, ask: 'reach' };
  }

  // Does this card, dropped on that target, make progress? Act 4's own cards are checked here; the rest
  // go to the work's engine.
  const OWN = ['plug', 'paren', 'pow', 'muldiv', 'addsub', 'plugf', 'writeout', 'rise', 'read', 'undef', 'plugpt', 'ptslope', 'same', 'perp', 'write', 'setx', 'sety'];
  const pointRef = ref => ref === 'P0' || ref === 'P1';
  function correct4(e, c, target) {
    const ref = refOf(target);
    if (c.op === 'trap') return false;
    switch (e.k4) {
      case 'eval': return evalCorrect(e, c, ref);
      case 'formula': return fCorrect(e, c, ref);
      case 'fin':
        if (!e.work) return c.op === 'writeout' && ref === 'F';
        return !wSolved(e.work) && wCorrect(e.work, c, target);
      case 'slope':
        if (e.m !== null) return false;
        if (e.src === 'slopeint' || e.src === 'standard') {
          if (fSolved(e.work)) return c.op === 'read' && ref === xTermRef(e.work);
          return fCorrect(e.work, c, ref);
        }
        if (!e.work) return c.op === 'rise' && pointRef(ref);
        return evalCorrect(e.work, c, ref);
      case 'line':
        if (e.done) return false;
        if (e.work) return wCorrect(e.work, c, target);
        if (e.m === null) {
          if (e.q === 'twopts') return c.op === 'rise' && pointRef(ref);
          if (e.q === 'parallel') return c.op === 'same' && (ref === 'Q' || ref === 'G0');
          if (e.q === 'perp') return c.op === 'perp' && !!c.v && fEq(c.v, fDiv(F(-1), e.ref.m)) && (ref === 'Q' || ref === 'G0');
          return false;
        }
        if (e.b === null) return (c.op === 'plugpt' || c.op === 'ptslope') && pointRef(ref) && !!e.pts[ref === 'P1' ? 1 : 0];
        return c.op === 'write' && ref === 'T';
      case 'icept':
        if (e.work) return wCorrect(e.work, c, target);
        return (c.op === 'setx' && e.found.y === null) || (c.op === 'sety' && e.found.x === null);
    }
    return false;
  }
  // The state whose cards are being played right now (for hands, rendering and animations).
  function active(e) {
    if (e.k4 === 'eval' || e.k4 === 'formula') return e;
    if (e.k4 === 'slope') return e.work && !(e.m !== null && e.work.k4 === 'eval') ? e.work : e;
    return e.work || e;
  }

  // ================================================================ path, skills, answers
  // Each move practises a skill: the stage it belongs to when that stage is unlocked, otherwise the
  // fight's own. Plain + − × ÷ moves inside an equation in one letter count for the fight's stage.
  const HOME = { plug: 'evalx', paren: 'evalx', pow: 'evalx', muldiv: 'evalx', addsub: 'evalx', plugf: 'funcs', writeout: 'funcs',
    rise: 'slope', read: 'slope', undef: 'slope', plugpt: 'lines', ptslope: 'lines', same: 'lines', perp: 'lines', write: 'lines', setx: 'lines', sety: 'lines' };
  function skillFor(m, main) {
    let home = HOME[m.op];
    if (!home && m.f4) home = m.op === 'dist' ? 'distribute' : m.op === 'comb' ? 'liketerms' : 'formulas';
    if (!home) home = m.op === 'dist' ? 'distribute' : m.op === 'comb' ? 'liketerms' : m.x ? 'xboth' : m.lcd ? 'clearfrac' : m.op === 'flip' ? 'ineq' : (m.op === 'none' || m.op === 'all') ? 'special' : main;
    return home === main || isUnlocked(home) ? home : main;
  }
  function pathOf4(e, main) {
    const path = []; let s = e;
    for (let i = 0; i < 60; i++) { const m = canon4(s); if (!m) break; path.push({ state: s, move: m, skill: skillFor(m, main) }); s = apply4(s, m, m.ref); }
    return { path, end: s };
  }
  function answerOf(e) {
    switch (e.k4) {
      case 'eval': return e.lhs ? `${e.lhs} = ${evalAnswer(e)}` : `${e.orig} = ${evalAnswer(e)} when ${e.vn} = ${fracText(e.val)}`;
      case 'formula': return fText(e);
      case 'fin': {
        if (!e.work) return '';
        if (wKind(e.work) === 'a3') { const s = A3.solution(e.work); return s ? `${e.fn.vn} ${s.rel} ${fracText(s.v)}` : ''; }
        return `${e.fn.vn} = ${fracText(a2Value(e.work))}`;
      }
      case 'slope': return e.m === 'undef' ? 'The slope is undefined (a vertical line)' : `m = ${fracText(e.m)}`;
      case 'line': return `y = ${lineTextOf(e.m, e.b)}`;
      case 'icept': return `x-intercept (${fracText(e.found.x)}, 0), y-intercept (0, ${fracText(e.found.y)})`;
    }
    return '';
  }
  function makeEquation4(state, enemy) {
    const main = state.skill || 'evalx', { path, end } = pathOf4(state, main);
    return { start: state, end, path, main, skills: [...new Set(path.map(p => p.skill))], enemy, act2: true, act4: true, answer: F(0), answerText: answerOf(end) };
  }
  function refreshPath(cur) {
    const fresh = pathOf4(cur.state, cur.main).path;
    cur.path = cur.path.slice(0, cur.step).concat(fresh);
  }

  // ================================================================ cards
  const OWN_CARD = {
    paren:    { label: '( )', text: 'Do the parentheses', kind: 'Parentheses' },
    pow:      { label: 'x²', text: 'Work out the power (square or cube)', kind: 'Power' },
    muldiv:   { label: `${TIMES} ${DIV}`, text: 'Multiply or divide', kind: 'Multiply/divide' },
    addsub:   { label: `+ ${MINUS}`, text: 'Add or subtract', kind: 'Add/subtract' },
    writeout: { label: 'Write out', text: 'Write out the rule', kind: 'Write out' },
    rise:     { label: 'Rise / run', text: 'Slope = rise over run, from a point', kind: 'Rise over run' },
    read:     { label: 'Read m', text: 'Read the slope: the number in front of x', kind: 'Read the slope' },
    undef:    { label: 'Undefined', text: 'Declare: slope undefined (the run is 0)', kind: 'Declare undefined' },
    plugpt:   { label: 'Plug point', text: 'Plug the point into y = mx + b', kind: 'Plug the point' },
    ptslope:  { label: 'Point-slope', text: `Point-slope: y ${MINUS} y₁ = m(x ${MINUS} x₁)`, kind: 'Point-slope form' },
    same:     { label: 'Same m', text: 'Parallel: same slope', kind: 'Same slope' },
    perp:     { label: `${MINUS}1/m`, text: 'Perpendicular: negative reciprocal slope', kind: 'Pick the slope' },
    write:    { label: 'Write y =', text: 'Write the line y = mx + b', kind: 'Write the line' },
    setx:     { label: 'x = 0', text: 'Set x = 0 (finds the y-intercept)', kind: 'Set x = 0' },
    sety:     { label: 'y = 0', text: 'Set y = 0 (finds the x-intercept)', kind: 'Set y = 0' },
  };
  function label(c) {
    if (c.f4) return fCardLabel(c);
    if (c.op === 'trap' && c.a4) return `<span class="clong">${c.label}</span>`;
    if (c.op === 'plug') return `<span class="clong">${c.vn || 'x'} = ${fracText(c.v)}</span>`;
    if (c.op === 'plugf') return `<span class="clong">${c.fname}(${fracText(c.v)})</span>`;
    if (c.op === 'perp' && c.v) return `<span class="clong">m = ${fracText(c.v)}</span>`;
    if (OWN_CARD[c.op]) return `<span class="clong">${OWN_CARD[c.op].label}</span>`;
    return null;
  }
  function text(c) {
    if (c.f4) return fCardText(c);
    if (c.op === 'trap' && c.a4) return c.text;
    if (c.op === 'plug') return `Plug in ${c.vn || 'x'} = ${fracText(c.v)}`;
    if (c.op === 'plugf') return `Plug ${fracText(c.v)} into ${c.fname}`;
    if (c.op === 'perp' && c.v) return `The new line's slope is ${fracText(c.v)}`;
    if (OWN_CARD[c.op]) return OWN_CARD[c.op].text;
    return null;
  }
  function kind(c) {
    if (c.f4) return { '+': 'Add (formula)', '-': 'Subtract (formula)', '*': 'Multiply (formula)', '/': 'Divide (formula)', comb: 'Combine', dist: 'Distribute' }[c.op];
    if (c.op === 'trap' && c.a4) return 'Trap: ' + c.trap;
    if (c.op === 'plug') return 'Plug in';
    if (c.op === 'plugf') return 'Plug into f';
    if (OWN_CARD[c.op]) return OWN_CARD[c.op].kind;
    return null;
  }
  const ICON_OF = { plug: 'plug', plugf: 'machine', writeout: 'unroll', paren: 'paren', pow: 'pow', muldiv: 'mul', addsub: 'add', rise: 'rise', read: 'read', undef: 'none',
    plugpt: 'plugpt', ptslope: 'ptslope', same: 'same', perp: 'perp', write: 'write', setx: 'zero', sety: 'zero' };
  function icon(c) {
    if (c.f4) return { '+': 'add', '-': 'sub', '*': 'mul', '/': 'div', comb: 'comb', dist: 'dist' }[c.op] || (c.t && c.t.k.d > 1 ? 'recip' : null);
    if (c.op === 'trap' && c.a4) return c.icon;
    return ICON_OF[c.op] || null;
  }
  // Fixed slots, counted from the left: the order of operations cards keep their PEMDAS order.
  const SLOT = { plug: 0, plugf: 0, writeout: 1, paren: 1, pow: 2, muldiv: 3, addsub: 4, rise: 0, read: 1, undef: 2, plugpt: 0, ptslope: 1, same: 2, perp: 3, write: 4, setx: 0, sety: 1 };
  const slot = c => (c.f4 || c.op === 'trap' ? null : SLOT[c.op] ?? null);
  const POINT_CARDS = ['rise', 'plugpt', 'ptslope'];
  const usesPoints = c => POINT_CARDS.includes(c.op) || (c.op === 'trap' && c.points);
  function targetSel(c) {
    const isA4 = OWN.includes(c.op) || c.f4 || (c.op === 'trap' && c.a4);
    if (!isA4 || (c.scope || 'both') !== 'part') return null;
    return '#equation .tok:not(.eq):not(.rel), #a4top .tok' + (usesPoints(c) || c.op === 'same' || c.op === 'perp' ? ', #graph .gtarget' : '');
  }
  // While a ◎ card is held, the graph's points glow (if the card uses them), and on Easy and Normal (or
  // on Hard after a wrong move in this question) the places this card can go are outlined.
  function onDrag(c, on) {
    const arena = $('arena');
    arena.classList.toggle('pts4', !!on && usesPoints(c));
    document.querySelectorAll('.ok4').forEach(el => el.classList.remove('ok4'));
    if (!on || !cur || !cur.act4 || !targetSel(c)) return;
    const hl = difficulty.highlight === 'on' || isTutorial() || (difficulty.highlight === 'afterWrong' && cur.wrong > 0);
    if (!hl) return;
    for (const el of document.querySelectorAll('#equation .tok[data-ref], #a4top .tok[data-ref], #graph .gtarget')) if (correct4(cur.state, c, el)) el.classList.add('ok4');
  }

  // ---------------------------------------------------------------- hands
  const evalFamily = (e, vn) => [{ op: 'plug', scope: 'part', v: e && e.val ? e.val : F(2), vn }, { op: 'paren', scope: 'part' }, { op: 'pow', scope: 'part' }, { op: 'muldiv', scope: 'part' }, { op: 'addsub', scope: 'part' }];
  const DECOYS = [0, 1, 2, 2];
  // Places a card could be dropped (for "would this card also be right here?").
  function candRefs(e) {
    const out = ['P0', 'P1', 'Q', 'G0', 'T', 'F', null];
    const a = active(e);
    if (a.k4 === 'eval') walk(a.tree, '', (n, p) => out.push('e' + p));
    if (a.k4 === 'formula') ['L', 'R'].forEach(s => a[s].forEach((o, i) => out.push(s + i)));
    return out;
  }
  const alsoRight = (e, c) => candRefs(e).some(r => correct4(e, c, r));
  function trap(trapName, lbl, txt, why, iconKey, extra = {}) { return { op: 'trap', a4: true, trap: trapName, scope: 'part', label: lbl, text: txt, why, icon: iconKey, ...extra }; }
  // The look-alike cards (decoys) and classic-mistake cards (traps) for a state's own move.
  function specials(e, correct, L, tut) {
    const out = { rule: [], decoys: [], traps: [] };
    const a = active(e);
    if (a.k4 === 'eval') {
      const ev = a;
      if (ev.tree.t === 'call') {
        const v = ev.tree.arg, f = ev.tree.name;
        out.decoys.push({ op: 'plugf', scope: 'part', v: fAdd(v, F(1)), fname: f });
        out.traps.push(trap('f times', `${f} ${TIMES} ${fracText(v)}`, `Multiply ${f} by ${fracText(v)}`,
          P(`${f}(${fracText(v)}) isn't ${f} times ${fracText(v)}. It means "put ${fracText(v)} into ${f}": the rule runs with ${fracText(v)} in place of ${ev.fn.vn}. Drop <b>Plug ${fracText(v)} into ${f}</b> on it.`), 'mul'));
      } else if (hasVar(ev.tree) && ev.val) {
        const v = ev.val;
        if (v.n < 0 && hasPowVar(ev.tree) && !tut) {
          const bad = fNeg(fMul(v, v));
          out.rule.push(trap('no brackets', `${ev.vn} = ${fracText(v)}<span class="ftag">no ( )</span>`, `Plug in ${fracText(v)} without brackets`,
            P(`Without brackets, ${MINUS}${fracText(fAbs(v))}² means ${MINUS}(${fracText(fAbs(v))}²) = ${fracText(bad)}: only the ${fracText(fAbs(v))} gets squared. But x is the whole number ${fracText(v)}, minus sign and all, so it goes in with brackets: (${fracText(v)})² = ${fracText(fMul(v, v))}.`) +
            P('<b>The rule:</b> a negative number plugged into a power always goes in brackets.'), 'plug'));
        }
        out.decoys.push({ op: 'plug', scope: 'part', v: fNeg(v), vn: ev.vn }, { op: 'plug', scope: 'part', v: fAdd(v, F(1)), vn: ev.vn });
      } else if (!hasVar(ev.tree)) {
        // "Add first": an addition or subtraction whose other side still has a product or power in it.
        let found = null;
        walk(ev.tree, '', n => { if (!found && (n.t === 'add' || n.t === 'sub') && isNum(n.a) && (n.b.t === 'mul' || n.b.t === 'pow') && isNum(leftLeaf(n.b))) found = n; });
        if (found) {
          const a1 = found.a.v, b1 = leftLeaf(found.b).v, wrong = found.t === 'add' ? fAdd(a1, b1) : fSub(a1, b1), sym = found.t === 'add' ? '+' : MINUS;
          out.traps.push(trap('add first', `${found.t === 'add' ? 'Add' : 'Subtract'} first`, `Do ${fracText(a1)} ${sym} ${paren(b1)} first`,
            P(`${found.t === 'add' ? 'Adding' : 'Subtracting'} can't go first here: the ${fracText(b1)} belongs to a ${found.b.t === 'pow' ? 'power' : 'product'}, ${treeText(found.b)}. Order of operations: parentheses, then powers, then ${TIMES} and ${DIV}, then + and ${MINUS}.`) +
            P(`Doing ${fracText(a1)} ${sym} ${paren(b1)} = ${fracText(wrong)} first would change the answer.`), found.t === 'add' ? 'add' : 'sub'));
        }
      }
    }
    if (e.k4 === 'fin' && !e.work) {
      out.rule.push(...(tut ? [] : [{ op: 'plugf', scope: 'part', v: e.rhs, fname: e.fn.name }]));
    }
    if ((e.k4 === 'slope' || e.k4 === 'line') && !e.work && e.pts && e.pts.length === 2 && correct.op === 'rise') {
      const [p, q] = e.pts;
      out.traps.push(trap('run over rise', 'Run / rise', 'Slope = run over rise',
        P(`Slope is <b>rise over run</b>: how far up, divided by how far across. From ${ptText(p)} to ${ptText(q)} it goes up ${fracText(fSub(q.y, p.y))} and across ${fracText(fSub(q.x, p.x))}, so the slope is ${fracText(fSub(q.y, p.y))}/${fracText(fSub(q.x, p.x))}, not the other way up.`), 'rise', { points: true }));
      out.traps.push(trap('mixed order', 'Rise / run (mixed)', `(${fracText(q.y)} ${MINUS} ${paren(p.y)}) / (${fracText(p.x)} ${MINUS} ${paren(q.x)})`,
        P(`The rise and the run have to start from the <b>same</b> point. Here the top starts from ${ptText(p)} and the bottom from ${ptText(q)}, so the sign comes out wrong. Use (${fracText(q.y)} ${MINUS} ${paren(p.y)})/(${fracText(q.x)} ${MINUS} ${paren(p.x)}).`), 'rise', { points: true }));
    }
    if (e.k4 === 'slope' && e.src === 'slopeint' && fSolved(e.work)) {
      const s = slopeOfFormula(e.work);
      if (!fz(s.b)) out.traps.push(trap('intercept as slope', `m = ${fracText(s.b)}`, `The slope is ${fracText(s.b)}`,
        P(`In y = mx + b the slope is m, the number in front of x. ${fracText(s.b)} is b, the y-intercept: where the line crosses the y-axis. Here the slope is ${fracText(s.m)}.`), 'read'));
    }
    if (e.k4 === 'line' && !e.work && e.m !== null && e.b === null) {
      const p = e.pts[0];
      if (!fEq(p.x, p.y)) out.traps.push(trap('swapped point', 'Plug (swapped)', `Plug ${ptText(p)} in as x = ${fracText(p.y)}, y = ${fracText(p.x)}`,
        P(`In ${ptText(p)} the first number is x and the second is y, so it goes in as ${fracText(p.y)} = ${fracText(e.m)}(${fracText(p.x)}) + b. Swapping them gives a different line that misses the point.`), 'plugpt', { points: true }));
    }
    if (e.k4 === 'line' && (e.q === 'parallel' || e.q === 'perp') && e.m === null) {
      out.rule.push(...(tut ? [] : [e.q === 'parallel' ? { op: 'perp', scope: 'part', v: fDiv(F(-1), e.ref.m) } : { op: 'same', scope: 'part' }]));
      // Perpendicular: the slope is the player's pick. The classic slips (flip only, sign only) are always dealt.
      if (e.q === 'perp') out.must = perpChoices(e.ref.m).slice(1);
      if (!fz(e.ref.b)) out.traps.push(trap('intercept as slope', `m = ${fracText(e.ref.b)}`, `Use ${fracText(e.ref.b)} as the slope`,
        P(`In y = ${lineTextOf(e.ref.m, e.ref.b)} the slope is ${fracText(e.ref.m)}, the number in front of x. ${fracText(e.ref.b)} is where it crosses the y-axis, which has nothing to do with the direction of the line.`), 'read'));
    }
    return out;
  }
  // A state's own family of cards (the other moves of its stage), dealt as wrong cards.
  function family(e) {
    const a = active(e);
    if (a.k4 === 'eval') {
      const fam = evalFamily(a, a.vn);
      if (a.tree.t === 'call') fam.unshift({ op: 'plugf', scope: 'part', v: a.tree.arg, fname: a.tree.name }, { op: 'writeout', scope: 'part' });
      if (a.lhs === 'm' || e.k4 === 'slope' || e.k4 === 'line') fam.push({ op: 'undef', scope: 'part' });
      if (!a.val) fam.splice(fam.findIndex(c => c.op === 'plug'), 1);
      return fam;
    }
    if (e.k4 === 'fin') return [{ op: 'writeout', scope: 'part' }, ...evalFamily(null, e.fn.vn).slice(1)];
    if (e.k4 === 'slope') return [{ op: 'rise', scope: 'part' }, { op: 'read', scope: 'part' }, { op: 'undef', scope: 'part' }, ...evalFamily(null).slice(1, 4)];
    if (e.k4 === 'line') return [...['rise', 'plugpt', 'ptslope', 'same', 'write'].map(op => ({ op, scope: 'part' })),
      ...(e.ref ? perpChoices(e.ref.m) : [{ op: 'perp', scope: 'part', v: F(-1, 2) }]).filter(c => !(e.q === 'parallel' && fEq(c.v, e.ref.m)))];
    if (e.k4 === 'icept') return [{ op: 'setx' }, { op: 'sety' }, { op: 'plugpt', scope: 'part' }, { op: 'write', scope: 'part' }, { op: 'read', scope: 'part' }];
    return [];
  }
  // The slope cards for a perpendicular line: the negative reciprocal first, then flip only, sign only, the same slope.
  function perpChoices(m) {
    return [fDiv(F(-1), m), fDiv(F(1), m), fNeg(m), m].map(v => ({ op: 'perp', scope: 'part', v }));
  }
  function ownHand(e, correct, size) {
    const tut = isTutorial(), L = lvl(), sp = specials(e, correct, L, tut);
    const hand = [correct], seen = new Set([cardLabel(correct)]);
    const tryAdd = c => { if (hand.length >= size) return; const k = cardLabel(c); if (seen.has(k)) return; if (c.op !== 'trap' && alsoRight(e, c)) return; seen.add(k); hand.push(c); };
    (sp.must || []).forEach(tryAdd);
    if (!tut && L >= 3) sp.traps.slice(0, 1).forEach(tryAdd);
    sp.rule.forEach(tryAdd);
    if (!tut) shuffle(sp.decoys).slice(0, DECOYS[L]).forEach(tryAdd);
    // Playtest fix: icept used to deal both Set x = 0 and Set y = 0 while both were right, breaking the
    // one-right-card rule. The other Set card is left out (alsoRight) until the first intercept is found.
    shuffle(family(e)).forEach(tryAdd);
    // Still short (small families): any other Act 4 card that isn't right here.
    shuffle([...evalFamily(null), { op: 'rise', scope: 'part' }, { op: 'read', scope: 'part' }, { op: 'write', scope: 'part' }, { op: 'plugpt', scope: 'part' }]).forEach(tryAdd);
    return shuffle(hand);
  }
  function fHand(e, correct, size) {
    const base = fSteps(e), tut = isTutorial();
    const useful = c => ((c.op === 'comb' || c.op === 'dist') ? ['L', 'R'].some(s => e[s].some((o, i) => fLegalPart(e, c, s + i))) : fSteps(fApply(e, c)) < base || fShrinks(e, c));
    const classic = [], rest = [];
    if (correct.op === '+' || correct.op === '-') classic.push({ ...correct, op: correct.op === '+' ? '-' : '+' });
    if (correct.op === '/') { classic.push({ ...correct, op: '*' }); if (correct.t.lit) classic.push(fT('-', T(1, correct.t.lit))); }
    if (correct.op === '*') classic.push({ ...correct, op: '/' });
    if (known('distribute')) classic.push({ op: 'dist', f4: true, scope: 'part' });
    if (known('liketerms')) classic.push({ op: 'comb', f4: true, scope: 'part' });
    const terms = [...e.L, ...e.R].flatMap(o => (o.g ? [...o.items, o.m] : [o])).filter(o => o.k.n);
    for (const t of terms) {
      const a = { ...t, k: fAbs(t.k) };
      if (!a.den && a.k.d === 1 && !(isOne(a) && !a.lit)) rest.push(fT('+', a), fT('-', a));
      if (a.lit && a.lit !== e.v) for (const ch of a.lit.replace(e.v, '')) rest.push(fT('/', T(1, ch)), fT('*', T(1, ch)));
      if (!a.lit && a.k.d === 1 && a.k.n > 1) rest.push(fT('/', T(a.k.n)), fT('*', T(a.k.n)));
      if (a.k.d > 1) rest.push(fT('*', T(a.k.d)), fT('/', T(a.k.d)));
    }
    rest.push(fT('/', T(1, e.v)));
    const hand = [correct], seen = new Set([cardLabel(correct)]);
    const fallback = shuffle([2, 3, 4, 5]).flatMap(n => [fT('+', T(n)), fT('-', T(n))]);
    for (const c of [...shuffle(classic), ...shuffle(rest), ...fallback]) {
      if (hand.length >= size) break;
      if (seen.has(cardLabel(c)) || useful(c)) continue;
      if (tut && (c.op === 'comb' || c.op === 'dist')) continue;
      seen.add(cardLabel(c)); hand.push(c);
    }
    return shuffle(hand);
  }
  function makeHand4(e, correct, size) {
    if (correct && correct.f4) return fHand(active(e).k4 === 'formula' ? active(e) : e, correct, size);
    const a = active(e);
    if (a !== e && !a.k4) {      // an equation or inequality in one letter: its own engine deals
      const h = wKind(a) === 'a3' ? A3.makeHand(a, correct, size) : A2.makeHand(a, correct, size);
      return h;
    }
    return ownHand(e, correct, size);
  }

  // ================================================================ wrong moves
  const NAMES = { add: 'adding', sub: 'subtracting', mul: 'multiplying', div: 'dividing', pow: 'the power' };
  const FAM_SYM = { addsub: `a + or ${MINUS}`, muldiv: `a ${TIMES} (written ·) or a fraction bar`, pow: 'a small ² or ³', paren: 'a pair of parentheses', undef: 'the fraction bar with 0 underneath', plug: 'the letter' };   // playtest fix: undef and plug had no entry, so a hint read "(undefined)"
  // Why an operation can't be done yet: the first thing under it that has to go first.
  function blocker(tree, p) {
    const n = at(tree, p); if (!n) return null;
    let found = null;
    walk(n, p, (m, q) => { if (!found && q !== p && isRedex(m)) found = { node: m, path: q }; });
    return found;
  }
  function evalWhy(ev, card, ref, long) {
    const p = pathOfRef(ref), node = p !== null ? at(ev.tree, p) : null, want = evalCanon(ev);
    const role = node ? node.t : null;
    if (ev.tree.t === 'call') {
      if (card.op === 'writeout') return long ? P(`${treeText(ev.tree)} asks for an <b>output</b>: what ${ev.tree.name} gives back when ${fracText(ev.tree.arg)} goes in. Writing out the rule is for questions like ${ev.tree.name}(x) = 11, where the output is known. Here, drop <b>Plug ${fracText(ev.tree.arg)} into ${ev.tree.name}</b> on ${treeText(ev.tree)}.`) : `${treeText(ev.tree)} asks for an output: plug ${fracText(ev.tree.arg)} into ${ev.tree.name}.`;
      if (card.op === 'plugf') return long ? P(`The number inside the brackets is what goes in: ${treeText(ev.tree)} means put ${fracText(ev.tree.arg)} into ${ev.tree.name}.`) : `${treeText(ev.tree)} means put ${fracText(ev.tree.arg)} in, not ${fracText(card.v)}.`;
      return long ? P(`${treeText(ev.tree)} is a function's output, not a number yet. First plug ${fracText(ev.tree.arg)} into ${ev.tree.name}: the rule comes out with ${fracText(ev.tree.arg)} in place of ${ev.fn.vn}.`) : `First plug ${fracText(ev.tree.arg)} into ${ev.tree.name}.`;
    }
    if (hasVar(ev.tree)) {
      if (card.op === 'plug' && !fEq(card.v, ev.val)) return long ? P(`The question says ${ev.vn} = ${fracText(ev.val)}, so that's the number that goes in, everywhere ${ev.vn} appears.`) : `${ev.vn} is ${fracText(ev.val)} here, not ${fracText(card.v)}.`;
      if (card.op === 'plug') return long ? P(`Plug in goes on a letter ${ev.vn}: drop it on any ${ev.vn} and every ${ev.vn} fills in at once.`) : `Right card: drop it on an ${ev.vn}.`;
      return long ? P(`${ev.vn} is still a letter, so there's nothing to work out yet. Plug in ${ev.vn} = ${fracText(ev.val)} first, then do the operations in order.`) : `Plug in ${ev.vn} = ${fracText(ev.val)} first.`;
    }
    if (card.op === 'plug') return long ? P(`Every ${ev.vn} has already been replaced by a number. What's left is plain arithmetic, done in order: parentheses, powers, ${TIMES} and ${DIV}, then + and ${MINUS}.`) : `There's no letter left to plug into.`;
    if (card.op === 'plugf' || card.op === 'writeout') return long ? P('The function has already been used: what is left is arithmetic.') : 'The function has already been used.';
    // undefined / dividing by 0
    if (card.op === 'undef') {
      const zero = node && node.t === 'div' && isRedex(node) && fz(node.b.v);
      if (zero) return long ? P('Right card, wrong place: drop it on the fraction bar with 0 underneath.') : 'Drop it on the fraction with 0 underneath.';
      return long ? P('A slope is only undefined when the run (the bottom) is 0: the line goes straight up and down. Here the bottom isn\'t 0, so work it out.') : `The bottom isn't 0, so the slope is a number.`;
    }
    if (node && node.t === 'div' && isRedex(node) && fz(node.b.v) && card.op === 'muldiv')
      return long ? P(`Nothing can be divided by 0. When the run is 0 the two points are straight above each other, the line is vertical, and its slope is <b>undefined</b>. Play Declare undefined on the fraction.`) : `You can't divide by 0: declare the slope undefined.`;
    // a family card dropped on the wrong kind of symbol, or somewhere it can't go yet
    const famOf = n => (n && n.t === 'par' ? 'paren' : n ? FAMILY[n.t] : null);
    if (card.op === 'paren') {
      if (!node || node.t !== 'par') return long ? P(`Do the parentheses goes on a pair of brackets ( ). ${want ? describeWant(ev, want) : ''}`) : `Do the parentheses goes on a pair of brackets.`;
      const b = blocker(ev.tree, p + 'a');
      return long ? P(`There's more than one step inside these brackets. Inside parentheses the usual order still holds, so first ${b ? `do ${treeText(b.node)}` : 'the step inside'}.`) : `Inside the brackets, ${b ? treeText(b.node) : 'that step'} comes first.`;
    }
    if (!node || !OPS.includes(node.t)) {
      if (node && node.t === 'num') return long ? P(`That's a number on its own. Operation cards go on the symbol: ${FAM_SYM[card.op] || 'the operation'}. ${want ? describeWant(ev, want) : ''}`) : `Drop it on ${FAM_SYM[card.op] || 'its symbol'}.`;
      return long ? P(`That card goes on ${FAM_SYM[card.op] || 'its symbol'}. ${want ? describeWant(ev, want) : ''}`) : `That card goes on ${FAM_SYM[card.op] || 'its symbol'}.`;
    }
    if (famOf(node) !== card.op) {
      return long ? P(`That symbol is ${NAMES[node.t] === 'the power' ? 'a power' : NAMES[node.t]}, and the card is for ${FAM_SYM[card.op]}. ${want ? describeWant(ev, want) : ''}`) : `That's ${node.t === 'pow' ? 'a power' : NAMES[node.t]}: this card goes on ${FAM_SYM[card.op]}.`;
    }
    // the right family, but something under it comes first
    const b = blocker(ev.tree, p);
    if (b) {
      const first = b.node, inPar = at(ev.tree, b.path.slice(0, -1));
      const reason = inPar && inPar.t === 'par' ? 'Parentheses come first.' : first.t === 'pow' ? 'Powers come before multiplying, dividing, adding and subtracting.' : (first.t === 'mul' || first.t === 'div') ? 'Multiplying and dividing come before adding and subtracting.' : 'That part has to be worked out first.';
      if (long) {
        let ex = '';
        if ((node.t === 'add' || node.t === 'sub') && (first.t === 'mul' || first.t === 'div')) ex = ` For example, in 2 + 3 · 4 you do 3 · 4 = 12 first, then 2 + 12 = 14. Adding first gives 5 · 4 = 20, which is wrong.`;
        if (node.t === 'mul' && first.t === 'pow') ex = ` For example, 3 · 2² means 3 · 4 = 12, not 6² = 36.`;
        return P(`${reason} Here ${treeText(first)} has to be done before this.${ex}`);
      }
      return `${reason} Do ${treeText(first)} first.`;
    }
    return long ? P('That move is not allowed here.') : 'That move is not allowed here.';
  }
  function describeWant(ev, want) {
    if (want.op === 'undef') return 'The bottom of the fraction is 0: declare the slope undefined.';
    const p = pathOfRef(want.ref), n = at(ev.tree, p);
    const what = want.op === 'paren' ? `the parentheses, ${treeText(n)}` : treeText(n);
    return `Next in order: ${what}.`;
  }
  // Short reason (shown under the equation) and long one (the Why? button) for a wrong move.
  function why4(e, card, target, long) {
    const ref = refOf(target), a = active(e), want = canon4(e);
    if (card.op === 'trap') return long ? card.why : `That's a trap: it isn't true. Tap Why? to see why.`;
    // own moves of each kind
    if (a.k4 === 'eval' && (OWN.includes(card.op))) {
      if (e.k4 === 'line' || e.k4 === 'slope') {
        if (['plugpt', 'ptslope', 'same', 'perp', 'write', 'rise', 'read'].includes(card.op)) return long ? P(`First finish working out the slope: ${describeWant(a, want)}`) : 'First finish working out the slope.';
      }
      return evalWhy(a, card, ref, long);
    }
    if (e.k4 === 'fin' && !e.work) {
      if (card.op === 'writeout') return long ? P(`Write out goes on ${e.fn.name}(${e.fn.vn}).`) : `Drop it on ${e.fn.name}(${e.fn.vn}).`;
      if (card.op === 'plugf') return long ? P(`${e.fn.name}(${e.fn.vn}) ${e.rel} ${fracText(e.rhs)} tells you the <b>output</b>: ${fracText(e.rhs)}. Plugging ${fracText(e.rhs)} in would treat it as an input. To find the input, write out ${e.fn.name}(${e.fn.vn}) as its rule and solve for ${e.fn.vn}.`) : `${fracText(e.rhs)} is the output, not the input: write out the rule and solve.`;
      return long ? P(`${e.fn.name}(${e.fn.vn}) is a name for the rule ${treeText(e.fn.rule)}. Write it out first, then solve.`) : `Write out ${e.fn.name}(${e.fn.vn}) first.`;
    }
    if (e.k4 === 'slope' && (e.src === 'slopeint' || e.src === 'standard') && OWN.includes(card.op)) {
      if (!fSolved(e.work)) return long ? P(`The number in front of x is only the slope once y is alone: y = mx + b. Solve for y first.`) : 'Solve for y first.';
      if (card.op === 'read') {
        const r = ref && a.k4 === 'formula' ? a[ref[0]] && a[ref[0]][+ref.slice(1)] : null;
        if (r && !r.lit) return long ? P(`${fracText(r.k)} is b, the y-intercept: where the line crosses the y-axis. The slope is the number in front of x.`) : `That's b, the y-intercept. The slope is the number in front of x.`;
        return long ? P('Drop Read the slope on the x-term: its number is the slope.') : 'Drop it on the x-term.';
      }
      return long ? P(`The line is in y = mx + b form, so the slope can be read straight off: the number in front of x.`) : 'y is alone: read the slope off.';
    }
    if ((e.k4 === 'slope' || e.k4 === 'line') && !e.work && OWN.includes(card.op)) {
      if (card.op === 'rise' && e.m === null && e.pts && e.pts.length === 2) return long ? P('Rise over run goes on one of the two points on the graph: it measures from that point to the other.') : 'Drop it on one of the points on the graph.';
      if (e.k4 === 'slope' && card.op === 'read') return long ? P('There\'s no equation to read the slope from: the line is given by two points. Use rise over run.') : 'Use rise over run from the points.';
      if (e.k4 === 'line') {
        if (e.m === null && (card.op === 'plugpt' || card.op === 'ptslope' || card.op === 'write')) return long ? P(`The slope isn't known yet. ${e.q === 'twopts' ? 'Find it with rise over run between the two points.' : e.q === 'parallel' ? 'Parallel lines have the same slope: use Same m on the given line.' : 'Perpendicular lines have negative reciprocal slopes: pick the slope that is the given one flipped over with its sign changed.'}`) : 'Find the slope first.';
        if (e.m === null && card.op === 'perp' && card.v && e.q === 'perp') {
          const m = e.ref.m, want = fDiv(F(-1), m), v = card.v;
          if (fEq(v, want)) return long ? P('Right slope: drop it on the given line.') : `Drop it on the given line's slope.`;
          const what = fEq(v, fDiv(F(1), m)) ? `You flipped ${fracText(m)} over but kept its sign.` : fEq(v, fNeg(m)) ? `You changed the sign of ${fracText(m)} but didn't flip it over.` : fEq(v, m) ? `${fracText(m)} is the same slope: that's a parallel line.` : `${fracText(v)} isn't the negative reciprocal of ${fracText(m)}.`;
          return long ? P(`${what} Perpendicular slopes are <b>negative reciprocals</b>: flip the fraction over <b>and</b> change the sign. ${fracText(m)} becomes ${fracText(want)}, and ${fracText(m)} ${TIMES} ${paren(want)} = ${MINUS}1.`) : `${what} Flip it and change the sign.`;
        }
        if (e.m === null && (card.op === 'same' || card.op === 'perp')) {
          if (e.q === 'twopts') return long ? P('There is no given line to copy a slope from. Use rise over run between the two points.') : 'Use rise over run between the points.';
          if ((card.op === 'same') === (e.q === 'parallel')) return long ? P('Right card: drop it on the given line\'s slope.') : `Drop it on the given line's slope.`;
          return long ? P(e.q === 'parallel' ? `Parallel lines never meet, so they go in the same direction: the <b>same</b> slope. The negative reciprocal is for perpendicular lines, which cross at a right angle.` : `Perpendicular lines cross at a right angle. Their slopes are negative reciprocals: flip the fraction and change the sign. The same slope is for parallel lines.`) : (e.q === 'parallel' ? 'Parallel lines have the same slope.' : 'Perpendicular lines have negative reciprocal slopes.');
        }
        if (e.b === null && card.op === 'write') return long ? P(`b isn't known yet. Plug the point into y = mx + b to find it.`) : 'Find b first: plug a point in.';
        if (e.b === null && (card.op === 'plugpt' || card.op === 'ptslope')) return long ? P('Drop it on a point the line goes through.') : 'Drop it on the point.';
        // Playtest fix: on slope-and-point, parallel and perpendicular questions these fell through to
        // "Start with rise over run", which told the player to use the card they had just played wrongly.
        if (e.m === null && card.op === 'rise' && (e.q === 'parallel' || e.q === 'perp')) return long ? P(`There's only one point, so there's no rise over run to measure. The slope comes from the given line: ${e.q === 'parallel' ? 'parallel lines have the same slope, so use Same m' : 'perpendicular slopes are negative reciprocals, so pick that slope'} on its slope.`) : `The slope comes from the given line: use ${e.q === 'parallel' ? 'Same m' : 'its negative reciprocal'}.`;
        if (e.m !== null && (card.op === 'same' || card.op === 'perp')) return long ? P(`The slope is already known: ${fracText(e.m)}. ${e.q === 'parallel' || e.q === 'perp' ? '' : 'There is no other line here to copy a slope from. '}Now find b.`) : 'The slope is already known. Now find b.';
        if (e.m !== null && card.op === 'rise') return long ? P(`The slope is already known: ${fracText(e.m)}.`) : 'The slope is already known.';
        if (e.b !== null && card.op === 'write') return long ? P('Drop Write the line on y = mx + b.') : 'Drop it on y = mx + b.';
        if (e.b !== null) return long ? P(`Both m and b are known: write the line, y = ${lineTextOf(e.m, e.b)}.`) : 'm and b are known: write the line.';
      }
      if (card.op === 'undef') return long ? P('Declare undefined is for a fraction with 0 underneath, once the slope has been worked out.') : 'Nothing is undefined yet.';
      if (e.k4 === 'line' && e.m === null && (e.q === 'parallel' || e.q === 'perp')) return long ? P(`Start with the slope: it comes from the given line. ${e.q === 'parallel' ? 'Use Same m on its slope' : 'Pick its negative reciprocal'}.`) : `Start with the slope of the given line.`;
      if (e.k4 === 'line' && e.m !== null) return long ? P(`The slope is ${fracText(e.m)}. Next find b: plug the point in.`) : 'Next find b: plug the point in.';
      return long ? P('Start with rise over run between the two points.') : 'Start with rise over run.';
    }
    if (e.k4 === 'icept' && !e.work && OWN.includes(card.op)) {
      if (card.op === 'setx' && e.found.y !== null) return long ? P('The y-intercept is already found. Setting y = 0 finds the other one.') : 'The y-intercept is already found.';
      if (card.op === 'sety' && e.found.x !== null) return long ? P('The x-intercept is already found. Setting x = 0 finds the other one.') : 'The x-intercept is already found.';
      return long ? P(`An intercept is where the line crosses an axis. On the y-axis x is 0, so set x = 0; on the x-axis y is 0, so set y = 0.`) : 'Set x = 0 or y = 0 to find where it crosses an axis.';
    }
    if (a.k4 === 'formula' && (card.f4 || OWN.includes(card.op))) {
      if (OWN.includes(card.op)) return long ? P(`First get ${a.v} alone: ${fText(a)}.`) : `First get ${a.v} alone.`;
      return fWhy(a, card, ref, want, long);
    }
    // an equation or inequality in one letter: its engine explains
    if (!a.k4) {
      if (OWN.includes(card.op)) return long ? P(`First solve for ${a.v || 'x'}.`) : `First solve for ${a.v || 'x'}.`;
      const fakeCur = { state: a, path: [{ move: want }], step: 0 };
      if (!long) return (wKind(a) === 'a3' ? A3 : A2).whyWrong(fakeCur, card, target);
      for (const fn of WHY_EXPLAINERS) { if (fn === explain4) continue; const h = fn({ state: a, card, correct: want, ref }); if (h) return h; }
      return null;
    }
    return long ? P('That card doesn\'t fit here.') : `That card doesn't fit here.`;
  }
  function fWhy(e, card, ref, want, long) {
    if (card.op === 'comb') return long ? P('Like terms have exactly the same letters: 2l and 5l combine, but 2l and 2w don\'t. Combine needs two of them on the same side.') : 'Combine needs two like terms (the same letters) on one side.';
    if (card.op === 'dist') return long ? P('Distribute goes on a number in front of parentheses.') : 'Distribute goes on parentheses.';
    const after = fApply(e, card, ref);
    if (!long) {
      if (want.op === 'dist') return `That's allowed, but clear the parentheses first. It would give ${fText(after)}`;
      if ((want.op === '+' || want.op === '-') && (card.op === '*' || card.op === '/')) return `That's allowed, but undo the + or ${MINUS} part first, then the ${TIMES} or ${DIV}.`;
      return `That's allowed, but ${e.v} still isn't alone: ${fText(after)}`;
    }
    let how;
    const tt = (e.L.some(o => hasV(o, e.v)) ? e.L : e.R);
    if (want.op === 'dist') how = 'Clear the parentheses first: multiply the term in front into each term inside.';
    else if (want.op === 'comb') how = 'Two like terms are on the same side. Combine them first.';
    else if (want.op === '+' || want.op === '-') how = `${signedT(want.t)} is ${want.op === '-' ? 'added to' : 'taken from'} the ${e.v}-term. Undo that first: ${fCardText(want).toLowerCase()}. Letters work just like numbers.`;
    else if (want.op === '/') how = `${e.v} is multiplied by ${signedT(want.t)}. Undo multiplying with dividing: divide both sides by ${signedT(want.t)}, and ${tt.length === 1 ? tBody({ ...tt[0], k: fAbs(tt[0].k) }, '', false) : 'it'} over ${signedT(want.t)} leaves just ${e.v}.`;
    else how = `${fCardText(want)}: it clears what's attached to ${e.v}.`;
    return P(`${fCardText(card)} is allowed, but it turns it into ${fHtml(after)}, which is no closer to ${e.v} alone.`) + P(`<b>What works here:</b> ${how}`);
  }
  function isCorrect(cur, card, target) { return correct4(cur.state, card, target); }
  const whyWrong = (cur, card, target) => why4(cur.state, card, target, false);
  function explain4({ state: e, card, ref }) {
    if (!e || !e.k4 || !card) return null;
    let target = ref;
    if (typeof ref === 'string' && !/^(e|L|R|P|Q|G|T|F)/.test(ref)) target = null;
    // whyWrong for delegated states needs the element (Act 3 checks the sign's role); the ref string works for the rest
    return why4(e, card, target, true);
  }
  if (typeof registerWhy === 'function') registerWhy(explain4);

  // ================================================================ rendering
  function topEl() {
    let t = $('a4top');
    if (!t) { t = document.createElement('div'); t.id = 'a4top'; $('equation').insertAdjacentElement('beforebegin', t); }
    return t;
  }
  function graphEl() {
    let g = $('graph');
    if (!g) { g = document.createElement('div'); g.id = 'graph'; $('equation').insertAdjacentElement('afterend', g); }
    return g;
  }
  function clear() {
    const t = $('a4top'); if (t) { t.innerHTML = ''; t.classList.remove('show'); }
    drawGraph(null);
    document.querySelectorAll('.fm4').forEach(el => el.remove());
  }
  const TOK = (html, role, ref, cls = '') => { const d = document.createElement('div'); d.className = `tok a4 r4-${role} ${cls}`; d.dataset.role = role; if (ref !== null && ref !== undefined) d.dataset.ref = ref; d.innerHTML = html; return d; };
  const EQTOK = (t = '=') => { const q = document.createElement('div'); q.className = 'tok eq'; q.dataset.role = 'eq'; q.textContent = t; return q; };
  function nodeEl(n, path, wrapNeg) {
    const w = document.createElement('span'); w.className = 'n4'; w.dataset.node = path;
    const put = el => w.appendChild(el), ref = 'e' + path;
    switch (n.t) {
      case 'num': put(TOK(n.v.n < 0 && wrapNeg ? `(${fracHtml(n.v)})` : fracHtml(n.v), 'num', ref)); break;
      case 'var': put(TOK(XI(n.name), 'var', ref, 'var')); break;
      case 'call': put(TOK(`${n.name}(${fracHtml(n.arg)})`, 'call', ref)); break;
      case 'add': case 'sub': put(nodeEl(n.a, path + 'a', false)); put(TOK(n.t === 'add' ? '+' : MINUS, 'op', ref, 'fam-addsub')); put(nodeEl(n.b, path + 'b', true)); break;
      case 'mul': {
        put(nodeEl(n.a, path + 'a', false));
        const imp = implicitMul(n); if (!imp) put(TOK('·', 'op', ref, 'fam-muldiv'));
        const b = nodeEl(n.b, path + 'b', true); put(b);
        // Playtest fix: 3x and x² showed as "3 x" and "x ²" (each box's padding). Written-together parts sit tight.
        if (imp) { const f = b.querySelector('.tok'); if (f && !f.classList.contains('r4-par')) f.classList.add('tightL'); }
        break;
      }
      case 'div': {
        w.className = 'n4 frac4';
        const top = document.createElement('span'), bot = document.createElement('span');
        top.className = bot.className = 'row4';
        top.appendChild(nodeEl(n.a, path + 'a', false)); bot.appendChild(nodeEl(n.b, path + 'b', false));
        w.append(top, TOK('<span class="bar4"></span>', 'bar', ref, 'fam-muldiv'), bot);
        break;
      }
      case 'pow': put(nodeEl(n.a, path + 'a', true)); put(TOK(n.e === 3 ? '³' : '²', 'pow', ref, 'sup4 fam-pow tightL')); break;
      case 'par': put(TOK('(', 'par', ref, 'fam-paren')); put(nodeEl(n.a, path + 'a', false)); put(TOK(')', 'par', ref, 'fam-paren')); break;
      case 'neg': put(TOK(MINUS, 'sign', null)); put(nodeEl(n.a, path + 'a', true)); break;
    }
    return w;
  }
  function renderEval(e) {
    const el = $('equation');
    if (e.lhs) { el.appendChild(TOK(e.lhs, 'lhs', null, 'lhs4')); el.appendChild(EQTOK()); }
    if (e.undef) { el.appendChild(TOK('undefined', 'result', null, 'undef4')); return; }
    if (e.tree.t === 'call' && e.lhs) { el.innerHTML = ''; el.appendChild(nodeEl(e.tree, '', false)); el.appendChild(EQTOK()); el.appendChild(TOK('?', 'q', null, 'q4')); return; }
    el.appendChild(nodeEl(e.tree, '', false));
  }
  function renderFormula(e) {
    const el = $('equation');
    for (const s of ['L', 'R']) {
      const side = e[s];
      if (!side.length) el.appendChild(TOK('0', 'num', s + 'z'));
      side.forEach((o, i) => { const t = TOK(fTermStr(o, i === 0, true, e.v), o.g ? 'group' : hasV(o, e.v) ? 'vterm' : 'term', s + i, 'f4t'); t.dataset.side = s; el.appendChild(t); });
      if (s === 'L') el.appendChild(EQTOK());
    }
  }
  function renderWork(w) {
    switch (wKind(w)) {
      case 'eval': return renderEval(w);
      case 'formula': return renderFormula(w);
      case 'a3': return A3.render(w);
      default: return A2.render(w);
    }
  }
  const banner = html => { const t = topEl(), h = askLine() + (html || ''); t.innerHTML = h; t.classList.toggle('show', !!h); };
  const ruleHtml = fn => `${fn.name}(${XI(fn.vn)}) = ${treeHtml(fn.rule)}`;
  const treeHtml = n => treeText(n).replace(/(?<![a-z])([a-z])(?![a-z])/g, m => XI(m));   // playtest fix: \b missed the x in "2x"
  function templateToks(e, inTop) {
    const mT = e.m === null ? '<span class="slot4">m</span>' : fIs(e.m, 1) ? '' : fIs(e.m, -1) ? MINUS : fracHtml(e.m);
    const bT = e.b === null ? '+ <span class="slot4">b</span>' : fz(e.b) ? '' : `${e.b.n < 0 ? MINUS : '+'} ${fracHtml(fAbs(e.b))}`;
    if (inTop) return `<span class="tmpl4">y = ${mT}x ${bT}</span>`;
    const el = $('equation');
    el.appendChild(TOK('y', 'ty', 'T', 'tmpl')); el.appendChild(EQTOK());
    el.appendChild(TOK(`${mT}${XI('x')}`, 'tm', 'T', 'tmpl'));
    if (bT) el.appendChild(TOK(bT, 'tb', 'T', 'tmpl'));
  }
  // ---------------------------------------------------------------- test-style questions
  // Every problem opens with one instruction worded the way a math test asks it ("Evaluate f(3).",
  // "Find the slope of the line through (2, 1) and (5, 7)."). It is picked once per problem from a few
  // real-test phrasings (never the same one twice in a row) and stays put while the state changes.
  // index.html shows it in its own prompt line when it has one; otherwise it heads the Act 4 banner.
  const PROMPT_CACHE = new WeakMap(), lastAsk = {};
  const askPick = (kind, opts) => { const fresh = opts.filter(t => t !== lastAsk[kind]); return (lastAsk[kind] = pick(fresh.length ? fresh : opts)); };
  const NW = h => `<span class="nw4">${h}</span>`;   // an equation or point in a question never breaks across lines
  const fnHtml = fn => NW(`${fn.name}(${XI(fn.vn)}) = ${treeHtml(fn.rule)}`);
  function promptOf(e) {
    const pts = n => (e.graph && e.graph.labels === false ? (n === 2 ? 'the two points shown' : 'the point shown') : e.pts.slice(0, n).map(p => NW(ptText(p))).join(' and '));
    const then = !e.then ? '' : e.then.q === 'out' ? ` Call the line f(${XI('x')}), then find f(${fracHtml(e.then.input)}).` : ` Then find ${XI('x')} where the line reaches ${XI('y')} = ${fracHtml(e.then.y)}.`;
    switch (e.k4) {
      case 'eval': {
        if (e.fn && e.tree.t === 'call') {
          const fx = `${e.fn.name}(${fracHtml(e.tree.arg)})`;
          return askPick('out', [`Given ${fnHtml(e.fn)}, find ${fx}.`, `Evaluate ${fx} for ${fnHtml(e.fn)}.`, `If ${fnHtml(e.fn)}, what is ${fx}?`]);
        }
        const v = `${XI(e.vn)} = ${fracHtml(e.val)}`;
        return askPick('eval', [`Evaluate the expression when ${v}.`, `Evaluate for ${v}.`, `Find the value of the expression when ${v}.`]);
      }
      case 'fin': {
        const q = `${e.fn.name}(${XI(e.fn.vn)}) ${e.rel} ${fracHtml(e.rhs)}`, v = XI(e.fn.vn);
        if (e.rel !== '=') return askPick('fin-ineq', [`Given ${fnHtml(e.fn)}, solve ${q}.`, `For ${fnHtml(e.fn)}, find all values of ${v} where ${q}.`]);
        return askPick('fin', [`Given ${fnHtml(e.fn)}, solve ${q}.`, `For ${fnHtml(e.fn)}, find ${v} when ${q}.`, `If ${fnHtml(e.fn)}, for what value of ${v} is ${q}?`]);
      }
      case 'formula': return askPick('formula', [`Solve for ${XI(e.v)}.`, `Solve the formula for ${XI(e.v)}.`, `Solve ${NW(fText(e))} for ${XI(e.v)}.`]);
      case 'slope':
        if (e.src === 'slopeint' || e.src === 'standard') return askPick('slope-eq', ['Find the slope of the line.', 'What is the slope of this line?', 'Find the slope.']);
        if (e.src === 'graph') return askPick('slope-graph', ['Find the slope of the line shown.', 'Find the slope of the graphed line.']);
        return askPick('slope-pts', [`Find the slope of the line through ${pts(2)}.`, `Find the slope of the line that passes through ${pts(2)}.`]);
      case 'line': {
        const write = askPick('line', ['Write an equation of the line', 'Find the equation of the line', 'Write the equation, in slope-intercept form, of the line']);
        if (e.q === 'twopts') return `${write} through ${pts(2)}.${then}`;
        if (e.q === 'parallel' || e.q === 'perp') return `${write} through ${pts(1)} that is ${e.q === 'parallel' ? 'parallel' : 'perpendicular'} to ${NW(`${XI('y')} = ${lineHtml(e.ref.m, e.ref.b)}`)}.${then}`;
        return `${write} with slope ${fracHtml(e.m0)} that passes through ${pts(1)}.${then}`;
      }
      case 'icept': return askPick('icept', [`Find the ${XI('x')}- and ${XI('y')}-intercepts of ${NW(stdHtml(e))}.`, `Where does ${NW(stdHtml(e))} cross the axes?`]) + (e.then ? then : '');
    }
    return '';
  }
  function prompt(e) {
    if (!e || !e.k4) return '';
    if (!PROMPT_CACHE.has(e)) PROMPT_CACHE.set(e, promptOf(e));
    return PROMPT_CACHE.get(e);
  }
  // The question line inside the banner, only when index.html has no prompt line of its own.
  const askLine = () => (!$('prompt') && cur && cur.act4 && cur.start ? `<div class="ask4">${prompt(cur.start)}</div>` : '');

  function render(e) {
    clear();
    const el = $('equation'); if (typeof clearNotes === 'function') clearNotes();
    el.innerHTML = ''; el.classList.add('a4');
    const fit = () => { el.classList.add('a2'); if (A2.fitEq) A2.fitEq(); };
    switch (e.k4) {
      case 'eval':
        banner(e.lineDone ? `<span class="lab4">Line</span> ${ruleHtml(e.fn)}` : '');
        if (e.graph) drawGraph(e.graph);
        renderEval(e); fit(); return;
      case 'formula':
        banner('');
        renderFormula(e); fit(); return;
      case 'fin': {
        banner(e.lineDone ? `<span class="lab4">Line</span> ${ruleHtml(e.fn)} · where does it reach ${XI('y')} = ${fracHtml(e.rhs)}?` : '');
        if (e.graph) drawGraph(e.graph);
        if (e.work) { renderWork(e.work); if (wKind(e.work) !== 'a3') fit(); return; }
        el.appendChild(TOK(`${e.fn.name}(${XI(e.fn.vn)})`, 'fx', 'F', 'fx4'));
        el.appendChild(EQTOK(e.rel)); el.lastChild.classList.add('rel');
        el.appendChild(TOK(fracHtml(e.rhs), 'num', null));
        fit(); return;
      }
      case 'slope': {
        banner('');
        drawGraph(e.graph);
        if (e.m !== null && !(e.work && e.work.k4 === 'eval')) { el.appendChild(TOK('m', 'lhs', null, 'lhs4')); el.appendChild(EQTOK()); el.appendChild(TOK(e.m === 'undef' ? 'undefined' : fracHtml(e.m), 'result', null, e.m === 'undef' ? 'undef4' : '')); fit(); return; }
        if (e.work) { renderWork(e.work); fit(); return; }
        el.appendChild(TOK('m', 'lhs', null, 'lhs4')); el.appendChild(EQTOK()); el.appendChild(TOK('?', 'q', null, 'q4'));
        fit(); return;
      }
      case 'line': {
        // The given line stays in the banner as a drop target for Same m and −1/m.
        const parts = [];
        if (e.q === 'parallel' || e.q === 'perp') parts.push(`<span class="lab4">Given</span> <span class="tok a4 r4-refm" data-role="refm" data-ref="Q">${XI('y')} = ${lineHtml(e.ref.m, e.ref.b)}</span>`);
        if (e.work) parts.push(templateToks(e, true));
        banner(parts.join(' · '));
        drawGraph(e.graph);
        if (e.work) { renderWork(e.work); if (wKind(e.work) !== 'a3') fit(); return; }
        templateToks(e, false); fit(); return;
      }
      case 'icept': {
        const f = e.found, ic = (v, t) => (v === null || v === undefined ? `<span class="slot4">?</span>` : t(fracHtml(v)));
        banner(`<span class="ic4">${XI('y')}-intercept ${ic(f.y, h => `(0, ${h})`)} · ${XI('x')}-intercept ${ic(f.x, h => `(${h}, 0)`)}</span>`);
        drawGraph(e.graph);
        if (e.work) { renderWork(e.work); fit(); return; }
        stdToks(e); fit(); return;
      }
    }
  }
  const lineHtml = (m, b) => lineTextOf(m, b).replace(/x/g, XI('x'));
  const stdText = e => `${fz(e.a) ? '' : (fIs(e.a, 1) ? '' : fIs(e.a, -1) ? MINUS : fracText(e.a)) + 'x'} ${e.b.n < 0 ? MINUS : '+'} ${fIs(fAbs(e.b), 1) ? '' : fracText(fAbs(e.b))}y = ${fracText(e.c)}`;
  const stdHtml = e => stdText(e).replace(/x/g, XI('x')).replace(/y/g, XI('y'));
  function stdToks(e) {
    const el = $('equation');
    el.appendChild(TOK(`${fIs(e.a, 1) ? '' : fIs(e.a, -1) ? MINUS : fracHtml(e.a)}${XI('x')}`, 'xt', null, 'std4'));
    el.appendChild(TOK(`${e.b.n < 0 ? MINUS : '+'} ${fIs(fAbs(e.b), 1) ? '' : fracHtml(fAbs(e.b))}${XI('y')}`, 'yt', null, 'std4'));
    el.appendChild(EQTOK());
    el.appendChild(TOK(fracHtml(e.c), 'num', null));
  }
  // Before an animation the equation is sized once, small enough for the result too (never resized mid-animation).
  function prefit(s, ns) {
    const a = active(s), b = active(ns);
    if (!a.k4 && b && !b.k4 && wKind(a) === wKind(b)) { render(s); (wKind(a) === 'a3' ? A3 : A2).prefit(a, b); return; }
    const px = () => parseFloat(getComputedStyle($('equation')).fontSize);
    render(ns); const after = px(); render(s); const before = px();
    if (before > after + 0.5) {
      const el = $('equation'), curSize = parseFloat(el.style.getPropertyValue('--eqSize')) || parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--eqSize')) || 56;
      el.style.setProperty('--eqSize', Math.floor(curSize * after / before) + 'px');
    }
  }
  addEventListener('resize', () => { if (cur && cur.act4 && !(typeof animating !== 'undefined' && animating) && A2.fitEq) A2.fitEq(); });

  // ---------------------------------------------------------------- the graph panel
  // A read-only grid drawn by code: { win: {x0, x1, y0, y1}, pts: [{x, y}], lines: [{m, b} | {x}], marks, labels }.
  // Points are drop targets (P0, P1) and so is a given line (G0). Lines and marks animate the first time
  // they appear in a question.
  function drawGraph(gs) {
    const el = graphEl();
    if (!gs) { el.innerHTML = ''; el.dataset.key = ''; el.classList.remove('show'); $('arena').classList.remove('g4'); return; }
    $('arena').classList.add('g4'); el.classList.add('show');
    const key = JSON.stringify(gs); if (el.dataset.key === key && el.firstChild) return;
    const qkey = JSON.stringify(gs.pts) + JSON.stringify(gs.win) + (gs.qid || '');
    if (el.dataset.q !== qkey || !el._seen) { el._seen = new Set(); el.dataset.q = qkey; }
    el.dataset.key = key;
    const W = 260, pad = 12, { x0, x1, y0, y1 } = gs.win, span = Math.max(x1 - x0, y1 - y0), s = (W - 2 * pad) / span;
    const cx = (x0 + x1) / 2, cy = (y0 + y1) / 2, vx0 = cx - span / 2, vx1 = cx + span / 2, vy0 = cy - span / 2, vy1 = cy + span / 2;
    const X = x => +(W / 2 + (x - cx) * s).toFixed(2), Y = y => +(W / 2 - (y - cy) * s).toFixed(2);
    const fresh = id => { const f = !el._seen.has(id); el._seen.add(id); return f ? ' anim' : ''; };
    const step = span <= 22 ? 1 : span <= 44 ? 2 : 5, lab = step * (span / step > 12 ? 5 : 2);
    let svg = `<svg viewBox="0 0 ${W} ${W}" role="img" aria-label="Graph">`;
    for (let x = Math.ceil(vx0 / step) * step; x <= vx1; x += step) svg += `<line class="gGrid" x1="${X(x)}" y1="${Y(vy0)}" x2="${X(x)}" y2="${Y(vy1)}"/>`;
    for (let y = Math.ceil(vy0 / step) * step; y <= vy1; y += step) svg += `<line class="gGrid" x1="${X(vx0)}" y1="${Y(y)}" x2="${X(vx1)}" y2="${Y(y)}"/>`;
    if (vy0 <= 0 && vy1 >= 0) svg += `<line class="gAxis" x1="${X(vx0)}" y1="${Y(0)}" x2="${X(vx1)}" y2="${Y(0)}"/><text class="gAxLab" x="${X(vx1) - 8}" y="${Y(0) - 5}">x</text>`;
    if (vx0 <= 0 && vx1 >= 0) svg += `<line class="gAxis" x1="${X(0)}" y1="${Y(vy0)}" x2="${X(0)}" y2="${Y(vy1)}"/><text class="gAxLab" x="${X(0) + 6}" y="${Y(vy1) + 12}">y</text>`;
    const ax = vy0 <= 0 && vy1 >= 0 ? 0 : vy0, ay = vx0 <= 0 && vx1 >= 0 ? 0 : vx0;
    for (let x = Math.ceil(vx0 / lab) * lab; x <= vx1; x += lab) if (x) svg += `<text class="gNum" x="${X(x)}" y="${Y(ax) + 11}">${numText(x)}</text>`;
    for (let y = Math.ceil(vy0 / lab) * lab; y <= vy1; y += lab) if (y) svg += `<text class="gNum" x="${X(ay) - 7}" y="${Y(y) + 3}" text-anchor="end">${numText(y)}</text>`;
    // lines, clipped to the window
    const seg = l => {
      if (l.x !== undefined) { const x = fv(l.x); return [[x, vy0], [x, vy1]]; }
      const m = fv(l.m), b = fv(l.b), pts = [];
      for (const x of [vx0, vx1]) { const y = m * x + b; if (y >= vy0 - 1e-9 && y <= vy1 + 1e-9) pts.push([x, y]); }
      if (m) for (const y of [vy0, vy1]) { const x = (y - b) / m; if (x > vx0 && x < vx1) pts.push([x, y]); }
      return pts.length >= 2 ? [pts[0], pts[1]] : null;
    };
    // Act 5: shaded half-planes { t: 'half', A, B, C, ge, cls } are the part of the view where
    // A·x + B·y ≥ C (ge) or ≤ C, clipped from the view square; { t: 'overlap', a, b } is where two of them meet.
    const halfPoly = h => {
      let poly = [[vx0, vy0], [vx1, vy0], [vx1, vy1], [vx0, vy1]];
      const f = ([x, y]) => (fv(h.A) * x + fv(h.B) * y - fv(h.C)) * (h.ge ? 1 : -1);
      const out = [];
      poly.forEach((p, i) => {
        const q = poly[(i + 1) % poly.length], fp = f(p), fq = f(q);
        if (fp >= 0) out.push(p);
        if ((fp >= 0) !== (fq >= 0)) { const t = fp / (fp - fq); out.push([p[0] + (q[0] - p[0]) * t, p[1] + (q[1] - p[1]) * t]); }
      });
      return out.map(([x, y]) => `${X(x)},${Y(y)}`).join(' ');
    };
    const shades = gs.marks.filter(mk => mk.t === 'half'), overlaps = gs.marks.filter(mk => mk.t === 'overlap');
    shades.forEach((h, i) => { svg += `<polygon class="gHalf ${h.cls || ''}${fresh('H' + JSON.stringify(h))}" points="${halfPoly(h)}"/>`; });
    overlaps.forEach((o, i) => {
      svg += `<clipPath id="gClip${i}"><polygon points="${halfPoly(o.a)}"/></clipPath>`;
      svg += `<polygon class="gOverlap${fresh('O' + JSON.stringify(o))}" clip-path="url(#gClip${i})" points="${halfPoly(o.b)}"/>`;
    });
    const labsAt = [];
    gs.lines.forEach((l, i) => {
      const sg = seg(l); if (!sg) return;
      const cls = (l.res ? 'gRes' : l.ref ? 'gRef' : 'gLine') + (l.cls ? ' ' + l.cls : '') + (l.dash ? ' gDash' : '');
      svg += `<line class="${cls}${fresh('L' + JSON.stringify(l))}" pathLength="1" x1="${X(sg[0][0])}" y1="${Y(sg[0][1])}" x2="${X(sg[1][0])}" y2="${Y(sg[1][1])}"/>`;
      if (l.ref) svg += `<line class="gtarget gLineHit" data-ref="${l.tref || 'G' + i}" data-role="gline" x1="${X(sg[0][0])}" y1="${Y(sg[0][1])}" x2="${X(sg[1][0])}" y2="${Y(sg[1][1])}"/>`;
      if (l.lab) {   // a small tag near the end of the line that is furthest right, so lines can be told apart
        // Playtest fix: two lines ending close together got their tags on top of each other, so a tag
        // that would land on an earlier one moves to its line's other end.
        const first = sg[0][0] > sg[1][0] || (sg[0][0] === sg[1][0] && sg[0][1] > sg[1][1]) ? 0 : 1;
        const at = e => [Math.max(16, Math.min(X(e[0]), W - 14)), Math.max(14, Math.min(W - 6, Y(e[1]) + (Y(e[1]) < 20 ? 12 : -4)))];
        const tries = [at(sg[first]), at(sg[1 - first])];
        const [lx, ly] = tries.find(([x, y]) => labsAt.every(([px, py]) => Math.hypot(px - x, py - y) > 20)) || tries[0];
        labsAt.push([lx, ly]);
        svg += `<text class="gLineLab ${l.cls || ''}" x="${lx}" y="${ly}" text-anchor="${lx < W / 2 ? 'start' : 'end'}">${l.lab}</text>`;
      }
    });
    // marks: the rise/run triangle and intercepts
    for (const mk of gs.marks) {
      const id = 'M' + JSON.stringify(mk), an = fresh(id);
      if (mk.t === 'tri') {
        const ax_ = X(fv(mk.a.x)), ay_ = Y(fv(mk.a.y)), bx = X(fv(mk.b.x)), by = Y(fv(mk.b.y));
        const run = fSub(mk.b.x, mk.a.x), rise = fSub(mk.b.y, mk.a.y);
        svg += `<line class="gRun${an}" pathLength="1" x1="${ax_}" y1="${ay_}" x2="${bx}" y2="${ay_}"/>`;
        svg += `<line class="gRise${an}" pathLength="1" x1="${bx}" y1="${ay_}" x2="${bx}" y2="${by}" style="animation-delay:.5s"/>`;
        const below = by < ay_;
        svg += `<text class="gRunLab${an}" x="${(ax_ + bx) / 2}" y="${ay_ + (below ? 14 : -6)}">run ${fracText(run)}</text>`;
        svg += `<text class="gRiseLab${an}" x="${bx + (bx >= ax_ ? 5 : -5)}" y="${(ay_ + by) / 2 + 4}" text-anchor="${bx >= ax_ ? 'start' : 'end'}">rise ${fracText(rise)}</text>`;
      } else if (mk.t === 'ic') svg += `<circle class="gIc${an}" cx="${X(fv(mk.x))}" cy="${Y(fv(mk.y))}" r="7"/>`;
      else if (mk.t === 'dot') {   // Act 5: the crossing point of a system, or a point being tested
        const dx = X(fv(mk.x)), dy = Y(fv(mk.y));
        svg += `<circle class="gDot ${mk.cls || ''}${an}" cx="${dx}" cy="${dy}" r="6"/>`;
        if (mk.lab) { const right = dx < W - 70; svg += `<text class="gPtLab${an}" x="${dx + (right ? 9 : -9)}" y="${dy - 8}" text-anchor="${right ? 'start' : 'end'}">${mk.lab}</text>`; }
      }
    }
    gs.pts.forEach((p, i) => {
      const px = X(fv(p.x)), py = Y(fv(p.y));
      svg += `<circle class="gPt${p.cls ? ' ' + p.cls : ''}" cx="${px}" cy="${py}" r="5"/>`;
      if (gs.labels) { const right = px < W - 60; svg += `<text class="gPtLab" x="${px + (right ? 8 : -8)}" y="${py - 7}" text-anchor="${right ? 'start' : 'end'}">${ptText(p)}</text>`; }
      if (gs.targets !== false) svg += `<circle class="gtarget gpt" data-ref="P${i}" data-role="point" cx="${px}" cy="${py}" r="16"/>`;
    });
    el.innerHTML = svg + '</svg>';
  }
  // A window that fits every point (and the origin) with one square of margin.
  function windowFor(xs, ys) {
    const allx = [...xs.map(fv), 0], ally = [...ys.map(fv), 0];
    const x0 = Math.floor(Math.min(...allx)) - 1, x1 = Math.ceil(Math.max(...allx)) + 1, y0 = Math.floor(Math.min(...ally)) - 1, y1 = Math.ceil(Math.max(...ally)) + 1;
    const w = Math.max(x1 - x0, y1 - y0, 8);
    const cx = (x0 + x1) / 2, cy = (y0 + y1) / 2;
    return { x0: Math.floor(cx - w / 2), x1: Math.ceil(cx + w / 2), y0: Math.floor(cy - w / 2), y1: Math.ceil(cy + w / 2) };
  }

  // ================================================================ animations
  // Timing follows the game's pattern: what's written fades in fast, hold() (scaled by animation speed),
  // the calculation runs fast (quick(), fixed), the result shows, hold().
  const eqq = sel => $('equation').querySelector(sel);
  const tokRef = ref => eqq(`.tok[data-ref="${ref}"]`) || document.querySelector(`#a4top .tok[data-ref="${ref}"], #graph [data-ref="${ref}"]`);
  const FAM_CLASS = { addsub: 'fam-addsub', muldiv: 'fam-muldiv', pow: 'fam-pow', paren: 'fam-paren' };
  async function animEval(c, s, ns, ref) {
    if (c.op === 'plug') return animPlug(c, s);
    if (c.op === 'plugf') return animMachine(c, s, ns);
    if (c.op === 'undef') return animUndef(s, ref);
    const p = pathOfRef(ref);
    let node = at(s.tree, p), wrapPath = p;
    if (c.op === 'paren') node = node.a;
    else if (p && at(s.tree, p.slice(0, -1)).t === 'par') wrapPath = p.slice(0, -1);   // the brackets go too
    const val = evalNode(node), fam = FAMILY[node.t];
    const wrap = eqq(`.n4[data-node="${wrapPath}"]`);
    if (!wrap) return;
    const toks = [...wrap.querySelectorAll('.tok')];
    const a = node.a.v, b = node.b ? node.b.v : null;
    const how = node.t === 'pow' ? Array(node.e).fill(paren(a)).join(` ${TIMES} `) : node.t === 'div' ? `${fracText(a)} ${DIV} ${paren(b)}` : `${fracText(a)} ${{ add: '+', sub: MINUS, mul: TIMES }[node.t]} ${paren(b)}`;
    const words = { add: 'Add', sub: 'Subtract', mul: 'Multiply', div: 'Divide', pow: node.e === 3 ? 'Cube' : 'Square' }[node.t];
    caption(c.op === 'paren' ? `Parentheses first: ${how}` : node.t === 'pow' ? `${words}: the base multiplies itself, ${how}` : `${words}: ${how}`);
    mark(toks, 'hot4'); mark(toks, FAM_CLASS[fam]);
    const n = note(`${how} = ${fracHtml(val)}`, toks); n.classList.add(FAM_CLASS[c.op === 'paren' ? 'paren' : fam]);
    await quick(150); await hold();
    mark(toks, 'melt4');
    await quick(320);
    dropNote(n);
    wrap.className = 'n4'; wrap.innerHTML = '';
    wrap.appendChild(TOK(fracHtml(val), 'num', null, 'pop'));
    caption(`${how} = ${fracText(val)}`);
    await quick(250); await hold();
  }
  async function animPlug(c, s) {
    const vars = [...$('equation').querySelectorAll('.tok.r4-var')];
    const neg = c.v.n < 0;
    caption(`Plug in ${s.vn} = ${fracText(c.v)}: every ${s.vn} becomes ${fracText(c.v)}${neg ? ', in brackets because it\'s negative' : ''}`);
    await quick(150);
    for (const v of vars) { v.innerHTML = neg || c.v.d > 1 ? `(${fracHtml(c.v)})` : fracHtml(c.v); v.classList.remove('var'); kickClass(v, 'drop4'); await quick(120); }
    if (neg && hasPowVar(s.tree)) caption(`(${fracText(c.v)})² = ${fracText(fMul(c.v, c.v))}: the brackets square the minus sign too`);
    await hold();
  }
  // Stage 15: a function machine appears, the input drops in the top, the rule runs, and the rule with the
  // input in place of x slides out.
  async function animMachine(c, s, ns) {
    const callTok = eqq('.tok.r4-call'); if (!callTok) return;
    const eq = $('equation'), r = callTok.getBoundingClientRect(), q = eq.getBoundingClientRect();
    const m = document.createElement('div'); m.className = 'fm4';
    m.innerHTML = `<div class="fm4in">${fracHtml(c.v)}</div><div class="fm4box"><b>${s.fn.name}</b><span class="fm4rule">${treeHtml(s.fn.rule)}</span><span class="fm4gear"></span></div><div class="fm4out">${treeHtml(ns.tree)}</div>`;
    m.style.left = (r.left + r.width / 2 - q.left) + 'px'; m.style.top = (r.top - q.top) + 'px';
    eq.appendChild(m);
    caption(`${treeText(s.tree)}: ${fracText(c.v)} goes into ${s.fn.name}`);
    await quick(150); m.classList.add('in'); await quick(500);
    m.classList.add('run'); caption(`The rule runs with ${fracText(c.v)} in place of ${s.fn.vn}`); await quick(600);
    m.classList.add('out'); caption(`Out comes ${treeText(ns.tree)}: now work it out`); await quick(400);
    await hold();
    m.remove();
  }
  async function animWriteOut(c, s, ns) {
    const t = eqq('.tok.r4-fx'); if (!t) return;
    caption(`${s.fn.name}(${s.fn.vn}) is a name for its rule: write out ${treeText(s.fn.rule)}`);
    await quick(150); await hold();
    t.innerHTML = treeHtml(s.fn.rule); kickClass(t, 'unroll4');
    await quick(450); await hold();
  }
  async function animUndef(s, ref) {
    const wrap = eqq(`.n4[data-node="${pathOfRef(ref)}"]`) || $('equation');
    caption('The run is 0, and nothing can be divided by 0: the line is vertical, so its slope is undefined');
    wrap.classList.add('crack4'); kickClass($('equation'), 'shake');
    await quick(700); await hold();
  }
  // Formula moves, written under the terms like Act 2's: + and − under the like term on each side,
  // × as a stamp under every term, ÷ as a fraction bar under each whole side.
  async function animFormula(c, s, ns, ref) {
    const sideToks = sd => [...$('equation').querySelectorAll(`.tok.f4t[data-side="${sd}"]`)];
    if (c.op === 'dist') {
      const tk = tokRef(ref), g = s[ref[0]][+ref.slice(1)];
      const prods = g.items.map(o => tMul(o, g.m));
      caption(`Distribute: ${g.items.map(o => `${signedT(g.m)} ${TIMES} ${signedT(o)} = ${signedT(tMul(o, g.m))}`).join(',  ')}`);
      mark([tk], 'hot4'); const n = note(prods.map((o, j) => fTermStr(o, j === 0, true, s.v)).join(' '), [tk]);
      await quick(150); await hold();
      dropNote(n); tk.innerHTML = prods.map((o, j) => fTermStr(o, j === 0 && ref.endsWith('0'), true, s.v)).join(' '); kickClass(tk, 'pop');
      await hold(); return;
    }
    if (c.op === 'comb') {
      const sd = ref[0], key = keyT(s[sd][+ref.slice(1)]), idx = s[sd].map((o, j) => (!o.g && keyT(o) === key ? j : -1)).filter(j => j >= 0);
      const toks = idx.map(j => tokRef(sd + j)); let k = F(0); idx.forEach(j => { k = fAdd(k, s[sd][j].k); });
      caption(`Like terms: ${idx.map((j, i) => fTermStr(s[sd][j], i === 0, false, s.v)).join(' ')} = ${fz(k) ? '0' : signedT({ ...s[sd][idx[0]], k })}`);
      mark(toks, 'hot4'); await quick(150); await hold();
      toks.slice(1).forEach(t => t.classList.add('melt4')); await quick(350);
      toks.slice(1).forEach(t => t.remove());
      if (fz(k)) toks[0].classList.add('melt4'); else { toks[0].innerHTML = fTermStr({ ...s[sd][idx[0]], k }, idx[0] === 0, true, s.v); kickClass(toks[0], 'pop'); }
      await hold(); return;
    }
    caption(fCardText(c));
    const notes = [];
    if (c.op === '/') for (const sd of ['L', 'R']) notes.push(note(paren(F(c.t.k.n, 1)) === '' ? '' : tBody({ ...c.t, k: c.t.k }, s.v, true).replace(/^/, c.t.k.n < 0 ? MINUS : ''), sideToks(sd), { bar: true }));
    else if (c.op === '*') for (const t of $('equation').querySelectorAll('.tok.f4t')) notes.push(note(TIMES + ' ' + (c.t.k.n < 0 ? `(${signedT(c.t)})` : tBody(c.t, s.v, true)), [t]));
    else {
      const t = { ...c.t, k: c.op === '+' ? c.t.k : fNeg(c.t.k) };
      for (const sd of ['L', 'R']) {
        const side = s[sd], i = side.findIndex(o => !o.g && keyT(o) === keyT(t)), tk = i >= 0 ? tokRef(sd + i) : sideToks(sd).slice(-1)[0];
        notes.push(note(fTermStr(t, false, true, s.v), [tk]));
        if (i >= 0 && fz(fAdd(side[i].k, t.k))) { notes[notes.length - 1]._cancel = tk; }
      }
    }
    await quick(150); await hold();
    const cancels = notes.filter(n => n._cancel);
    if (cancels.length) { cancels.forEach(n => mark([n, n._cancel], 'cancel')); await quick(350); cancels.forEach(n => n._cancel.classList.add('melt4')); }
    notes.forEach(n => n.classList.add('merge'));
    await quick(250);
    // the new terms, side by side
    for (const sd of ['L', 'R']) {
      const toks = sideToks(sd), nside = ns[sd];
      if (toks.length === nside.length) toks.forEach((tk, j) => { const h = fTermStr(nside[j], j === 0, true, s.v); if (tk.innerHTML !== h) { tk.innerHTML = h; kickClass(tk, 'pop'); } });
    }
    notes.forEach(dropNote);
    await hold();
  }
  // Stage 16: rise over run. The triangle draws on the graph and the fraction is written out.
  async function animRise(c, s, ns, ref) {
    const w = active(ns), a = w.from, b = w.to;
    caption(`Rise over run from ${ptText(a)} to ${ptText(b)}: up ${fracText(fSub(b.y, a.y))}, across ${fracText(fSub(b.x, a.x))}`);
    drawGraph(ns.graph);
    await quick(1100);
    $('equation').innerHTML = ''; renderEval(w); $('equation').classList.add('a2'); if (A2.fitEq) A2.fitEq();
    [...$('equation').querySelectorAll('.tok')].forEach(t => kickClass(t, 'pop'));
    caption(`m = (change in y) / (change in x) = (${fracText(b.y)} ${MINUS} ${paren(a.y)}) / (${fracText(b.x)} ${MINUS} ${paren(a.x)})`);
    await quick(300); await hold();
  }
  async function animRead(c, s, ns, ref) {
    const t = tokRef(ref); const m = ns.m;
    caption(`In y = mx + b the number in front of x is the slope: m = ${fracText(m)}`);
    if (t) { mark([t], 'hot4'); const n = note(`m = ${fracHtml(m)}`, [t]); n.classList.add('lift4'); await quick(150); await hold(); dropNote(n); }
    await quick(200);
  }
  async function animSameSlope(c, s, ns) {
    const t = document.querySelector('#a4top .r4-refm');
    const m = s.ref.m, nm = ns.m;
    caption(c.op === 'same' ? `Parallel lines go the same way: same slope, m = ${fracText(nm)}` : `Perpendicular: flip ${fracText(m)} over and change its sign, m = ${fracText(nm)}`);
    if (t) mark([t], 'hot4');
    const slot = eqq('.tok.r4-tm');
    if (slot) { const n = note(c.op === 'same' ? fracHtml(m) : `${fracHtml(m)} → ${fracHtml(nm)}`, [slot]); n.classList.add(c.op === 'perp' ? 'flip4' : 'lift4'); await quick(150); await hold(); dropNote(n); }
    else { await quick(150); await hold(); }
  }
  // The point's x and y fly from the graph into y = mx + b, then the arithmetic is done.
  async function animPlugPoint(c, s, ns, ref) {
    const p = s.pts[ref === 'P1' ? 1 : 0], dot = document.querySelector(`#graph [data-ref="${ref}"]`);
    const ty = eqq('.tok.r4-ty'), tm = eqq('.tok.r4-tm');
    caption(`Plug ${ptText(p)} into y = mx + b: y = ${fracText(p.y)} and x = ${fracText(p.x)}`);
    if (dot && ty && tm) {
      const fly = async (html, to) => {
        const from = dot.getBoundingClientRect(), dest = to.getBoundingClientRect();
        const chip = document.createElement('div'); chip.className = 'fly4'; chip.innerHTML = html;
        chip.style.left = (from.left + from.width / 2) + 'px'; chip.style.top = (from.top + from.height / 2) + 'px';
        document.body.appendChild(chip); void chip.offsetWidth;
        chip.style.transform = `translate(${dest.left + dest.width / 2 - from.left - from.width / 2}px, ${dest.top + dest.height / 2 - from.top - from.height / 2}px)`;
        await quick(450); chip.remove();
      };
      await fly(fracHtml(p.y), ty); ty.innerHTML = fracHtml(p.y); kickClass(ty, 'pop');
      await fly(fracHtml(p.x), tm); tm.innerHTML = `${fracHtml(s.m)}(${fracHtml(p.x)})`; kickClass(tm, 'pop');
      await quick(150); await hold();
      const mx = fMul(s.m, p.x); tm.innerHTML = fracHtml(mx); kickClass(tm, 'pop');
      caption(`${fracText(s.m)} ${TIMES} ${paren(p.x)} = ${fracText(mx)}. Now solve for b`);
      await quick(200); await hold();
    } else { await quick(150); await hold(); }
  }
  async function animPtSlope(c, s, ns, ref) {
    const p = s.pts[ref === 'P1' ? 1 : 0];
    caption(`Point-slope form: y ${MINUS} y₁ = m(x ${MINUS} x₁), with the point ${ptText(p)} and m = ${fracText(s.m)}`);
    const el = $('equation'); el.innerHTML = '';
    el.appendChild(TOK(`y ${MINUS} ${paren(p.y)} = ${fracHtml(s.m)}(x ${MINUS} ${paren(p.x)})`, 'tmp', null, 'pop'));
    await quick(150); await hold();
  }
  async function animWrite(c, s, ns) {
    caption(`m = ${fracText(s.m)} and b = ${fracText(s.b)}: y = ${lineTextOf(s.m, s.b)}`);
    for (const t of $('equation').querySelectorAll('.tok.tmpl')) kickClass(t, 'pop');
    drawGraph(ns.graph || (ns.k4 ? ns.graph : null));
    await quick(900); await hold();
  }
  async function animSetZero(c, s, ns) {
    const which = c.op === 'setx' ? 'x' : 'y', t = eqq(which === 'x' ? '.tok.r4-xt' : '.tok.r4-yt');
    caption(`On the ${which === 'x' ? 'y' : 'x'}-axis, ${which} = 0: the ${which}-term vanishes`);
    if (t) { const n = note(`${which} = 0`, [t]); n.classList.add('stamp4'); await quick(150); await hold(); mark([t, n], 'cancel'); await quick(300); t.classList.add('melt4'); dropNote(n); await quick(300); }
    await hold();
  }
  function animFor(card) {
    return async (c, s, ns, ref) => {
      const a = active(s);
      // the move finishes a piece of work: play that work's animation, then show what it led to
      if (a !== s && !OWN.includes(c.op) && !c.f4 && !a.k4) { await (wKind(a) === 'a3' ? A3.animFor() : A2.animFor(c))(c, a, active(ns) === a ? a : wApply(a, c, ref), ref); return; }
      if (a.k4 === 'formula' && c.f4) { await animFormula(c, a, fApply(a, c, ref), ref); return; }
      if (a.k4 === 'eval' && ['plug', 'plugf', 'paren', 'pow', 'muldiv', 'addsub', 'undef'].includes(c.op)) { await animEval(c, a, evalApply(a, c, ref), ref); return; }
      switch (c.op) {
        case 'writeout': return animWriteOut(c, s, ns);
        case 'rise': return animRise(c, s, ns, ref);
        case 'read': return animRead(c, s, ns, ref);
        case 'same': case 'perp': return animSameSlope(c, s, ns);
        case 'plugpt': return animPlugPoint(c, s, ns, ref);
        case 'ptslope': return animPtSlope(c, s, ns, ref);
        case 'write': return animWrite(c, s, ns);
        case 'setx': case 'sety': return animSetZero(c, s, ns);
      }
    };
  }

  // ================================================================ generators
  const RANGE = [6, 10, 15, 15];
  const COEF = [5, 9, 12, 15];
  const SIMPLE_FRACS = [[1, 2], [1, 3], [2, 3], [3, 2], [1, 4], [3, 4]];
  const sgn = () => (Math.random() < 0.5 ? -1 : 1);
  // Values to plug in. Every level gets negative values (and the 'negpow' case always is one); Expert
  // sometimes plugs in a fraction.
  function evalValue(L, neg) {
    if (L === 3 && Math.random() < 0.25) { const [p, q] = pick([[1, 2], [3, 2], [1, 3], [2, 3]]); return F((neg ? -1 : 1) * p, q); }
    const v = rand(1, [5, 6, 9, 12][L]);
    return F(neg ? -v : v);
  }
  const EVAL_CASES = ['lin', 'sq', 'paren', 'parsq', 'rev', 'negsq', 'frac', 'quad', 'negpow'];
  function evalShape(shape, L, x, C) {
    const a = rand(2, C), b = rand(1, C) * sgn(), c = rand(1, C);
    switch (shape) {
      case 'lin': return pm(mul(num(a), vr()), b);
      case 'sq': return pm(mul(num(rand(2, Math.min(C, 6))), pw(vr())), b);
      case 'paren': return mul(num(a), par(pm(vr(), b)));
      case 'parsq': { const k = rand(1, 3); const inner = pw(par(pm(vr(), nonZero(-6, 6)))); return k === 1 ? inner : mul(num(k), inner); }
      case 'rev': return sub(num(rand(5, C + 8)), mul(num(a), vr()));
      case 'negsq': return add(ng(pw(vr())), mul(num(rand(2, Math.min(C, 8))), vr()));
      case 'frac': {
        const den = rand(2, 5), aa = rand(1, 4);
        // keep (a·x + b) a multiple of den below Expert
        let bb = rand(1, 9) * sgn();
        if (L < 3 && x.d === 1) { const top = aa * x.n + bb, r = ((top % den) + den) % den; bb -= r; if (bb === 0) bb = den; }
        return dv(pm(aa === 1 ? vr() : mul(num(aa), vr()), bb), num(den));
      }
      case 'quad': return pm(sub(pw(vr()), mul(num(rand(2, Math.min(C, 7))), vr())), rand(1, C) * sgn());
    }
    return vr();
  }
  // Extra steps: one more term (Normal), then nested parentheses (Hard), then more (Expert).
  function addEvalSteps(tree, k, L) {
    // Playtest fix: steps used to pile up loose numbers (+ 3 − 1 − 1) and wrap a bare product in brackets
    // (3(15(x + 14))). A loose number is now added at most once, and only a sum or difference gets nested.
    let termed = false;
    for (let i = 0; i < k; i++) {
      const opts = termed ? ['xterm'] : ['xterm', 'term'];
      if (L >= 2 && i === 0 && (tree.t === 'add' || tree.t === 'sub')) opts.push('nest', 'nest');
      const o = pick(opts);
      if (o === 'term') termed = true;
      if (o === 'term') tree = pm(tree, nonZero(-9, 9));
      else if (o === 'xterm') tree = pmT(tree, mul(num(rand(2, 6)), vr()), Math.random() < 0.5);
      else tree = pm(mul(num(rand(2, 4)), par(tree)), nonZero(-9, 9));
    }
    return tree;
  }
  function genEval(cs, tut = isTutorial()) {
    const L = lvl(tut), C = COEF[L], steps = tut ? 0 : difficulty.steps;
    cs = cs || pick(EVAL_CASES);
    for (let i = 0; i < 300; i++) {
      const shape = cs === 'negpow' ? pick(['sq', 'parsq', 'negsq', 'quad']) : cs;
      const neg = cs === 'negpow' || (!tut && Math.random() < (L ? 0.45 : 0.25));
      const x = tut ? F(rand(2, 5)) : evalValue(L, neg);
      let tree = evalShape(shape, L, x, tut ? 4 : C);
      if (steps) tree = addEvalSteps(tree, steps, L);
      const res = evaluate(tree, 'x', x);
      if (!res) continue;
      if (L < 3 && !isInt(res)) continue;
      if (!isInt(res) && res.d > 12) continue;   // playtest fix: Expert gave answers like 1127/2
      if (Math.abs(fv(res)) > [60, 150, 300, 300][L]) continue;
      if (opCount(tree) > 9) continue;
      return { fn: { ...evalState(tree, x, 'x'), skill: 'evalx' }, enemy: 'plugger' };
    }
    return { fn: { ...evalState(pm(mul(num(3), vr()), 4), F(2), 'x'), skill: 'evalx' }, enemy: 'plugger' };
  }

  // Stage 15. Rules: 2x + 3, 3(x − 2), 9 − 2x, x/4 + 1 (and a·x² + c, x² + bx for outputs).
  const FUNC_CASES = ['out', 'in', 'outsq', 'letter', 'ineq'];
  function linRule(shape, vn, C, steps) {
    const a = rand(2, C), b = rand(1, C) * sgn();
    let r;
    switch (shape) {
      case 'lin': r = pm(mul(num(a), vr(vn)), b); break;
      case 'paren': r = mul(num(a), par(pm(vr(vn), b))); break;
      case 'rev': r = sub(num(rand(3, C + 6)), mul(num(a), vr(vn))); break;
      case 'fracx': r = pm(dv(vr(vn), num(rand(2, 5))), b); break;
    }
    if (steps && shape === 'paren') r = pm(r, nonZero(-9, 9));
    return r;
  }
  function genFunc(cs, tut = isTutorial()) {
    const L = lvl(tut), C = tut ? 5 : COEF[L], steps = tut ? 0 : difficulty.steps;
    cs = cs || pick(FUNC_CASES);
    const name = cs === 'letter' ? pick(['g', 'h']) : pick(['f', 'f', 'g']), vn = cs === 'letter' ? pick(['t', 'n', 'k']) : 'x';
    const q = cs === 'letter' ? pick(['out', 'in']) : cs === 'outsq' ? 'out' : cs;
    for (let i = 0; i < 300; i++) {
      if (q === 'out') {
        const sq = cs === 'outsq';
        let rule = sq ? (Math.random() < 0.5 ? pm(mul(num(rand(2, Math.min(C, 5))), pw(vr(vn))), rand(1, C) * sgn()) : add(pw(vr(vn)), mul(num(rand(2, Math.min(C, 6))), vr(vn))))
          : linRule(pick(['lin', 'paren', 'rev']), vn, C, steps);
        if (!sq && steps >= 2) rule = pmT(rule, mul(num(rand(2, 4)), vr(vn)), Math.random() < 0.5);
        const input = tut ? F(rand(2, 5)) : evalValue(L, sq ? Math.random() < 0.5 : Math.random() < 0.35);
        const res = evaluate(rule, vn, input);
        if (!res || (L < 3 && !isInt(res)) || Math.abs(fv(res)) > [60, 150, 400, 800][L]) continue;
        const fn = { name, vn, rule };
        return { fn: { ...evalState(call(name, input), null, vn, { fn, lhs: `${name}(${fracText(input)})` }), skill: 'funcs' }, enemy: 'boxmimic' };
      }
      // input questions: f(x) = 11, or f(x) > 7
      const shape = cs === 'ineq' ? pick(['lin', 'rev', 'paren']) : pick(tut ? ['lin'] : ['lin', 'paren', 'rev', 'fracx']);
      const rule = linRule(shape, vn, C, steps);
      let x0 = F(rand(tut ? 1 : -6, tut ? 6 : [6, 9, 12, 12][L]));
      if (!tut && Math.random() < (L === 3 ? 0.35 : 0.15)) x0 = F(rand(1, 7) * sgn(), 2);
      const rhs = evaluate(rule, vn, x0);
      if (!rhs || !isInt(rhs) || fz(x0)) continue;
      const rel = cs === 'ineq' ? pick(['<', '≤', '>', '≥']) : '=';
      const st = { k4: 'fin', fn: { name, vn, rule }, rel, rhs, work: null, skill: 'funcs' };
      // the answer must still come out of the engine as x0 (Act 2 solves linear rules exactly)
      return { fn: st, enemy: 'boxmimic' };
    }
    return genFunc('out', true);
  }

  // Stage 16
  const SLOPE_CASES = ['pts-pos', 'pts-neg', 'graph', 'slopeint', 'standard', 'zero', 'undef'];
  function slopeValue(L, sign, tut) {
    if (!tut && Math.random() < [0.25, 0.3, 0.4, 0.5][L]) { const [p, q] = pick(L >= 3 ? [...SIMPLE_FRACS, [5, 3], [4, 5], [5, 2]] : SIMPLE_FRACS); return F(sign * p, q); }
    return F(sign * rand(1, [3, 4, 5, 6][L]));
  }
  // Two points on a line with slope m (null: vertical), inside ±R.
  function pointsFor(m, R, L) {
    for (let i = 0; i < 400; i++) {
      const x1 = rand(-R, R), y1 = rand(-R, R);
      let x2, y2;
      if (m === null) { x2 = x1; y2 = rand(-R, R); if (y2 === y1) continue; }
      else {
        const run = m.d * rand(1, Math.max(1, Math.floor(R / m.d))) * sgn();
        x2 = x1 + run; y2 = y1 + fv(fMul(m, F(run)));
        if (!Number.isInteger(y2) || Math.abs(x2) > R || Math.abs(y2) > R || x2 === x1) continue;
      }
      // spread across the quadrants: not both points in one corner too often
      return [{ x: F(x1), y: F(y1) }, { x: F(x2), y: F(y2) }];
    }
    return [{ x: F(1), y: F(2) }, { x: F(4), y: F(8) }];
  }
  function graphFor(pts, extraXs = [], extraYs = [], lines = [], labels = true) {
    return { win: windowFor([...pts.map(p => p.x), ...extraXs], [...pts.map(p => p.y), ...extraYs]), pts, lines, marks: [], labels };
  }
  const labelled = (L, tut) => tut || (L <= 1 && Math.random() < 0.7);
  function genSlope(cs, tut = isTutorial()) {
    const L = lvl(tut), R = tut ? 6 : RANGE[L];
    cs = cs || pick(SLOPE_CASES);
    const base = { k4: 'slope', skill: 'slope', m: null, work: null };
    if (cs === 'slopeint' || cs === 'standard') {
      if (cs === 'slopeint') {
        const m = slopeValue(L, sgn(), tut), b = F(nonZero(-R + 1, R - 1));
        const work = { k4: 'formula', L: [T(1, 'y')], R: Math.random() < 0.25 && !tut ? [T(b), T(m, 'x')] : [T(m, 'x'), T(b)], v: 'y' };
        const g = graphFor([], [F(0)], [b], [{ m, b }], false); g.targets = false;
        return { fn: { ...base, src: 'slopeint', work, graph: g }, enemy: 'slopeling' };
      }
      for (let i = 0; i < 200; i++) {
        const a = nonZero(-[4, 6, 9, 12][L], [4, 6, 9, 12][L]), b = nonZero(-[4, 6, 9, 12][L], [4, 6, 9, 12][L]);
        if (Math.abs(b) === 1 || gcd(a, b) !== 1) continue;
        const c = b * rand(-4, 4) || b * 2;
        const work = { k4: 'formula', L: [T(a, 'x'), T(b, 'y')], R: [T(c)], v: 'y' };
        const m = F(-a, b), bb = F(c, b);
        if (Math.abs(fv(bb)) > R) continue;
        const g = graphFor([], [F(0)], [bb], [{ m, b: bb }], false); g.targets = false;
        return { fn: { ...base, src: 'standard', work, graph: g }, enemy: 'slopeling' };
      }
    }
    let m;
    if (cs === 'zero') m = F(0);
    else if (cs === 'undef') m = null;
    else m = slopeValue(L, cs === 'pts-neg' ? -1 : cs === 'pts-pos' ? 1 : sgn(), tut);
    const pts = pointsFor(m, R, L);
    const lab = cs === 'graph' ? false : labelled(L, tut);
    const lines = cs === 'graph' ? [m === null ? { x: pts[0].x } : { m, b: fSub(pts[0].y, fMul(m, pts[0].x)) }] : [];
    return { fn: { ...base, src: cs === 'graph' ? 'graph' : 'pts', pts, graph: graphFor(pts, [], [], lines, lab) }, enemy: 'slopeling' };
  }

  // Stage 17
  const LINE_CASES = ['slopept', 'twopts', 'icept', 'ptslope', 'parallel', 'perp'];
  function niceLine(L, tut) {   // a slope and an intercept whose points are easy to plot
    for (let i = 0; i < 200; i++) {
      const m = slopeValue(L, sgn(), tut);
      const b = L >= 3 && !tut && Math.random() < 0.3 ? F(rand(1, 9) * sgn(), 2) : F(rand(-5, 5));
      return { m, b };
    }
  }
  function pointOn(m, b, R) {
    for (let i = 0; i < 200; i++) {
      const x = m.d * rand(1, Math.max(1, Math.floor(R / m.d))) * sgn(), y = fAdd(fMul(m, F(x)), b);
      if (Math.abs(fv(y)) > R || x === 0) continue;
      return { x: F(x), y };
    }
    return { x: F(m.d), y: fAdd(fMul(m, F(m.d)), b) };
  }
  function genLine(cs, tut = isTutorial(), then = null) {
    const L = lvl(tut), R = tut ? 6 : RANGE[L];
    cs = cs || pick(LINE_CASES);
    const base = { k4: 'line', skill: 'lines', q: cs, m: null, b: null, work: null, done: false, then };
    const lab = labelled(L, tut);
    if (cs === 'icept') {
      for (let i = 0; i < 200; i++) {
        const p = nonZero(-R, R), q = nonZero(-R, R);       // the intercepts (p, 0) and (0, q)
        let a = q, b = p, c = p * q; const g = gcd(gcd(a, b), c); a /= g; b /= g; c /= g;
        if (a < 0) { a = -a; b = -b; c = -c; }
        if (Math.abs(a) === Math.abs(b) && Math.random() < 0.7) continue;
        let A = F(a), B = F(b), Cc = F(c);
        if (L >= 3 && !tut && Math.random() < 0.4) { Cc = fAdd(Cc, F(1)); if (fz(Cc)) continue; }   // fraction intercepts on Expert
        const xi = fDiv(Cc, A), yi = fDiv(Cc, B);
        const gr = graphFor([], [xi], [yi], [], lab); gr.targets = false;
        return { fn: { k4: 'icept', skill: 'lines', a: A, b: B, c: Cc, found: { x: null, y: null }, work: null, which: null, graph: gr, then }, enemy: 'liner' };
      }
    }
    const ln = niceLine(L, tut);
    if (cs === 'twopts') {
      const p1 = pointOn(ln.m, ln.b, R); let p2;
      for (let i = 0; i < 50; i++) { p2 = pointOn(ln.m, ln.b, R); if (!fEq(p2.x, p1.x)) break; }
      if (fEq(p2.x, p1.x)) p2 = { x: fAdd(p1.x, F(ln.m.d)), y: fAdd(p1.y, F(ln.m.n)) };
      const pts = [p1, p2];
      return { fn: { ...base, pts, graph: graphFor(pts, [], [], [], lab) }, enemy: 'liner' };
    }
    if (cs === 'parallel' || cs === 'perp') {
      let m = ln.m;
      if (cs === 'perp') { for (let i = 0; i < 20 && Math.abs(m.n) > 4; i++) m = slopeValue(L, sgn(), tut); }
      const ans = cs === 'perp' ? fDiv(F(-1), m) : m;
      const b1 = F(rand(-4, 4)), p = pointOn(ans, F(rand(-4, 4)), R);
      const ref = { m, b: b1 };
      const gr = graphFor([p], [F(0)], [b1], [{ m, b: b1, ref: true }], lab);
      return { fn: { ...base, ref, pts: [p], graph: gr }, enemy: 'liner' };
    }
    // slope and a point (written as slope-and-point, or for point-slope form)
    const p = pointOn(ln.m, ln.b, R);
    return { fn: { ...base, m: ln.m, m0: ln.m, pts: [p], graph: graphFor([p], [], [], [], lab) }, enemy: 'liner' };
  }

  // Stage 9 formulas. Each is a familiar formula, solved for one of its letters.
  const FORMULA_CASES = ['product', 'triple', 'perim', 'half', 'linear', 'standard', 'group'];
  function genFormula(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(FORMULA_CASES);
    const make = (Ls, Rs, v, extra = {}) => ({ fn: { k4: 'formula', L: Ls, R: Rs, v, skill: 'formulas', ...extra }, enemy: 'formulist' });
    const k = !tut && L >= 1 && Math.random() < 0.5 ? rand(2, [3, 4, 6, 9][L]) : 1;   // harder levels put a number in too: d = 3rt
    switch (cs) {
      case 'product': { const [res, a, b] = pick([['d', 'r', 't'], ['A', 'l', 'w'], ['F', 'm', 'a'], ['W', 'F', 'd']]); const v = pick([a, b]); return make([T(1, res)], [T(k, a + b)], v); }
      case 'triple': { const [res, lits] = pick([['V', 'lwh'], ['I', 'Prt']]); const v = pick([...lits]); return make([T(1, res)], [T(k, lits)], v); }
      case 'perim': {
        const R = [T(2, 'l'), T(2, 'w')]; if (!tut && L >= 2) R.push(T(1, 's'));
        const v = pick(['l', 'w']); return make([T(1, 'P')], R, v);
      }
      case 'half': { const half = !tut && L >= 3 && Math.random() < 0.5 ? F(pick([2, 3]), pick([3, 5])) : F(1, 2); return make([T(1, 'A')], [T(half, 'bh')], pick(['b', 'h'])); }
      case 'linear': { const R = [T(1, 'mx'), T(1, 'b')]; return make([T(1, 'y')], R, pick(['x', 'b', 'm'].slice(0, tut ? 1 : 3))); }
      case 'standard': {
        const C = [4, 6, 9, 12][L];
        for (let i = 0; i < 100; i++) {
          const a = nonZero(-C, C), b = nonZero(-C, C), c = rand(1, 4 * C) * sgn(); if (gcd(a, b) !== 1 || Math.abs(b) === 1 && L) continue;
          return make([T(a, 'x'), T(b, 'y')], [T(c)], 'y');
        }
        return make([T(2, 'x'), T(3, 'y')], [T(12)], 'y');
      }
      case 'group': return make([T(1, 'P')], [GR(T(2), [T(1, 'l'), T(1, 'w')])], pick(['l', 'w']));
    }
    return make([T(1, 'd')], [T(1, 'rt')], 't');
  }
  // Act 2 elite with formulas newest: two steps stacked, e.g. P = 2(l + w) + s, or A = (1/2)h(b + c).
  function genFormulaStacked() {
    const opts = [
      () => ({ fn: { k4: 'formula', L: [T(1, 'A')], R: [GR(T(F(1, 2), 'h'), [T(1, 'b'), T(1, 'c')])], v: 'b', skill: 'formulas' }, enemy: 'bracketknight' }),
      () => ({ fn: { k4: 'formula', L: [T(1, 'P')], R: [GR(T(2), [T(1, 'l'), T(1, 'w')]), T(1, 's')], v: 'w', skill: 'formulas' }, enemy: 'bracketknight' }),
      () => ({ ...genFormula('standard'), enemy: 'bracketknight' }),
    ];
    return pick(opts)();
  }

  // ---------------------------------------------------------------- elite and boss
  function genStacked4(list) {
    const act4 = list.filter(id => (SKILL[id].act || 1) === 4), newest = act4[act4.length - 1];
    if (newest === 'lines') { const g = genLine('twopts', false, { q: 'out', input: F(rand(-4, 5)) }); return { ...g, enemy: 'gradientknight' }; }
    if (newest === 'slope') return { ...genSlope(pick(['standard', 'graph'])), enemy: 'gradientknight' };
    if (newest === 'funcs') return { ...genFunc(pick(['outsq', 'ineq'])), enemy: 'gradientknight' };
    // order of operations only: a longer one, with a negative value and nested parentheses
    for (let i = 0; i < 100; i++) {
      const g = genEval(pick(['parsq', 'quad', 'negsq']));
      g.fn.tree = addEvalSteps(g.fn.tree, 1, 2); g.fn.orig = treeText(g.fn.tree);
      const res = evaluate(g.fn.tree, 'x', g.fn.val);
      if (res && Math.abs(fv(res)) < 600 && (isInt(res) || difficulty.level >= 3)) return { ...g, enemy: 'gradientknight' };
    }
    return { ...genEval('parsq'), enemy: 'gradientknight' };
  }
  function buildFight4(node, list) {
    const act4 = list.filter(id => (SKILL[id].act || 1) === 4);
    if (node.type === 'elite') return { phases: [() => genStacked4(list)], handSize: difficulty.hand, enemy: 'gradientknight' };
    // Boss: one phase per Act 4 stage, then a combined phase: the line through two points, and where it reaches a height.
    const phases = act4.map(id => () => GENS[id](pick(SKILL[id].cases)));
    phases.push(() => {
      for (let i = 0; i < 50; i++) {
        const g = genLine('twopts', false);
        const st = g.fn, m = twoPtSlope(st.pts[0], st.pts[1]), b = fSub(st.pts[0].y, fMul(m, st.pts[0].x));
        const x0 = F(rand(-5, 8)), y = fAdd(fMul(m, x0), b);
        if (!isInt(y) || fz(m)) continue;
        st.then = { q: 'in', y };
        return g;
      }
      return genLine('twopts', false, { q: 'out', input: F(3) });
    });
    return { phases, handSize: difficulty.hand, enemy: 'cartographer' };
  }
  const GENS = { evalx: genEval, funcs: genFunc, slope: genSlope, lines: genLine, formulas: genFormula };

  // ---------------------------------------------------------------- variety and difficulty
  function textOf4(e) {
    switch (e.k4) {
      case 'eval': return `eval ${e.fn ? ruleHtml(e.fn) + ' ' : ''}${e.orig} @${e.val ? fracText(e.val) : ''}`;
      case 'formula': return `formula ${fText(e)} for ${e.v}`;
      case 'fin': return `fin ${treeText(e.fn.rule)} ${e.rel} ${fracText(e.rhs)}`;
      case 'slope': return `slope ${e.src} ${e.pts ? e.pts.map(ptText).join(' ') : fText(e.work)}`;
      case 'line': return `line ${e.q} ${e.pts.map(ptText).join(' ')} ${e.m ? fracText(e.m) : ''}${e.ref ? ' ref ' + fracText(e.ref.m) : ''}`;
      case 'icept': return `icept ${stdText(e)}`;
    }
    return 'a4';
  }
  if (typeof ENGINES === 'object') ENGINES.fn = { text: textOf4, mirror: e => (e.k4 === 'formula' ? { ...e, L: e.R, R: e.L } : e) };
  // Generators read the difficulty themselves (numbers, extra steps, labels), and tutorials stay on Easy.
  const applyDifficulty = g => g;

  // ================================================================ skills, enemies, act
  const formulaSkill = { id: 'formulas', stage: 9, act: 2, name: 'Formulas', cases: FORMULA_CASES, gen: cycled('formulas', c => genFormula(c)),
    title: 'Stage 9: Formulas',
    intro: 'A formula is an equation with several letters, like d = rt. To solve it for one letter, treat every other letter just like a number: the same cards work. Undo + and − first, then × and ÷. Dividing by r is like dividing by 3.',
    example: 'd = rt, solve for t<br>t is multiplied by r → divide both sides by r<br>d/r = t<br><br>P = 2l + 2w, solve for w<br>Subtract 2l → P − 2l = 2w<br>Divide by 2 → P/2 − l = w',
    tutorial: [() => genFormula('product', true), () => genFormula('perim', true)] };
  const iSpecial = SKILLS.findIndex(s => s.id === 'special');
  SKILLS.splice(iSpecial >= 0 ? iSpecial + 1 : SKILLS.length, 0, formulaSkill);
  SKILLS.push(
    { id: 'evalx', stage: 14, act: 4, name: 'Order of operations', cases: EVAL_CASES, gen: cycled('evalx', c => genEval(c)),
      title: 'Stage 14: Order of operations',
      intro: 'These enemies are expressions with a value for x. Plug the value in, then work it out one operation at a time: you pick which comes next. The order is parentheses first, then powers, then × and ÷, then + and −. A negative number plugged into a power goes in brackets: (−3)² = 9. Every card here is ◎: drop it on its symbol.',
      example: 'Evaluate 3x² − 4 when x = 2<br>Plug in x = 2 → 3 · 2² − 4<br>Power → 3 · 4 − 4<br>Multiply → 12 − 4<br>Subtract → 8',
      tutorial: [() => ({ fn: { ...evalState(pm(mul(num(2), vr()), 1), F(3)), skill: 'evalx' }, enemy: 'plugger' }), () => ({ fn: { ...evalState(mul(num(4), par(add(vr(), num(1)))), F(2)), skill: 'evalx' }, enemy: 'plugger' })] },
    { id: 'funcs', stage: 15, act: 4, name: 'Functions', cases: FUNC_CASES, gen: cycled('funcs', c => genFunc(c)),
      title: 'Stage 15: Function notation',
      intro: 'A function is a rule with a name: f(x) = 2x + 3. f(4) means "put 4 into f": drop ◎ Plug 4 into f on it and the rule comes out with 4 in place of x, ready to work out. f(x) = 11 asks the other way round: which input gives 11? Drop ◎ Write out on f(x) to turn it into 2x + 3 = 11, then solve.',
      example: 'f(x) = 2x + 3<br>f(4): plug 4 into f → 2 · 4 + 3 → 11<br><br>f(x) = 11: write out → 2x + 3 = 11<br>Subtract 3 → 2x = 8 → x = 4',
      tutorial: [() => genFunc('out', true), () => genFunc('in', true)] },
    { id: 'slope', stage: 16, act: 4, name: 'Slope', cases: SLOPE_CASES, gen: cycled('slope', c => genSlope(c)),
      title: 'Stage 16: Slope',
      intro: 'The slope m says how steep a line is: rise over run, how far up for each step across. Drop ◎ Rise over run on a point on the graph: it measures from there to the other point and writes m = (change in y)/(change in x). If y = mx + b is given, the slope is the number in front of x: ◎ Read the slope. A flat line has slope 0; a vertical one has a run of 0, and its slope is undefined.',
      example: '(1, 2) and (4, 8)<br>Rise over run → m = (8 − 2)/(4 − 1)<br>→ 6/3 → m = 2<br><br>y = −3x + 5 → read the slope → m = −3',
      tutorial: [() => genSlope('pts-pos', true), () => genSlope('slopeint', true)] },
    { id: 'lines', stage: 17, act: 4, name: 'Lines', cases: LINE_CASES, gen: cycled('lines', c => genLine(c)),
      title: 'Stage 17: Equations of lines',
      intro: 'Write the line as y = mx + b: m is the slope and b is where it crosses the y-axis. With the slope and a point, drop ◎ Plug the point on the point and solve for b, then ◎ Write the line. Two points? Find m with rise over run first. Parallel lines share a slope; perpendicular slopes are negative reciprocals. To find intercepts, set x = 0 or y = 0.',
      example: 'Slope 3, through (2, 5)<br>Plug the point → 5 = 3(2) + b → 5 = 6 + b<br>Subtract 6 → b = −1<br>Write the line → y = 3x − 1',
      tutorial: [() => genLine('slopept', true), () => genLine('twopts', true)] },
  );
  for (const s of SKILLS) SKILL[s.id] = s;
  progress = loadProgress();     // the save was first read before these skills existed
  // Saves from before stage 9 existed: anyone past stage 8 gets it unlocked (its tutorial comes in their next Act 2 run).
  if (SKILLS.slice(SKILLS.indexOf(formulaSkill) + 1).some(s => isUnlocked(s.id)) && !isUnlocked('formulas')) { progress.unlocked.push('formulas'); saveProgress(); }

  Object.assign(ENEMIES, {
    formulist:      { name: 'Formulist',        rank: 'Normal', color: '#e9c46a', size: 84 },
    plugger:        { name: 'Plugger',          rank: 'Normal', color: '#2a9d8f', size: 84 },
    boxmimic:       { name: 'Box Mimic',        rank: 'Normal', color: '#e76f51', size: 84 },
    slopeling:      { name: 'Slopeling',        rank: 'Normal', color: '#8ecae6', size: 84 },
    liner:          { name: 'Liner',            rank: 'Normal', color: '#a7c957', size: 84 },
    gradientknight: { name: 'Gradient Knight',  rank: 'Elite',  color: '#6d6875', size: 100, horns: true },
    cartographer:   { name: 'The Cartographer', rank: 'Boss',   color: '#bc6c25', size: 120, crown: true },
  });
  ACTS[4] = { name: 'The Map Room', sub: 'Expressions, functions and lines', boss: 'The Cartographer', firstSkill: 'evalx',
    blurb: 'The Map Room\'s charts have come alive. Its enemies hide a value, a function\'s output, a slope or a whole line. Work them out, read the graphs, and defeat The Cartographer.' };

  const svgI = body => `<svg viewBox="0 0 24 24" width="1em" height="1em" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round">${body}</svg>`;
  Object.assign(CARD_ICONS, {
    plug:    { name: 'Plug in a value', svg: svgI('<path d="M12 3v9M8 8l4 4 4-4"/><rect x="5" y="15" width="14" height="6" rx="1"/>') },
    paren:   { name: 'Do the parentheses', svg: svgI('<path d="M9 3C5 7 5 17 9 21M15 3c4 4 4 14 0 18"/>') },
    pow:     { name: 'Work out a power', svg: svgI('<path d="M4 20l6-10 6 10"/><path d="M15 3h4l-4 5h4"/>') },
    machine: { name: 'Plug into a function', svg: svgI('<path d="M12 2v5M9 5l3 3 3-3"/><rect x="4" y="9" width="16" height="9" rx="2"/><path d="M12 18v4"/>') },
    unroll:  { name: 'Write out a function\'s rule', svg: svgI('<path d="M4 6h10M4 12h16M4 18h12"/>') },
    rise:    { name: 'Rise over run (slope from two points)', svg: svgI('<path d="M4 20h12V8"/><path d="M4 20L16 8"/>') },
    read:    { name: 'Read the slope off y = mx + b', svg: svgI('<path d="M3 12s3-6 9-6 9 6 9 6-3 6-9 6-9-6-9-6z"/><circle cx="12" cy="12" r="2.5"/>') },
    plugpt:  { name: 'Plug a point into y = mx + b', svg: svgI('<circle cx="6" cy="6" r="2.5"/><path d="M8 8l8 8M12 18h6v-6"/>') },
    ptslope: { name: 'Point-slope form', svg: svgI('<circle cx="7" cy="17" r="2.5"/><path d="M9 15l10-10"/>') },
    same:    { name: 'Parallel: same slope', svg: svgI('<path d="M4 18L16 6M8 20L20 8"/>') },
    perp:    { name: 'Perpendicular: negative reciprocal', svg: svgI('<path d="M4 20L20 4M8 8l8 8"/>') },
    write:   { name: 'Write the line y = mx + b', svg: svgI('<path d="M3 21l3-1 12-12-2-2L4 18z"/><path d="M14 4l2 2"/>') },
    zero:    { name: 'Set x = 0 or y = 0 (intercepts)', svg: svgI('<ellipse cx="12" cy="12" rx="6" ry="8"/>') },
  });

  const css = document.createElement('style');
  css.textContent = `
    #equation.a4 { gap:0; flex-wrap:nowrap; max-width:100%; }
    #equation.a4 .tok { flex-shrink:0; }
    .tok.a4 { min-width:0; padding:4px 3px; min-height:calc(var(--eqSize) * 1.35); max-width:none; border-width:3px; }
    .tok.a4.r4-op, .tok.a4.r4-par { padding-left:6px; padding-right:6px; }
    .tok.a4.tightL { margin-left:-6px; }
    .tok.a4.sup4 { font-size:.55em; align-self:flex-start; min-height:0; padding:2px 3px; margin-top:.25em; }
    .tok.a4 .xv, .tok.a4.var .xv, #a4top .xv, .fm4 .xv { font-style:normal; color:var(--accent); }
    .tok.a4 .lv { font-style:normal; }
    .n4 { display:contents; }
    .n4.frac4 { display:inline-flex; flex-direction:column; align-items:center; font-size:.78em; margin:0 .1em; }
    .row4 { display:flex; align-items:center; }
    .frac4 .tok.a4 { min-height:0; padding:2px 3px; }
    .tok.a4.r4-bar { min-height:0; width:100%; height:.5em; padding:.12em 0; display:flex; align-items:center; }
    .bar4 { display:block; width:100%; height:.12em; min-height:3px; background:currentColor; border-radius:2px; }
    .tok.a4.lhs4 { color:var(--ink); }
    .tok.a4.q4 { color:var(--muted); }
    .tok.a4.undef4 { color:var(--bad); font-size:.6em; }
    .tok.a4.hot4.fam-addsub, .unote.fam-addsub { color:#06d6a0; }
    .tok.a4.hot4.fam-muldiv, .unote.fam-muldiv { color:#b8a9ff; }
    .tok.a4.hot4.fam-pow, .unote.fam-pow { color:#ff9ad5; }
    .tok.a4.hot4.fam-paren, .unote.fam-paren { color:#ffc46b; }
    .tok.a4.hot4 { background:#ffffff14; border-color:currentColor; }
    .tok.a4.melt4 { transform:scale(.55); opacity:.15; }
    .tok.a4.drop4 { animation: drop4 .35s cubic-bezier(.2,1.5,.4,1); color:var(--accent); }
    @keyframes drop4 { from { transform: translateY(-60px); opacity:0; } }
    .tok.a4.unroll4 { animation: unroll4 .45s ease-out; transform-origin:left center; }
    @keyframes unroll4 { from { transform: scaleX(0); opacity:.2; } }
    .n4.crack4 { animation: crack4 .7s ease-in both; color:var(--bad); }
    @keyframes crack4 { 30% { transform: rotate(-4deg); } 60% { transform: rotate(3deg) translateY(4px); } 100% { transform: translateY(30px) rotate(8deg); opacity:.2; } }
    .unote.lift4 { color:var(--accent); animation: lift4 .5s cubic-bezier(.2,1.5,.4,1); }
    @keyframes lift4 { from { transform: translate(-50%, -24px) scale(.5); opacity:0; } }
    .unote.flip4 { color:#ff9ad5; animation: spinNote .5s ease-in-out; }
    .unote.stamp4 { color:var(--bad); font-weight:bold; animation: stamp4 .35s cubic-bezier(.2,1.6,.4,1); }
    @keyframes stamp4 { from { transform: translate(-50%, 0) scale(2.2); opacity:0; } }
    .tok.a4.f4t { padding-left:5px; padding-right:5px; }
    .tok.a4.tmpl .slot4, #a4top .slot4 { color:var(--muted); border-bottom:2px dashed var(--muted); padding:0 .1em; }
    .tok.a4.fx4 { color:var(--ink); }
    .tok.ok4, #graph .gtarget.ok4 { border-color: var(--good) !important; background:#06d6a022 !important; }
    #graph .gtarget.ok4 { stroke:var(--good); stroke-width:3; fill:#06d6a033; }
    .fly4 { position:fixed; z-index:30; transform:translate(0,0); transition: transform .45s cubic-bezier(.3,.9,.4,1); font-size:24px; font-weight:bold; color:var(--accent);
            margin:-14px 0 0 -10px; text-shadow:0 2px 0 #000; pointer-events:none; }
    /* function machine (stand-in art: a 48 × 32 sprite with a 4-frame "running" animation later) */
    .fm4 { position:absolute; transform:translate(-50%, -30%); z-index:4; display:flex; flex-direction:column; align-items:center; gap:4px; font-size:16px; pointer-events:none; }
    .fm4box { background:#3d3760; border:3px solid #000; border-radius:8px; padding:6px 10px; display:flex; align-items:center; gap:8px; color:var(--ink); box-shadow:0 4px 0 #000; transform:scale(0); transition: transform .3s cubic-bezier(.2,1.5,.4,1); }
    .fm4box b { color:var(--accent); font-size:20px; }
    .fm4rule { font-size:14px; color:var(--muted); }
    .fm4gear { width:14px; height:14px; border:3px dotted var(--accent); border-radius:50%; }
    .fm4in, .fm4out { font-weight:bold; color:var(--accent); opacity:0; }
    .fm4.in .fm4box { transform:scale(1); }
    .fm4.in .fm4in { animation: fmIn .45s ease-in forwards; }
    @keyframes fmIn { 0% { opacity:0; transform:translateY(-30px); } 40% { opacity:1; } 100% { opacity:0; transform:translateY(18px); } }
    .fm4.run .fm4box { animation: fmRun .15s steps(2) 4; }
    .fm4.run .fm4gear { animation: fmGear .6s linear; }
    @keyframes fmRun { 50% { transform: translateX(-2px) rotate(-2deg); } }
    @keyframes fmGear { to { transform: rotate(360deg); } }
    .fm4.out .fm4out { animation: fmOut .4s cubic-bezier(.2,1.4,.4,1) forwards; font-size:22px; }
    @keyframes fmOut { from { opacity:0; transform:translateY(-14px) scale(.6); } to { opacity:1; transform:none; } }
    .nw4 { white-space:nowrap; }
    #a4top .ask4 { color:var(--ink); font-size:1.08em; letter-spacing:.2px; }
    #a4top .ask4 .xv { font-weight:bold; }
    #a4top { display:none; font-size:17px; color:var(--muted); text-align:center; padding:0 10px; line-height:1.5; }
    #a4top.show { display:block; }
    #a4top .lab4 { font-size:.75em; border:1px solid var(--muted); border-radius:3px; padding:0 4px; margin-right:4px; vertical-align:middle; }
    #a4top .tok.a4 { display:inline-flex; min-height:0; padding:0 4px; border-width:2px; color:var(--ink); vertical-align:middle; }
    #a4top .tmpl4 { color:var(--ink); }
    #a4top .ic4 { display:inline-block; color:var(--ink); }
    #a4top b, #a4top i { color:var(--ink); }
    #arena.targeting #a4top .tok.a4 { border-color: var(--muted); background:#ffffff0d; }
    #a4top .tok.a4.hover { border-color: var(--accent); background:#ffd16633; }
    /* the graph panel: right of the equation on desktop and landscape phones, under it on portrait phones */
    #graph { display:none; position:absolute; right:14px; top:50%; transform:translateY(-50%); width:260px; height:260px; color:var(--muted); line-height:0; }
    #graph.show { display:block; }
    #arena.g4 { padding-right:290px; }
    #graph svg { width:100%; height:100%; overflow:visible; background:#0003; border:2px solid #0008; border-radius:6px; }
    #graph .gGrid { stroke:#ffffff14; stroke-width:1; }
    #graph .gAxis { stroke:#a59fc4; stroke-width:2; }
    #graph .gAxLab, #graph .gNum { fill:#a59fc4; font: bold 10px "Courier New", monospace; text-anchor:middle; }
    #graph .gAxLab { font-size:12px; font-style:italic; }
    #graph .gLine { stroke:#7bdff2; stroke-width:2.5; opacity:.7; }
    #graph .gRef { stroke:#ff9ad5; stroke-width:3; stroke-dasharray:6 4; }
    #graph .gRes { stroke:var(--accent); stroke-width:3.5; }
    #graph .gRun { stroke:#06d6a0; stroke-width:3.5; }
    #graph .gRise { stroke:#ff9ad5; stroke-width:3.5; }
    #graph .gRunLab { fill:#06d6a0; font: bold 12px "Courier New", monospace; text-anchor:middle; }
    #graph .gRiseLab { fill:#ff9ad5; font: bold 12px "Courier New", monospace; }
    #graph .gPt { fill:var(--accent); stroke:#000; stroke-width:1.5; }
    #graph .gPtLab { fill:var(--ink); font: bold 12px "Courier New", monospace; paint-order:stroke; stroke:#1d1b2a; stroke-width:3px; }
    #graph .gIc { fill:none; stroke:var(--good); stroke-width:3; }
    #graph .gIc.anim { animation: gPulse 1s ease-out 2; transform-box:fill-box; transform-origin:center; }
    @keyframes gPulse { 50% { stroke-width:6; transform: scale(1.6); } }
    #graph .gDash { stroke-dasharray:.035 .025 !important; }   /* lines carry pathLength="1", so dash lengths are fractions of the line */
    #graph .anim.gDash[pathLength] { stroke-dasharray:.04 .03 !important; stroke-dashoffset:0; animation: gFade .5s ease-out both; }
    #graph .gHalf { fill:#7bdff2; opacity:.16; stroke:none; }
    #graph .gHalf.anim { animation: gShade .7s ease-out both; }
    #graph .gOverlap { fill:var(--accent); opacity:.38; stroke:none; }
    #graph .gOverlap.anim { animation: gGlow 1.2s ease-out both; }
    @keyframes gShade { from { opacity:0; } }
    @keyframes gGlow { 0% { opacity:0; } 50% { opacity:.65; } 100% { opacity:.38; } }
    #graph .gDot { fill:var(--good); stroke:#000; stroke-width:1.5; }
    #graph .gDot.anim { animation: gPulse 1s ease-out 2; transform-box:fill-box; transform-origin:center; }
    #graph .gLineLab { font: bold 11px "Courier New", monospace; fill:#7bdff2; paint-order:stroke; stroke:#1d1b2a; stroke-width:3px; }
    #graph .gtarget { fill:transparent; stroke:transparent; cursor:pointer; }
    #graph .gLineHit { stroke:transparent; stroke-width:24; }
    #arena.pts4 #graph .gtarget.gpt { stroke:var(--muted); stroke-width:2; stroke-dasharray:4 3; fill:#ffffff10; }
    #arena.targeting #graph .gLineHit { stroke:#ffffff18; }
    #graph .gtarget.hover { stroke:var(--accent) !important; stroke-width:3; fill:#ffd16633 !important; }
    #graph .anim[pathLength] { stroke-dasharray:1; stroke-dashoffset:1; animation: gDraw .7s ease-out forwards; }
    #graph text.anim { animation: gFade .4s ease-out .6s both; }
    @keyframes gDraw { to { stroke-dashoffset:0; } }
    @keyframes gFade { from { opacity:0; } }
    @media (max-width: 640px) {
      #a4top { font-size:12px; line-height:1.35; }
      #arena.g4 { padding-right:0; }
      #graph { position:static; transform:none; width:clamp(150px, 28vh, 230px); height:clamp(150px, 28vh, 230px); flex:none; }
      #arena.g4 #enemyBox svg { width:36px; height:36px; }
      .tok.a4 { min-height:calc(var(--eqSize) * 1.4); padding:3px 2px; }
      .tok.a4.r4-op, .tok.a4.r4-par { padding-left:4px; padding-right:4px; }
      .fm4 { font-size:12px; } .fm4box b { font-size:16px; } .fm4rule { font-size:11px; }
    }
    @media (orientation: landscape) and (max-height: 520px) {
      #a4top { font-size:11px; }
      #arena.g4 { padding-right:calc(min(56vh, 40vw) + 12px); }
      #graph { position:absolute; right:6px; top:50%; transform:translateY(-50%); width:min(56vh, 40vw); height:min(56vh, 40vw); }
    }
  `;
  document.head.appendChild(css);

  window.ACT4 = { apply: apply4, isSolved: isSolved4, makeEquation: makeEquation4, refreshPath, render, prefit, clear, makeHand: makeHand4,
    isCorrect, whyWrong, animFor, applyDifficulty, label, text, kind, icon, slot, targetSel, onDrag, buildFight: buildFight4,
    genFormulaStacked, drawGraph, gens: GENS, eqText: textOf4, prompt,
    // test hooks
    _canon: canon4, _correct: correct4, _active: active, _evaluate: evaluate,
    // shared with act5.js (systems), which builds on the formula engine, the work delegation and the graph panel
    kit: { T, GR, fApply, fCanon, fSolved, fCorrect, fSteps, fText, fHtml, fTermStr, fSide, fHand, fWhy, fCardText, hasV, keyT, tMul, signedT,
      renderFormula, animFormula, drawGraph, windowFor, TOK, EQTOK, topEl, banner, refOf, P, XI, kickClass, clone, fNeg, fSub, fDiv, fEq, fz, fv,
      isTutorial, lvl, known, ptText, lineTextOf, lineHtml, explain4 } };
})();
