// =====================================================================
//  Act 5: The Twin Observatory (systems of equations and inequalities)
// =====================================================================
// Stage 18  Substitution             y = 2x, x + y = 9
// Stage 19  Elimination              2x + 3y = 12, 2x − y = 4
// Stage 20  Special systems          parallel lines (no solution), the same line twice, solving by graphing
// Stage 21  Systems of inequalities  y > x + 1, y ≤ −2x + 4
//
// States have a kind, `k5`:
//   sys    two equations in x and y: { eqs: [eq, eq], vals: {x, y}, work, method, ask, verdict, done }
//          Each equation is Act 4's formula model ({ L, R } of terms T(k, 'x'), T(k, 'y'), T(k)).
//          method: 'sub' | 'elim' | 'any' (which moves count); ask: 'solve' | 'count' | 'graph'.
//          `work` is the smaller problem being solved right now: a formula (getting one letter alone in
//          one equation, solved by Act 4's formula engine) or an equation in one letter (Act 2's model,
//          after substituting, eliminating or plugging a value back in). When the letters cancel, the work
//          is a statement like 0 = 5 and the player declares No solution or Infinitely many.
//   ineq5  two inequalities in x and y: { rows: [{ L, R, rel, form }], st: [{ line, shade }], askPt, ans }
//          Each boundary is drawn solid or dashed, then a side is shaded (or found with a test point).
//          The overlap of the two shaded sides glows on the graph panel.
//
// This file builds on act4.js: the formula engine, the graph panel (drawGraph, with half-planes added
// for this act) and its helpers come from ACT4.kit. index.html switches to this engine for generators
// that return { sys } (cur.act5).
'use strict';
(function () {
  const A2 = window.ACT2, A4 = window.ACT4;
  if (!A2 || !A4 || !A4.kit) return;
  const K = A4.kit;
  const { T, fApply, fCanon, fSolved, fCorrect, fTermStr, fSide, fHand, fWhy, drawGraph, TOK, EQTOK, banner, refOf, P, kickClass, clone, fNeg, fSub, fDiv, fEq, fz, fv } = K;
  const isTutorial = K.isTutorial, lvl = K.lvl;
  const sgn = () => (Math.random() < 0.5 ? -1 : 1);
  const LET = ['x', 'y'], other = v => (v === 'x' ? 'y' : 'x');
  const ROWLAB = ['①', '②'];
  const ptText = p => `(${fracText(p.x)}, ${fracText(p.y)})`;
  const O = { x: F(0), y: F(0) };

  // ================================================================ equations in x and y
  const nz = side => side.filter(t => t.g || !fz(t.k));
  const EQ = (L, R) => ({ L: nz(L), R: nz(R) });
  const stdEq = (a, b, c) => EQ([T(a, 'x'), T(b, 'y')], [T(c)]);
  const yEq = (m, b) => EQ([T(1, 'y')], [T(m, 'x'), T(b)]);
  const xEq = (n, d) => EQ([T(1, 'x')], [T(n, 'y'), T(d)]);
  // a·x + b·y = c, whatever the shape
  function std(eq) {
    let a = F(0), b = F(0), c = F(0);
    for (const [side, s] of [[eq.L, 1], [eq.R, -1]]) for (const t of side) {
      if (t.g) continue;
      const k = s > 0 ? t.k : fNeg(t.k);
      if (t.lit === 'x') a = fAdd(a, k); else if (t.lit === 'y') b = fAdd(b, k); else c = fSub(c, k);
    }
    return { a, b, c };
  }
  const hasL = (eq, v) => [...eq.L, ...eq.R].some(t => !t.g && t.lit === v && !fz(t.k));
  const coefOf = (eq, v) => std(eq)[v === 'x' ? 'a' : 'b'];
  const aloneIn = (eq, v) => fSolved({ ...eq, v });
  const aloneV = eq => (aloneIn(eq, 'y') ? 'y' : aloneIn(eq, 'x') ? 'x' : null);
  const exprOf = (eq, v) => (eq.L.length === 1 && eq.L[0].lit === v && fIs(eq.L[0].k, 1) ? eq.R : eq.L);
  // Lined up: x-term then y-term on the left, one number on the right.
  function isStd(eq) {
    if (eq.R.length > 1 || eq.R.some(t => t.g || t.lit)) return false;
    const lits = eq.L.map(t => (t.g ? '?' : t.lit)).join(',');
    return lits === 'x' || lits === 'y' || lits === 'x,y' || lits === 'y,x';
  }
  // The terms that are on the wrong side for ax + by = c (a letter on the right, a number on the left),
  // each as the both-sides move that clears it: 3y = 7 − 2x needs "add 2x to both sides".
  function moveOpts(eq, i) {
    const out = [];
    for (const [side, want] of [[eq.L, false], [eq.R, true]]) for (const t of side) {
      if (t.g || fz(t.k) || !!t.lit !== want) continue;
      out.push(C5('move', { row: i, sgn: t.k.n > 0 ? '-' : '+', t: { k: fAbs(t.k), lit: t.lit || '', den: '' } }));
    }
    return out;
  }
  // Adds (or subtracts) a term on both sides of one equation; the left side is kept in x, y order.
  function moveEq(eq, c) {
    const q = clone(eq), k = c.sgn === '+' ? c.t.k : fNeg(c.t.k);
    for (const s of ['L', 'R']) {
      const side = q[s], j = side.findIndex(o => !o.g && o.lit === c.t.lit && !o.den);
      if (j >= 0) { const nk = fAdd(side[j].k, k); if (fz(nk)) side.splice(j, 1); else side[j] = { ...side[j], k: nk }; }
      else side.push(T(k, c.t.lit));
    }
    const ord = t => (t.lit === 'x' ? 0 : t.lit === 'y' ? 1 : 2);
    q.L.sort((a, b) => ord(a) - ord(b));
    return q;
  }
  const moveTerm = c => fTermStr({ k: c.t.k, lit: c.t.lit, den: '' }, true, false, '');
  // The line on the graph: { m, b } or a vertical { x }.
  function lineOf(eq) {
    const { a, b, c } = std(eq);
    if (fz(b)) return fz(a) ? null : { x: fDiv(c, a) };
    return { m: fDiv(fNeg(a), b), b: fDiv(c, b) };
  }
  const scaleEq = (eq, k) => ({ L: eq.L.map(t => ({ ...t, k: fMul(t.k, F(k)) })), R: eq.R.map(t => ({ ...t, k: fMul(t.k, F(k)) })) });
  const lineupEq = eq => { const s = std(eq); return stdEq(s.a, s.b, s.c); };
  const sideHtml = side => fSide(side, true, '');
  const sideText = side => fSide(side, false, '');
  const eqText = (eq, rel = '=') => `${sideText(eq.L)} ${rel} ${sideText(eq.R)}`;
  const eqHtml = (eq, rel = '=') => `${sideHtml(eq.L)} ${rel} ${sideHtml(eq.R)}`;
  const isUnit = k => fIs(fAbs(k), 1);
  const intOK = f => isInt(f);

  // ---------------------------------------------------------------- to Act 2's model (one letter)
  // Act 2 calls its letter x and shows w.v; terms in the other letter are replaced by `repl`.
  function a2Side(side, u, repl) {
    const out = [];
    for (const t of side) {
      if (!t.lit) out.push({ t: 'n', k: t.k });
      else if (t.lit === u) out.push({ t: 'x', k: t.k });
      else out.push(...repl(t));
    }
    return out.filter(i => i.t === 'g' || !fz(i.k));
  }
  const toItem = t => (t.lit ? { t: 'x', k: t.k } : { t: 'n', k: t.k });
  function substA2(eq, v, expr) {
    const u = other(v);
    const repl = t => (expr.length === 1 ? [toItem(K.tMul(expr[0], T(t.k)))] : [{ t: 'g', m: t.k, items: expr.map(toItem) }]);
    return { L: a2Side(eq.L, u, repl), R: a2Side(eq.R, u, repl), result: null, v: u };
  }
  function plugA2(eq, v, val) {
    const repl = t => [{ t: 'n', k: fMul(t.k, val) }];
    return { L: a2Side(eq.L, other(v), repl), R: a2Side(eq.R, other(v), repl), result: null, v: other(v) };
  }
  // Adding (sign 1) or subtracting (sign −1) the equations, column by column.
  function sumCols(eqs, sign) {
    const s0 = std(eqs[0]), s1 = std(eqs[1]), f = F(sign);
    return { a: fAdd(s0.a, fMul(f, s1.a)), b: fAdd(s0.b, fMul(f, s1.b)), c: fAdd(s0.c, fMul(f, s1.c)) };
  }
  function combineA2(eqs, sign) {
    const s = sumCols(eqs, sign);
    const u = fz(s.a) ? 'y' : 'x', k = fz(s.a) ? s.b : s.a;
    return { L: fz(k) ? [] : [{ t: 'x', k }], R: fz(s.c) ? [] : [{ t: 'n', k: s.c }], result: null, v: u };
  }
  const sumN = side => side.reduce((a, i) => (i.t === 'n' ? fAdd(a, i.k) : a), F(0));
  const isStmt = w => !!w && !w.k4 && !w.result && ![...w.L, ...w.R].some(i => i.t !== 'n');
  const stmtTrue = w => fEq(sumN(w.L), sumN(w.R));
  const stmtText = w => `${fracText(sumN(w.L))} = ${fracText(sumN(w.R))}`;
  function a2Val(w) {
    const oth = w.L.length === 1 && w.L[0].t === 'x' ? w.R : w.L;
    return sumN(oth);
  }

  // ================================================================ inequalities
  const strict = rel => rel === '<' || rel === '>';
  const geRel = rel => rel === '>' || rel === '≥';
  const flipRel = rel => ({ '<': '>', '>': '<', '≤': '≥', '≥': '≤' })[rel];
  const relHolds = (v, rel) => (rel === '<' ? v < 0 : rel === '≤' ? v <= 0 : rel === '>' ? v > 0 : v >= 0);
  const valAt = (row, p) => { const { a, b, c } = std(row); return fv(a) * fv(p.x) + fv(b) * fv(p.y) - fv(c); };
  const onLine = (row, p) => Math.abs(valAt(row, p)) < 1e-9;
  const inRow = (row, p) => relHolds(valAt(row, p), row.rel);
  // Which side is shaded: above or below (more y or less), or right or left for a vertical boundary.
  function sideOf(row) {
    const { a, b } = std(row), ge = geRel(row.rel);
    if (fz(b)) return (a.n > 0) === ge ? 'right' : 'left';
    return (b.n > 0) === ge ? 'above' : 'below';
  }
  const SHADE = ['above', 'below', 'left', 'right'];
  const TESTPTS = [O, { x: F(1), y: F(0) }];
  const halfOf = (row, i) => { const { a, b, c } = std(row); return { t: 'half', A: a, B: b, C: c, ge: geRel(row.rel), cls: 'h5' + i }; };

  // ================================================================ states
  const qid = () => Math.random().toString(36).slice(2, 8);
  function sysState(eqs, o = {}) {
    return { k5: 'sys', eqs, vals: { x: null, y: null }, work: null, method: o.method || 'any', ask: o.ask || 'solve', shown: false,
      verdict: null, done: false, skill: o.skill, sol: o.sol || null, cands: o.cands || null, win: o.win || null, qid: qid() };
  }
  function ineqState(rows, o = {}) {
    return { k5: 'ineq5', rows, st: rows.map(() => ({ line: null, shade: null, tested: null })), askPt: o.askPt || null, ans: null,
      skill: o.skill || 'sysineq', win: o.win || { x0: -7, x1: 7, y0: -7, y1: 7 }, qid: qid() };
  }
  const rowOf = ref => { const m = /^q(\d)/.exec(ref || ''); return m ? +m[1] : -1; };
  const C5 = (op, o = {}) => ({ op, a5: true, scope: op === 'addeq' || op === 'subeq' ? 'both' : 'part', ...o });
  const ROWCARD = ['iso', 'subst', 'plugv', 'scale', 'lineup', 'solid', 'dashed', 'above', 'below', 'left', 'right', 'test', 'ttrue', 'tfalse', 'move'];
  const TVERDICT = ['ttrue', 'tfalse'];
  const VERDICT = ['snone', 'sall', 'sone'];

  // ================================================================ the moves that count
  // Every right move for a state (the first is the one the game expects). A card is right when it
  // matches one of them, dropped on the right equation.
  function scaleOpts(s0, s1) {
    const out = [];
    for (const col of ['a', 'b']) {
      const p = Math.abs(fv(s0[col])), q = Math.abs(fv(s1[col]));
      if (!p || !q || !Number.isInteger(p) || !Number.isInteger(q)) continue;
      if (q > p && q % p === 0) out.push(C5('scale', { row: 0, k: q / p, col }));
      if (p > q && p % q === 0) out.push(C5('scale', { row: 1, k: p / q, col }));
    }
    if (!out.length) for (const col of ['a', 'b']) {
      const p = Math.abs(fv(s0[col])), q = Math.abs(fv(s1[col]));
      if (!p || !q || !Number.isInteger(p) || !Number.isInteger(q)) continue;
      const l = p / gcd(p, q) * q;
      out.push(C5('scale', { row: 0, k: l / p, col }), C5('scale', { row: 1, k: l / q, col }));
    }
    return out.sort((x, y) => x.k - y.k);
  }
  function subOpts(e) {
    const o = [];
    for (const v of ['y', 'x']) for (const i of [0, 1]) if (aloneIn(e.eqs[1 - i], v) && hasL(e.eqs[i], v)) o.push(C5('subst', { v, row: i }));
    if (o.length) return o;
    for (const v of ['y', 'x']) for (const i of [0, 1]) {
      const q = e.eqs[i];
      if (hasL(q, v) && hasL(q, other(v)) && isUnit(coefOf(q, v)) && [...q.L, ...q.R].filter(t => t.lit === v).length === 1) o.push(C5('iso', { v, row: i }));
    }
    return o;
  }
  function elimOpts(e) {
    const ns = [0, 1].filter(i => !isStd(e.eqs[i]));
    if (ns.length) return ns.flatMap(i => moveOpts(e.eqs[i], i));
    const o = [], add = sumCols(e.eqs, 1), sub = sumCols(e.eqs, -1);
    if (fz(add.a) || fz(add.b)) o.push(C5('addeq'));
    if (fz(sub.a) || fz(sub.b)) o.push(C5('subeq'));
    if (o.length) return o;
    return scaleOpts(std(e.eqs[0]), std(e.eqs[1]));
  }
  const lineupOpts = e => [0, 1].filter(i => !isStd(e.eqs[i])).flatMap(i => moveOpts(e.eqs[i], i));
  function countVerdict(e) {
    const l0 = lineOf(e.eqs[0]), l1 = lineOf(e.eqs[1]);
    if (fEq(l0.m, l1.m)) return fEq(l0.b, l1.b) ? 'sall' : 'snone';
    return 'sone';
  }
  function options(e) {
    if (e.k5 === 'ineq5') return optionsI(e);
    if (e.done) return [];
    if (e.work) return [];
    if (e.ask === 'graph') { const i = e.cands.findIndex(p => fEq(p.x, e.sol.x) && fEq(p.y, e.sol.y)); return [C5('readpt', { ref: 'P' + i })]; }
    if (e.ask === 'count') {
      const notY = [0, 1].filter(i => !aloneIn(e.eqs[i], 'y'));
      if (notY.length) return notY.map(i => C5('iso', { v: 'y', row: i }));
      const vd = C5(countVerdict(e));
      return e.shown ? [vd] : [C5('slopes'), vd];
    }
    const kn = LET.filter(v => e.vals[v] !== null);
    if (kn.length === 1) {
      const v = kn[0], u = other(v);
      return [0, 1].filter(i => hasL(e.eqs[i], u)).sort((i, j) => (aloneIn(e.eqs[j], u) ? 1 : 0) - (aloneIn(e.eqs[i], u) ? 1 : 0))
        .map(i => C5('plugv', { v, val: e.vals[v], row: i }));
    }
    if (e.method === 'sub') return subOpts(e);
    if (e.method === 'elim') return elimOpts(e);
    if ([0, 1].some(i => aloneV(e.eqs[i]))) return [...subOpts(e), ...lineupOpts(e)];
    if (e.eqs.every(isStd)) return [...elimOpts(e), ...subOpts(e)];
    return [...subOpts(e), ...lineupOpts(e)];
  }
  function stepI(e, i) {
    const st = e.st[i], r = e.rows[i];
    if (!st.line) return [C5(strict(r.rel) ? 'dashed' : 'solid', { row: i })];
    if (st.shade) return [];
    // After a test point the player decides: is the inequality true there? That picks the side.
    if (st.tested) return [C5(inRow(r, st.tested) ? 'ttrue' : 'tfalse', { row: i, p: st.tested })];
    const o = [C5(sideOf(r), { row: i })];
    for (const p of TESTPTS) if (!onLine(r, p)) o.push(C5('test', { row: i, p }));
    // y alone (or a plain x = c): the sign says which side. Otherwise the game expects a test point.
    if (r.form === 'std' && !onLine(r, O)) o.unshift(o.splice(1, 1)[0]);
    return o;
  }
  const inBoth = (e, p) => e.rows.every(r => inRow(r, p));
  const pendingTest = e => [0, 1].find(i => e.st[i].tested && !e.st[i].shade);
  function optionsI(e) {
    const pend = pendingTest(e);
    if (pend !== undefined) return stepI(e, pend);     // a tested point is answered before anything else
    const out = [...stepI(e, 0), ...stepI(e, 1)];
    if (out.length) return out;
    if (e.askPt && !e.ans) return [C5(inBoth(e, e.askPt) ? 'yes' : 'no')];
    return [];
  }

  function canon5(e) {
    if (e.k5 === 'sys' && !e.done && e.work) {
      const w = e.work;
      if (w.k4 === 'formula') return fSolved(w) ? null : fCanon(w);
      if (isStmt(w)) return C5(stmtTrue(w) ? 'sall' : 'snone');
      return A2.canon(w);
    }
    const o = options(e);
    return o.length ? o[0] : null;
  }
  const isSolved5 = e => canon5(e) === null;
  const sameP = (a, b) => !!a && !!b && fEq(a.x, b.x) && fEq(a.y, b.y);
  function matches(o, c, ref) {
    if (o.op !== c.op) return false;
    if (ROWCARD.includes(c.op) && rowOf(ref) !== o.row) return false;
    if (c.op === 'scale') return Math.abs(c.k) === Math.abs(o.k);
    if (c.op === 'iso' || c.op === 'subst') return c.v === o.v;
    if (c.op === 'plugv') return c.v === o.v && fEq(c.val, o.val);
    if (c.op === 'readpt') return ref === o.ref;
    if (c.op === 'test') return sameP(c.p, o.p);
    if (c.op === 'move') return c.sgn === o.sgn && c.t.lit === o.t.lit && fEq(c.t.k, o.t.k);
    return true;
  }
  function correct5(e, c, target) {
    const ref = refOf(target);
    if (c.op === 'trap') return false;
    if (e.k5 === 'sys' && !e.done && e.work) {
      const w = e.work;
      if (isStmt(w)) return !!c.a5 && c.op === (stmtTrue(w) ? 'sall' : 'snone');
      if (c.a5) return false;
      return w.k4 === 'formula' ? fCorrect(w, c, ref) : A2.isCorrect({ state: w }, c, target);
    }
    if (!c.a5) return false;
    return options(e).some(o => matches(o, c, ref));
  }

  // ---------------------------------------------------------------- applying a move
  // Once a piece of work is finished it folds back into the system: a letter alone replaces its
  // equation; a solved one-letter equation gives a value.
  function settle(r) {
    const w = r.work;
    if (w && w.k4 === 'formula' && fSolved(w)) {
      const left = w.L.length === 1 && w.L[0].lit === w.v && fIs(w.L[0].k, 1);
      r.eqs[w.row] = left ? { L: w.L, R: w.R } : { L: w.R, R: w.L };
      r.work = null;
    } else if (w && !w.k4 && !isStmt(w) && A2.isSolved(w)) { r.vals[w.v] = a2Val(w); r.work = null; }
    if (!r.work && r.vals.x !== null && r.vals.y !== null) r.done = true;
    return r;
  }
  function apply5(e, c, ref) {
    const r = clone(e);
    if (e.k5 === 'ineq5') {
      const i = rowOf(ref);
      if (c.op === 'solid' || c.op === 'dashed') r.st[i].line = c.op;
      else if (SHADE.includes(c.op)) r.st[i].shade = c.op;
      else if (c.op === 'test') r.st[i].tested = c.p;
      else if (TVERDICT.includes(c.op)) r.st[i].shade = sideOf(e.rows[i]);
      else if (c.op === 'yes' || c.op === 'no') r.ans = c.op;
      return r;
    }
    if (e.work) {
      if (c.a5 && (c.op === 'snone' || c.op === 'sall')) { r.verdict = c.op; r.done = true; r.stmt = stmtText(e.work); r.work = null; return r; }
      if (c.a5 || c.op === 'trap') return r;
      r.work = e.work.k4 === 'formula' ? fApply(e.work, c, ref) : A2.apply(e.work, c, ref);
      return settle(r);
    }
    const i = rowOf(ref);
    switch (c.op) {
      case 'iso': r.work = { k4: 'formula', L: clone(e.eqs[i].L), R: clone(e.eqs[i].R), v: c.v, row: i }; break;
      case 'subst': { const j = 1 - i; r.work = substA2(e.eqs[i], c.v, exprOf(e.eqs[j], c.v)); r.work.from = j; r.work.into = i; break; }
      case 'plugv': r.work = plugA2(e.eqs[i], c.v, c.val); r.work.into = i; break;
      case 'scale': r.eqs[i] = scaleEq(e.eqs[i], c.k); break;
      case 'move': r.eqs[i] = moveEq(e.eqs[i], c); break;
      case 'addeq': case 'subeq': r.work = combineA2(e.eqs, c.op === 'addeq' ? 1 : -1); r.work.op = c.op; break;
      case 'slopes': r.shown = true; break;
      case 'sone': case 'snone': case 'sall': r.verdict = c.op; r.done = true; break;
      case 'readpt': { const p = e.cands[+String(ref).slice(1)]; if (p) { r.vals = { x: p.x, y: p.y }; r.done = true; } break; }
      default: return r;
    }
    return settle(r);
  }

  // ================================================================ path, skills, answers
  const HOME = { iso: 'subst', subst: 'subst', scale: 'elim', move: 'elim', addeq: 'elim', subeq: 'elim',
    snone: 'special5', sall: 'special5', sone: 'special5', slopes: 'special5', readpt: 'special5',
    solid: 'sysineq', dashed: 'sysineq', ttrue: 'sysineq', tfalse: 'sysineq', above: 'sysineq', below: 'sysineq', left: 'sysineq', right: 'sysineq', test: 'sysineq', yes: 'sysineq', no: 'sysineq' };
  function skillFor(m, main) {
    let home = m.a5 ? HOME[m.op] : null;
    if (!home) home = m.op === 'dist' ? 'distribute' : m.op === 'comb' ? 'liketerms' : m.x ? 'xboth' : m.lcd ? 'clearfrac' : m.f4 ? 'formulas' : main;
    return home === main || isUnlocked(home) ? home : main;
  }
  function pathOf5(e, main) {
    const path = []; let s = e;
    for (let i = 0; i < 60; i++) { const m = canon5(s); if (!m) break; path.push({ state: s, move: m, skill: skillFor(m, main) }); s = apply5(s, m, m.row !== undefined ? 'q' + m.row : m.ref); }
    return { path, end: s };
  }
  const solText = v => `x = ${fracText(v.x)}, y = ${fracText(v.y)}`;
  function answerOf(e) {
    if (e.k5 === 'ineq5') {
      const base = 'The solution is where the two shaded sides overlap';
      if (!e.askPt) return base;
      return `${ptText(e.askPt)} ${inBoth(e, e.askPt) ? 'is' : 'is not'} a solution`;
    }
    if (e.verdict === 'snone') return 'No solution: the lines are parallel';
    if (e.verdict === 'sall') return 'Infinitely many solutions: it\'s the same line';
    if (e.verdict === 'sone') return 'One solution: the lines cross once';
    return `(${fracText(e.vals.x)}, ${fracText(e.vals.y)}): ${solText(e.vals)}`;
  }
  function makeEquation5(state, enemy) {
    const main = state.skill || 'subst', { path, end } = pathOf5(state, main);
    return { start: state, end, path, main, skills: [...new Set(path.map(p => p.skill))], enemy, act2: true, act5: true, answer: F(0), answerText: answerOf(end) };
  }
  function refreshPath(cur) {
    const fresh = pathOf5(cur.state, cur.main).path;
    cur.path = cur.path.slice(0, cur.step).concat(fresh);
  }

  // ================================================================ cards
  const CARD = {
    iso:    c => ({ label: `Solve for ${c.v}`, text: `Get ${c.v} alone in one equation`, kind: 'Solve for a letter', icon: 'iso5' }),
    subst:  c => ({ label: `Sub in ${c.v}`, text: `Put ${c.v}'s expression in for ${c.v} in the other equation`, kind: 'Substitute', icon: 'subst5' }),
    plugv:  c => ({ label: `${c.v} = ${fracText(c.val)}`, text: `Plug ${c.v} = ${fracText(c.val)} back into an equation`, kind: 'Plug back in', icon: 'plug' }),
    scale:  c => ({ label: `Scale ${TIMES}${c.k < 0 ? `(${MINUS}${-c.k})` : c.k}`, text: `Multiply every term of one equation by ${numText(c.k)}`, kind: 'Multiply an equation', icon: 'scale5' }),
    move:   c => ({ label: `${c.sgn === '+' ? '+' : MINUS}${c.t ? moveTerm(c) : ''}`, text: c.t ? `${c.sgn === '+' ? 'Add' : 'Subtract'} ${moveTerm(c)} ${c.sgn === '+' ? 'to' : 'from'} both sides` : 'Move a term across', kind: c.sgn === '+' ? 'Add to both sides' : 'Subtract from both sides', icon: c.sgn === '+' ? 'add' : 'sub' }),
    addeq:  () => ({ label: '① + ②', text: 'Add the two equations, column by column', kind: 'Add the equations', icon: 'addeq5' }),
    subeq:  () => ({ label: '① − ②', text: 'Subtract ② from ①, column by column', kind: 'Subtract the equations', icon: 'subeq5' }),
    snone:  () => ({ label: 'No solution', text: 'Declare: no solution (the lines never meet)', kind: 'Declare no solution', icon: 'none' }),
    sall:   () => ({ label: 'All points', text: 'Declare: infinitely many solutions (same line)', kind: 'Declare infinitely many', icon: 'all' }),
    sone:   () => ({ label: 'One point', text: 'Declare: exactly one solution (lines cross once)', kind: 'Declare one solution', icon: 'one5' }),
    slopes: () => ({ label: 'm and b', text: 'Compare the slopes and the y-intercepts', kind: 'Compare slopes', icon: 'read' }),
    readpt: () => ({ label: 'Read point', text: 'Read the point where the two lines cross', kind: 'Read the crossing point', icon: 'cross5' }),
    solid:  () => ({ label: 'Solid line', text: `Solid boundary: ≤ or ≥ include the line`, kind: 'Solid boundary', icon: 'solid5' }),
    dashed: () => ({ label: 'Dashed line', text: 'Dashed boundary: &lt; or &gt; leave the line out', kind: 'Dashed boundary', icon: 'dashed5' }),
    above:  () => ({ label: 'Shade above', text: 'Shade above the line', kind: 'Shade a side', icon: 'shade5' }),
    below:  () => ({ label: 'Shade below', text: 'Shade below the line', kind: 'Shade a side', icon: 'shade5' }),
    left:   () => ({ label: 'Shade left', text: 'Shade left of the line', kind: 'Shade a side', icon: 'shade5' }),
    right:  () => ({ label: 'Shade right', text: 'Shade right of the line', kind: 'Shade a side', icon: 'shade5' }),
    test:   c => ({ label: `Test ${ptText(c.p)}`, text: `Test ${ptText(c.p)} in the inequality to pick a side`, kind: 'Test point', icon: 'test5' }),
    ttrue:  c => ({ label: 'True ✓', text: c.p ? `${ptText(c.p)} makes it true: shade its side` : 'The test point makes it true: shade its side', kind: 'Test point is true', icon: 'all' }),
    tfalse: c => ({ label: 'False ✗', text: c.p ? `${ptText(c.p)} makes it false: shade the other side` : 'The test point makes it false: shade the other side', kind: 'Test point is false', icon: 'none' }),
    yes:    () => ({ label: 'Yes ✓', text: 'The point is a solution: in both shaded regions', kind: 'Declare a solution', icon: 'one5' }),
    no:     () => ({ label: 'No ✗', text: 'The point is not in both shaded regions', kind: 'Declare not a solution', icon: 'none' }),
  };
  const info = c => (c && c.a5 && CARD[c.op] ? CARD[c.op](c) : null);
  const label = c => (c && c.op === 'trap' && c.a5 ? `<span class="clong">${c.label}</span>` : info(c) ? `<span class="clong">${info(c).label}</span>` : null);
  const text = c => (c && c.op === 'trap' && c.a5 ? c.text : info(c) ? info(c).text : null);
  const kind = c => (c && c.op === 'trap' && c.a5 ? 'Trap: ' + c.trap : info(c) ? info(c).kind : null);
  const icon = c => (c && c.op === 'trap' && c.a5 ? c.icon : info(c) ? info(c).icon : null);
  // Fixed slots, counted from the left.
  const SLOT = { iso: 0, subst: 1, plugv: 2, lineup: 0, scale: 1, addeq: 2, subeq: 3, sone: 4, snone: 5, sall: 6, slopes: 0, readpt: 1,
    solid: 0, dashed: 1, above: 2, below: 3, left: 2, right: 3, test: 4, yes: 5, no: 6, ttrue: 2, tfalse: 3 };
  const slot = c => (c && c.a5 && c.op !== 'trap' && c.op !== 'scale' ? SLOT[c.op] ?? null : null);
  const ROWSEL = '#equation .tok[data-row]:not(.eq), #a4top .tok[data-row]';
  function targetSel(c) {
    if (!c) return null;
    if (c.f4 || (!c.a5 && c.op !== 'trap')) return (c.scope || 'both') === 'part' ? '#equation .tok:not(.eq):not(.rel)' : null;
    if ((c.scope || 'both') !== 'part') return null;
    if (c.op === 'readpt') return '#graph .gtarget';
    if (['solid', 'dashed', 'test', ...TVERDICT, ...SHADE].includes(c.op) || (c.op === 'trap' && c.rowCard)) return ROWSEL + ', #graph .gtarget';
    return ROWSEL;
  }
  // Where a ◎ card could go (its own kind of place), so a card with one place applies by itself.
  function places(e, c) {
    if (e.k5 === 'ineq5') {
      if (c.op === 'solid' || c.op === 'dashed' || (c.op === 'trap' && c.rowCard)) return [0, 1].filter(i => !e.st[i].line);
      if (TVERDICT.includes(c.op)) return [0, 1].filter(i => e.st[i].tested && !e.st[i].shade);
      if (SHADE.includes(c.op) || c.op === 'test') return [0, 1].filter(i => e.st[i].line && !e.st[i].shade);
      return null;
    }
    if (e.work) return null;
    switch (c.op) {
      case 'subst': return [0, 1].filter(i => hasL(e.eqs[i], c.v) && aloneIn(e.eqs[1 - i], c.v));
      case 'move': return [0, 1].filter(i => !isStd(e.eqs[i]));
      case 'iso': case 'plugv': case 'scale': return [0, 1];
      case 'trap': return c.rowCard ? [0, 1] : null;
    }
    return null;
  }
  function autoTarget(c) {
    if (!cur || !cur.act5) return 'pass';
    if (!c.a5 && !(c.op === 'trap' && c.a5)) {
      // Combine inside a formula: its own kind of place (like terms on one side), so one pair applies by itself
      if (c.f4 && c.op === 'comb' && cur.state.work && cur.state.work.k4 === 'formula') {
        const w = cur.state.work, refs = [];
        for (const s of ['L', 'R']) { const seen = new Set(); w[s].forEach((t, i) => { if (t.g) return; const k = K.keyT(t); if (w[s].filter(o => !o.g && K.keyT(o) === k).length >= 2 && !seen.has(k)) { seen.add(k); refs.push(s + i); } }); }
        if (refs.length >= 2) return undefined;
        return refs.length ? $('equation').querySelector(`.tok[data-ref="${refs[0]}"]`) : null;
      }
      return 'pass';
    }
    if (c.scope !== 'part') return 'pass';
    if (c.op === 'readpt') return undefined;
    const ps = places(cur.state, c);
    if (!ps) return null;                                  // a verdict or a statement about the whole system
    if (ps.length >= 2) return undefined;
    if (!ps.length) return null;
    return document.querySelector(`#equation .tok[data-row="${ps[0]}"]:not(.eq), #a4top .tok[data-row="${ps[0]}"]`) || 'q' + ps[0];
  }
  // While a card is held, the places it can go glow (Easy and Normal, or Hard after a wrong move).
  function onDrag(c, on) {
    document.querySelectorAll('.ok5').forEach(el => el.classList.remove('ok5'));
    if (!on || !cur || !cur.act5) return;
    const sel = targetSel(c); if (!sel) return;
    const hl = difficulty.highlight === 'on' || isTutorial() || (difficulty.highlight === 'afterWrong' && cur.wrong > 0);
    if (!hl) return;
    for (const el of document.querySelectorAll(sel)) if (el.dataset.ref && correct5(cur.state, c, el)) el.classList.add('ok5');
  }

  // ---------------------------------------------------------------- hands
  const DECOYS = [1, 1, 2, 2];
  function candRefs(e) {
    const out = ['q0', 'q1', null, 'P0', 'P1', 'P2', 'P3'];
    return out;
  }
  const alsoRight = (e, c) => candRefs(e).some(r => correct5(e, c, r));
  function trap(name, lbl, txt, why, iconKey, extra = {}) { return { op: 'trap', a5: true, trap: name, scope: 'part', label: lbl, text: txt, why, icon: iconKey, ...extra }; }
  // Rule decoys (classic mistakes, dealt at every level outside tutorials) and Expert traps.
  function specials(e, correct) {
    const out = { rule: [], traps: [] };
    if (e.k5 === 'ineq5') {
      const i = [0, 1].find(j => !e.st[j].line);
      if (i !== undefined) {
        const r = e.rows[i];
        if (!strict(r.rel)) out.traps.push(trap('dashed for ≤', `Dashed for ${r.rel}`, `Draw ${r.rel} dashed: it isn't strictly ${r.rel === '≤' ? 'less' : 'greater'}`,
          P(`${r.rel} means "${r.rel === '≤' ? 'less than' : 'greater than'} <b>or equal to</b>", so points on the line count: the boundary is solid. Only < and > (no "or equal") get a dashed line.`), 'dashed5', { rowCard: true }));
      }
      return out;
    }
    if (e.work && isStmt(e.work)) {
      out.rule.push(trap('zero answer', '(0, 0)', `${stmtText(e.work)}, so the answer is x = 0, y = 0`,
        P(`${stmtText(e.work)} has no x or y in it at all: it doesn't say what x or y are. It's a statement that is ${stmtTrue(e.work) ? 'always true, so every point on the line works: infinitely many solutions' : 'never true, so no point works: no solution'}.`), 'none'));
      return out;
    }
    if (e.work) return out;
    if (correct.op === 'subst') {
      const into = e.eqs[correct.row], expr = exprOf(e.eqs[1 - correct.row], correct.v), k = coefOf(into, correct.v);
      if (expr.length >= 2 && !isUnit(k)) {
        const ex = sideText(expr);
        out.rule.push(trap('no brackets', `Sub ${correct.v}<span class="ftag">no ( )</span>`, `Substitute ${correct.v} = ${ex} without brackets`,
          P(`${correct.v} is the whole expression ${ex}, so it goes in brackets: ${fracText(k)}(${ex}). Without them, ${fracText(k)} would only multiply the first term.`) + P('<b>The rule:</b> a substituted expression always goes in brackets.'), 'subst5'));
      }
    }
    if (correct.op === 'move') {      // the classic slip: the term's own sign instead of the opposite one
      const bad = { ...correct, sgn: correct.sgn === '+' ? '-' : '+' };
      out.rule.push(bad);
    }
    if (correct.op === 'scale') {
      const lt = correct.col === 'a' ? 'x' : 'y';
      out.rule.push(trap('one term', `${TIMES}${correct.k} ${lt}-term`, `Multiply only the ${lt}-term by ${correct.k}`,
        P(`Multiplying an equation means <b>every</b> term, on both sides: 2x + y = 5 times 3 is 6x + 3y = 15. Changing only the ${lt}-term makes a different equation (a different line), so the answer would be wrong.`), 'scale5', { rowCard: true }));
    }
    if (correct.op === 'addeq' || correct.op === 'subeq' || correct.op === 'move') {
      out.traps.push(trap('add unlike', 'Add x and y', 'Combine the x- and y-terms: 2x + 3y = 5xy',
        P('x-terms and y-terms are unlike terms: 2x + 3y can\'t be combined. Elimination works column by column, x with x and y with y.'), 'comb'));
    }
    // Playtest fix: this trap also came up before any letter was found ("Stop here: y is the answer" on a
    // fresh system). It only makes sense once one value is known.
    if (correct.op === 'plugv' && (e.vals.x !== null || e.vals.y !== null)) {
      out.traps.push(trap('half done', 'Done!', `Stop here: ${e.vals.x !== null ? 'x' : 'y'} = ${fracText(e.vals.x !== null ? e.vals.x : e.vals.y)} is the answer`,
        P('A system asks for a point (x, y): both letters. Plug the value you found back in to get the other one.'), 'none'));
    }
    return out;
  }
  function family(e, correct) {
    if (e.k5 === 'ineq5') {
      const f = ['solid', 'dashed', 'above', 'below'].map(op => C5(op));
      if (e.rows.some(r => fz(std(r).b))) f.push(C5('left'), C5('right'));
      f.push(C5('test', { p: O }));
      const pend = pendingTest(e);
      if (pend !== undefined) f.push(...TVERDICT.map(op => C5(op, { p: e.st[pend].tested })));
      if (e.askPt) f.push(C5('yes'), C5('no'));
      return f;
    }
    if (e.work && isStmt(e.work)) return [C5('snone'), C5('sall'), C5('sone'), C5('addeq'), C5('subeq')];
    if (e.ask === 'count') return [C5('iso', { v: 'y' }), C5('iso', { v: 'x' }), C5('slopes'), C5('sone'), C5('snone'), C5('sall'), C5('readpt')];
    if (e.ask === 'graph') return [C5('readpt'), C5('sone'), C5('snone'), C5('sall'), C5('subst', { v: 'y' }), C5('addeq')];
    const f = [C5('iso', { v: 'x' }), C5('iso', { v: 'y' }), C5('subst', { v: 'x' }), C5('subst', { v: 'y' }), C5('addeq'), C5('subeq')];
    // Both-sides moves for the terms of an equation that isn't lined up, with both signs (one is wrong)
    if (e.method !== 'sub') e.eqs.forEach((q, i) => { if (isStd(q)) return; for (const t of [...q.L, ...q.R]) if (!t.g && !fz(t.k)) for (const sg of ['+', '-']) f.push(C5('move', { sgn: sg, t: { k: fAbs(t.k), lit: t.lit || '', den: '' } })); });
    const ks = new Set([2, 3]);
    for (const q of e.eqs) { const s = std(q); for (const k of [s.a, s.b]) { const n = Math.abs(fv(k)); if (Number.isInteger(n) && n >= 2 && n <= 9) ks.add(n); } }
    ks.forEach(k => f.push(C5('scale', { k })));
    for (const v of LET) if (e.vals[v] !== null) f.push(C5('plugv', { v, val: e.vals[v] }));
    if (isUnlocked('special5')) f.push(C5('snone'), C5('sall'));
    return f;
  }
  function ownHand(e, correct, size) {
    const tut = isTutorial(), L = lvl();
    const hand = [correct], seen = new Set([cardLabel(correct)]);
    const add = c => { if (hand.length >= size) return; const k = cardLabel(c); if (seen.has(k)) return; if (c.op !== 'trap' && alsoRight(e, c)) return; seen.add(k); hand.push(c); };
    const sp = specials(e, correct);
    if (TVERDICT.includes(correct.op)) add(C5(correct.op === 'ttrue' ? 'tfalse' : 'ttrue', { p: correct.p }));   // true or false: both always in the hand
    if (!tut && L >= 3) sp.traps.slice(0, 1).forEach(add);
    if (!tut) sp.rule.slice(0, DECOYS[L]).forEach(add);
    shuffle(family(e, correct)).forEach(add);
    return shuffle(hand);
  }
  function makeHand5(e, correct, size) {
    if (e.k5 === 'sys' && e.work && !isStmt(e.work)) {
      const w = e.work;
      return w.k4 === 'formula' ? fHand(w, correct, size) : A2.makeHand(w, correct, size);
    }
    return ownHand(e, correct, size);
  }

  // ================================================================ wrong moves
  const S = (long, short, more) => (long ? P(more || short) : short);
  const rowName = i => ROWLAB[i] || 'that equation';
  function why5(e, card, target, long) {
    const ref = refOf(target), want = canon5(e), i = rowOf(ref);
    if (card.op === 'trap') return long ? card.why : 'That\'s a trap: it isn\'t true. Tap Why? to see why.';
    if (e.k5 === 'ineq5') return whyI(e, card, i, want, long);
    if (e.work) return whyWork(e, card, target, ref, want, long);
    const opts = options(e);
    if (VERDICT.includes(card.op)) {
      if (e.ask === 'count') {
        if (!e.eqs.every(q => aloneIn(q, 'y'))) return S(long, 'Get y alone in both equations first.', 'To compare the lines, write both as y = mx + b first: then m is the slope and b is where the line crosses the y-axis.');
        return S(long, countWhy(e, true), countWhy(e, false));
      }
      if (e.ask === 'graph') return S(long, 'The lines on the graph do cross: read the point where they meet.');
      return S(long, 'Keep solving: you can only tell once a letter is gone.', 'You can only declare no solution or infinitely many when the letters cancel and leave a statement like 0 = 5 or 0 = 0. Keep solving.');
    }
    if (e.ask === 'count') {
      if (card.op === 'iso' && i >= 0 && aloneIn(e.eqs[i], 'y')) return S(long, `${rowName(i)} already has y alone.`);
      if (card.op === 'iso' && card.v === 'x') return S(long, 'Get y alone, not x: y = mx + b shows the slope.');
      if (card.op === 'slopes' && !e.eqs.every(q => aloneIn(q, 'y'))) return S(long, 'Get y alone first.', 'The number in front of x is only the slope once y is alone: y = mx + b. Solve that equation for y first.');
      if (card.op === 'slopes') return S(long, 'The slopes are already side by side: decide how many solutions.');
      return S(long, 'Compare the slopes and intercepts.', 'Different slopes: the lines cross once. Same slope, different b: parallel, never meet. Same slope and same b: the same line.');
    }
    if (e.ask === 'graph') {
      if (card.op === 'readpt' && ref) {
        const p = e.cands[+String(ref).slice(1)];
        if (p) {
          const on = e.eqs.map(q => onLine(q, p));
          return S(long, on[0] || on[1] ? `${ptText(p)} is only on line ${on[0] ? '①' : '②'}. The solution is on both.` : `${ptText(p)} isn't on either line.`,
            `${ptText(p)} ${on[0] || on[1] ? `is on line ${on[0] ? '①' : '②'} only` : 'isn\'t on either line'}. The solution of a system is the point that works in both equations: where the two lines cross.`);
        }
      }
      return S(long, 'Read the point where the two lines cross.', 'Solving by graphing: the solution is the point on both lines, where they cross. Drop Crossing point on it.');
    }
    const kn = LET.filter(v => e.vals[v] !== null);
    if (card.op === 'plugv') {
      if (!kn.length) return S(long, 'Nothing is known yet: find x or y first.');
      const u = other(card.v);
      if (i >= 0 && !hasL(e.eqs[i], u)) return S(long, `${rowName(i)} has no ${u} in it to find.`);
      return S(long, 'Drop it on an equation.');
    }
    if (kn.length === 1) {
      const v = kn[0];
      return S(long, `You know ${v} = ${fracText(e.vals[v])}: plug it back in to find ${other(v)}.`, `${v} = ${fracText(e.vals[v])} is half the answer. Plug it into either equation (Plug ${v} = ${fracText(e.vals[v])} back in) and solve for ${other(v)}.`);
    }
    const subWay = e.method !== 'elim', elimWay = e.method !== 'sub';
    if (card.op === 'subst') {
      if (!subWay) return S(long, 'Use elimination here: line up the columns and add or subtract.', 'This enemy asks for elimination: make one column cancel (multiply an equation if needed), then add or subtract the equations.');
      const src = [0, 1].find(j => aloneIn(e.eqs[j], card.v));
      if (src === undefined) return S(long, `No equation has ${card.v} alone yet.`, `Substitution puts an expression for ${card.v} into the other equation, so first one equation must read ${card.v} = ... . Get a letter alone first (Solve for), picking one with no number in front.`);
      if (i === src) return S(long, `That's where ${card.v} came from: put it into the other equation.`, `Putting ${card.v}'s expression back into the equation it came from just gives ${card.v} = ${card.v}, which tells you nothing. Substitute into the <b>other</b> equation.`);
      return S(long, `Substitute ${opts[0] && opts[0].v ? opts[0].v : 'the other letter'} instead.`);
    }
    if (card.op === 'iso') {
      if (!subWay) return S(long, 'Use elimination here.', 'This enemy asks for elimination: line up the columns, make one column cancel, then add or subtract.');
      const src = [0, 1].find(j => aloneV(e.eqs[j]));
      if (src !== undefined) return S(long, `${rowName(src)} already has ${aloneV(e.eqs[src])} alone: substitute it.`);
      if (i >= 0) {
        const k = coefOf(e.eqs[i], card.v);
        if (!isUnit(k)) return S(long, `${card.v} has ${fracText(fAbs(k))} in front there: that means fractions.`, `Getting ${card.v} alone in ${rowName(i)} means dividing by ${fracText(fAbs(k))}, which makes fractions. Pick a letter that has no number in front (just 1 or ${MINUS}1).`);
      }
      return S(long, 'Pick a letter with no number in front.');
    }
    if (card.op === 'addeq' || card.op === 'subeq') {
      if (!elimWay) return S(long, 'Use substitution here.', 'This enemy asks for substitution: get a letter alone, then put its expression into the other equation.');
      if (!e.eqs.every(isStd)) return S(long, 'Line the equations up first.', 'To add or subtract equations, x must sit over x and y over y, with the numbers on the right. Move the terms that are on the wrong side first: add or subtract them on both sides.');
      const s = sumCols(e.eqs, card.op === 'addeq' ? 1 : -1), s0 = std(e.eqs[0]), s1 = std(e.eqs[1]);
      const res = `${fracText(s.a)}x + ${fracText(s.b)}y`.replace('+ ' + MINUS, MINUS + ' ');
      const other_ = sumCols(e.eqs, card.op === 'addeq' ? -1 : 1);
      if (fz(other_.a) || fz(other_.b)) {
        const col = fz(other_.a) ? 'a' : 'b', L_ = col === 'a' ? 'x' : 'y';
        return card.op === 'addeq'
          ? S(long, `${fracText(s0[col])}${L_} and ${fracText(s1[col])}${L_} have the same sign: adding doesn't cancel them. Subtract.`, `Adding gives ${res}: nothing cancels. ${fracText(s0[col])}${L_} and ${fracText(s1[col])}${L_} are the same, so <b>subtracting</b> cancels them (same signs subtract, opposite signs add).`)
          : S(long, `${fracText(s0[col])}${L_} and ${fracText(s1[col])}${L_} are opposites: subtracting doesn't cancel them. Add.`, `Subtracting gives ${res}: nothing cancels. ${fracText(s0[col])}${L_} and ${fracText(s1[col])}${L_} are opposites, so <b>adding</b> cancels them.`);
      }
      return S(long, `That gives ${res}: no column cancels. Multiply an equation first.`, `${card.op === 'addeq' ? 'Adding' : 'Subtracting'} gives ${res}, which still has both letters. First multiply one equation (or both) so the x's or the y's have the same number in front.`);
    }
    if (card.op === 'scale') {
      if (!elimWay) return S(long, 'Use substitution here.');
      if (!e.eqs.every(isStd)) return S(long, 'Line the equations up first.');
      if (opts.some(o => o.op === 'addeq' || o.op === 'subeq')) return S(long, 'A column already cancels: add or subtract now.', 'One column already has matching numbers, so adding or subtracting the equations cancels it right away. No need to multiply.');
      if (i < 0) return S(long, 'Drop it on one equation.');
      const sc = std(scaleEq(e.eqs[i], card.k)), o = std(e.eqs[1 - i]);
      return S(long, `${TIMES}${card.k} makes ${fracText(sc.a)}x and ${fracText(sc.b)}y: neither matches ${fracText(o.a)}x or ${fracText(o.b)}y.`,
        `Multiplying ${rowName(i)} by ${card.k} gives ${fracText(sc.a)}x and ${fracText(sc.b)}y. To eliminate, one column must match the other equation's (${fracText(o.a)}x, ${fracText(o.b)}y), same number or opposite. Look for a number that turns one into the other.`);
    }
    if (card.op === 'move') {
      if (i >= 0 && isStd(e.eqs[i])) return S(long, `${rowName(i)} is already lined up: x and y on the left, the number on the right.`);
      if (!elimWay) return S(long, 'Use substitution here.', 'This enemy asks for substitution: get a letter alone, then put its expression into the other equation. There is nothing to line up.');
      const q = i >= 0 ? e.eqs[i] : null, tt = moveTerm(card);
      const on = q ? [...q.L, ...q.R].find(o => !o.g && o.lit === card.t.lit && fEq(fAbs(o.k), card.t.k)) : null;
      if (on) {
        const onL = q.L.includes(on), wrongSide = !!on.lit === !onL;
        if (!wrongSide) return S(long, `${fTermStr(on, true, false, '')} is already on the right side of the equals sign.`, `For elimination each equation reads x-term, y-term = number. ${fTermStr(on, true, false, '')} is already where it belongs, so leave it there and move the term that isn't.`);
        const sum = fTermStr({ k: fAdd(on.k, card.sgn === '+' ? card.t.k : fNeg(card.t.k)), lit: on.lit, den: '' }, true, false, '');
        return S(long, `${fTermStr(on, true, false, '')} ${card.sgn === '+' ? '+' : MINUS} ${tt} doesn't cancel: use the opposite sign.`, `To clear ${fTermStr(on, true, false, '')} from its side, do the opposite: ${on.k.n > 0 ? 'subtract' : 'add'} ${tt} on both sides. ${card.sgn === '+' ? 'Adding' : 'Subtracting'} it gives ${sum} instead of 0.`);
      }
      return S(long, 'That term isn\'t in this equation.', 'Move a term that is on the wrong side of this equation: a letter on the right, or a number on the left.');
    }
    if (card.op === 'slopes' || card.op === 'readpt') return S(long, 'Solve it with algebra: substitution or elimination.');
    return S(long, 'That card doesn\'t fit here.');
  }
  function countWhy(e, short) {
    const l0 = lineOf(e.eqs[0]), l1 = lineOf(e.eqs[1]), v = countVerdict(e);
    const ms = `slopes ${fracText(l0.m)} and ${fracText(l1.m)}`;
    if (v === 'sone') return short ? `Different ${ms}: the lines cross once.` : `The ${ms} are different, so the lines aren't parallel: they cross at exactly one point. <b>One solution.</b>`;
    if (v === 'snone') return short ? 'Same slope, different y-intercepts: parallel lines.' : `Both slopes are ${fracText(l0.m)} but the y-intercepts are ${fracText(l0.b)} and ${fracText(l1.b)}: parallel lines that never meet. <b>No solution.</b>`;
    return short ? 'Same slope and same y-intercept: the same line.' : `Same slope (${fracText(l0.m)}) and the same y-intercept (${fracText(l0.b)}): both equations are the same line, so every point on it works. <b>Infinitely many solutions.</b>`;
  }
  function whyWork(e, card, target, ref, want, long) {
    const w = e.work;
    if (isStmt(w)) {
      const t = stmtTrue(w), st = stmtText(w);
      if (VERDICT.includes(card.op)) {
        if (card.op === 'sone') return S(long, `The letters are gone, so the lines don't cross at one point.`, `${st} has no x or y left. One solution would end with x = a number. Here it's ${t ? 'always true: the same line, infinitely many solutions' : 'never true: parallel lines, no solution'}.`);
        return t ? S(long, `${st} is always true: every point on the line works.`, `${st} is true no matter what x and y are. Both equations are the same line, so there are <b>infinitely many solutions</b>.`)
          : S(long, `${st} is never true: no point works.`, `${st} is false whatever x and y are. The lines are parallel and never meet: <b>no solution</b>.`);
      }
      return S(long, `x and y are gone. Is ${st} true or false?`);
    }
    const what = w.k4 === 'formula' ? `getting ${w.v} alone in ${rowName(w.row)}` : `solving for ${w.v}`;
    if (card.a5) return S(long, `First finish ${what}.`, `You're in the middle of ${what}: ${w.k4 === 'formula' ? K.fText(w) : A2.eqText(w)}. Finish that first.`);
    if (w.k4 === 'formula') return card.f4 ? fWhy(w, card, ref, want, long) : S(long, `First finish ${what}.`);
    const fakeCur = { state: w, path: [{ move: want }], step: 0 };
    if (!long) return A2.whyWrong(fakeCur, card, target);
    for (const fn of WHY_EXPLAINERS) { if (fn === explain5 || fn === K.explain4) continue; const h = fn({ state: w, card, correct: want, ref }); if (h) return h; }
    return null;
  }
  function whyI(e, card, i, want, long) {
    const r = e.rows[i], st = e.st[i];
    if (card.op === 'yes' || card.op === 'no') {
      if (!e.st.every(s => s.shade)) return S(long, 'Shade both inequalities first.');
      const p = e.askPt, bad = e.rows.findIndex(rr => !inRow(rr, p));
      if (bad < 0) return S(long, `${ptText(p)} is in both shaded regions: it is a solution.`, `${ptText(p)} makes both inequalities true, so it's in the overlap: it <b>is</b> a solution.`);
      const rr = e.rows[bad];
      if (onLine(rr, p)) return S(long, `${ptText(p)} is on the dashed line of ${rowName(bad)}: not included.`, `${ptText(p)} sits right on the boundary of ${rowName(bad)}, and that boundary is dashed (${rr.rel}): points on it don't count. Not a solution.`);
      return S(long, `${ptText(p)} isn't in the shaded side of ${rowName(bad)}.`, `Plug ${ptText(p)} into ${rowName(bad)}: ${eqText(rr, rr.rel)} is false there. A solution of the system must be in <b>both</b> shaded regions.`);
    }
    if (card.op === 'solid' || card.op === 'dashed') {
      if (i < 0) return S(long, 'Drop it on an inequality.');
      if (st.line) return S(long, `${rowName(i)}'s boundary is already drawn.`);
      return strict(r.rel) ? S(long, `${r.rel} doesn't include the line: draw it dashed.`, `${r.rel} means strictly ${r.rel === '<' ? 'less' : 'greater'}: points on the line don't count, so the boundary is <b>dashed</b>. ≤ and ≥ ("or equal to") get a solid line.`)
        : S(long, `${r.rel} includes the line: draw it solid.`, `${r.rel} means "or equal to", so points on the line count: the boundary is <b>solid</b>. Only < and > get a dashed line.`);
    }
    const pend = pendingTest(e);
    if (TVERDICT.includes(card.op)) {
      if (pend === undefined) return S(long, 'Test a point first.', 'True and False answer a test point: plug a point that is not on the line into the inequality, then say whether it makes it true.');
      const rr = e.rows[pend], p = e.st[pend].tested, v = inRow(rr, p), { a, b, c: cc } = std(rr);
      const lhs = `${fracText(a)}(${fracText(p.x)}) + ${fracText(b)}(${fracText(p.y)})`.replace('+ ' + MINUS, MINUS + ' ');
      const val = fracText(fAdd(fMul(a, p.x), fMul(b, p.y))), cmp = `${val} ${rr.rel} ${fracText(cc)}`;
      return S(long, `${cmp} is ${v ? 'true' : 'false'}.`, `Plug ${ptText(p)} into ${rowName(pend)}: ${lhs} = ${val}, and ${cmp} is <b>${v ? 'true' : 'false'}</b>. ${v ? `So ${ptText(p)} is on the side to shade.` : `So ${ptText(p)} is on the wrong side: shade the other side.`}`);
    }
    if (pend !== undefined) return S(long, `You tested ${ptText(e.st[pend].tested)}: is it true or false?`, `You plugged ${ptText(e.st[pend].tested)} into ${rowName(pend)}. Decide first: does it make the inequality true or false? That tells you which side to shade.`);
    if (SHADE.includes(card.op) || card.op === 'test') {
      if (i < 0) return S(long, 'Drop it on an inequality (or its line).');
      if (!st.line) return S(long, `Draw ${rowName(i)}'s boundary line first.`);
      if (st.shade) return S(long, `${rowName(i)} is already shaded.`);
      if (card.op === 'test') return S(long, `${ptText(card.p)} is on the line, so it can't pick a side.`, `${ptText(card.p)} lies right on ${rowName(i)}'s boundary, so testing it can't tell you which side to shade. Test a point that isn't on the line, or read the side off with y alone.`);
      const side = sideOf(r), vert = fz(std(r).b);
      if (vert !== (card.op === 'left' || card.op === 'right')) return S(long, vert ? 'This boundary is vertical: shade left or right.' : 'Left and right are for a vertical line, x = a number.');
      if (r.form === 'std') {
        const { b } = std(r);
        return S(long, `Careful: in ${eqText(r, r.rel)} y isn't alone. Test a point.`, `In ${eqText(r, r.rel)} y isn't alone${b.n < 0 ? ' and has a minus sign' : ''}, so ${r.rel} doesn't directly say above or below. Get y alone (dividing by a negative flips the sign) or test a point like (0, 0). Here the solution is <b>${side}</b> the line.`);
      }
      if (vert) return S(long, `${eqText(r, r.rel)} is everything to the ${side} of the line.`);
      return S(long, `y ${r.rel} ... means y-values ${side} the line.`, `With y alone, ${r.rel} ${geRel(r.rel) ? 'means bigger y-values: <b>above</b>' : 'means smaller y-values: <b>below</b>'} the line.`);
    }
    return S(long, 'That card doesn\'t fit here.');
  }
  const isCorrect = (cur, card, target) => correct5(cur.state, card, target);
  const whyWrong = (cur, card, target) => why5(cur.state, card, target, false);
  function explain5({ state: e, card, ref }) {
    if (!e || !e.k5 || !card) return null;
    return why5(e, card, ref, true);
  }
  if (typeof registerWhy === 'function') registerWhy(explain5);

  // ================================================================ rendering
  function tok5(html, ref, row, cls = '') { const d = TOK(html, 't5', ref, 't5 ' + cls); d.dataset.row = row; return d; }
  function rowsEl(rows) {
    const wrap = document.createElement('div'); wrap.className = 'sys5wrap';
    const brace = document.createElement('div'); brace.className = 'brace5';
    const grid = document.createElement('div'); grid.className = 'rows5';
    rows.forEach((q, i) => {
      const lab = document.createElement('div'); lab.className = 'lab5 r' + i; lab.textContent = ROWLAB[i];
      const side = (s, items) => {
        const box = document.createElement('div'); box.className = 'side5 ' + s;
        if (!items.length) box.appendChild(tok5('0', `q${i}${s}z`, i));
        items.forEach((t, j) => { const d = tok5(fTermStr(t, j === 0, true, ''), `q${i}${s}${j}`, i); d.dataset.side = s; d.dataset.lit = t.lit || ''; box.appendChild(d); });
        return box;
      };
      const rel = EQTOK(q.rel || '='); rel.dataset.row = i; if (q.rel && q.rel !== '=') rel.classList.add('rel');
      grid.append(lab, side('L', q.L), rel, side('R', q.R));
    });
    wrap.append(brace, grid);
    return wrap;
  }
  // Two rows are fitted together: the widest row fits the width and both rows fit the height.
  function fit5() {
    const el = $('equation'), w = el.querySelector('.sys5wrap'); if (!w) return;
    el.style.removeProperty('--eqSize');
    const base = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--eqSize')) || 56;
    let size = Math.round(base * 0.82);
    el.style.setProperty('--eqSize', size + 'px');
    const maxH = Math.max(80, ($('arena').clientHeight || 400) * (innerWidth <= 640 ? 0.34 : 0.42));
    el.classList.add('fitting');
    for (let i = 0; i < 10; i++) {
      const availW = el.clientWidth * 0.94, needW = w.scrollWidth, needH = w.offsetHeight;
      const f = Math.min(availW && needW > availW ? availW / needW : 1, needH > maxH ? maxH / needH : 1);
      if (f >= 0.99) break;
      size = Math.max(12, Math.floor(size * Math.min(0.97, f)));
      el.style.setProperty('--eqSize', size + 'px');
      if (size <= 12) break;
    }
    el.classList.remove('fitting');
  }
  const fitA2 = () => { $('equation').classList.add('a2'); if (A2.fitEq) A2.fitEq(); };
  const valsHtml = e => (e.k5 === 'sys' && (e.vals.x !== null || e.vals.y !== null) && !e.done
    ? ` <span class="vals5">${LET.map(v => `<i>${v}</i> = ${e.vals[v] === null ? '<span class="slot4">?</span>' : `<b>${fracHtml(e.vals[v])}</b>`}`).join(' · ')}</span>` : '');
  function topRows(e, note = '') {
    const rows = e.k5 === 'ineq5' ? e.rows : e.eqs;
    const html = rows.map((q, i) => `<span class="lab5 r${i}">${ROWLAB[i]}</span><span class="tok a4 t5top" data-row="${i}" data-ref="q${i}">${eqHtml(q, q.rel || '=')}</span>`).join(' ');
    banner(`<span class="sys5top">${html}</span>${valsHtml(e)}${note ? `<span class="note5">${note}</span>` : ''}`);
  }
  function statusBanner(e) {
    if (e.ask === 'count' && e.shown) {
      const ls = e.eqs.map(lineOf);
      banner(ls.map((l, i) => `<span class="lab5 r${i}">${ROWLAB[i]}</span> <i>m</i> = <b>${fracHtml(l.m)}</b>, <i>b</i> = <b>${fracHtml(l.b)}</b>`).join(' &nbsp; '));
      return;
    }
    const v = valsHtml(e);
    if (v) banner(v);
  }
  function resultHtml(e) {
    if (e.verdict === 'snone') return `${e.stmt ? e.stmt + ' → ' : ''}No solution`;
    if (e.verdict === 'sall') return `${e.stmt ? e.stmt + ' → ' : ''}Infinitely many`;
    if (e.verdict === 'sone') return 'One solution';
    return `(<i>x</i>, <i>y</i>) = (${fracHtml(e.vals.x)}, ${fracHtml(e.vals.y)})`;
  }
  // The graph: lines ① and ② (with a dot where they cross once solved); for inequalities, the drawn
  // boundaries, the shading and the overlap.
  function winFor(e) {
    if (e.win) return e.win;
    const xs = [], ys = [];
    for (const q of e.eqs) { const l = lineOf(q); if (!l) continue; if (l.x !== undefined) xs.push(l.x); else { ys.push(l.b); if (!fz(l.m)) xs.push(fDiv(fNeg(l.b), l.m)); } }
    if (e.done && e.vals.x !== null) { xs.push(e.vals.x); ys.push(e.vals.y); }
    const clampF = f => F(Math.max(-14, Math.min(14, Math.round(fv(f)))));
    return K.windowFor(xs.map(clampF), ys.map(clampF));
  }
  function graphOf(e) {
    if (e.k5 === 'ineq5') {
      const lines = [], marks = [];
      e.rows.forEach((r, i) => {
        const st = e.st[i]; if (!st.line) return;
        lines.push({ ...lineOf(r), dash: st.line === 'dashed', cls: 'g5 g5r' + i, lab: ROWLAB[i], ref: true, tref: 'q' + i });
        if (st.shade) marks.push(halfOf(r, i));
        else if (st.tested) marks.push({ t: 'dot', x: st.tested.x, y: st.tested.y, lab: ptText(st.tested), cls: 'test5' });
      });
      if (e.st.every(s => s.shade)) marks.push({ t: 'overlap', a: halfOf(e.rows[0], 0), b: halfOf(e.rows[1], 1) });
      if (e.askPt) marks.push({ t: 'dot', x: e.askPt.x, y: e.askPt.y, lab: ptText(e.askPt), cls: 'ask5' });
      return { win: e.win, pts: [], lines, marks, labels: false, qid: e.qid };
    }
    const show = e.ask === 'graph' || e.done;
    if (!show) return null;
    const lines = e.eqs.map((q, i) => ({ ...lineOf(q), cls: 'g5 g5r' + i, lab: ROWLAB[i] }));
    const marks = [];
    if (e.done && e.vals.x !== null) marks.push({ t: 'dot', x: e.vals.x, y: e.vals.y, lab: `(${fracText(e.vals.x)}, ${fracText(e.vals.y)})` });
    const pts = e.ask === 'graph' && !e.done ? e.cands : [];
    return { win: winFor(e), pts, lines, marks, labels: false, targets: e.ask === 'graph' && !e.done, qid: e.qid };
  }
  function render(e) {
    const el = $('equation'); if (typeof clearNotes === 'function') clearNotes();
    el.innerHTML = ''; el.classList.add('a4', 'sys5');
    const g = graphOf(e); if (g) drawGraph(g);
    if (e.k5 === 'ineq5') { el.appendChild(rowsEl(e.rows)); fit5(); return; }
    if (e.done) {
      topRows(e); el.classList.remove('sys5');
      el.appendChild(TOK(resultHtml(e), 'res5', null, 'res5')); fitA2(); return;
    }
    if (e.work) {
      const w = e.work;
      topRows(e, w.k4 === 'formula' ? `Getting ${w.v} alone in ${ROWLAB[w.row]}` : isStmt(w) ? 'The letters cancelled' : `Solve for ${w.v}`);
      el.classList.remove('sys5');
      if (w.k4 === 'formula') { K.renderFormula(w); fitA2(); } else A2.render(w);
      return;
    }
    statusBanner(e);
    el.appendChild(rowsEl(e.eqs)); fit5();
  }
  function clear() {
    const el = $('equation'); if (el) el.classList.remove('sys5');
    document.querySelectorAll('.fly5').forEach(n => n.remove());
  }
  const fontPx = () => parseFloat(getComputedStyle($('equation')).fontSize);
  function prefit(s, ns) {
    const a = s.k5 === 'sys' ? s.work : null, b = ns.k5 === 'sys' ? ns.work : null;
    if (a && b && !a.k4 && !b.k4 && !isStmt(b)) { render(s); A2.prefit(a, b); return; }
    render(ns); const after = fontPx(); render(s); const before = fontPx();
    if (before > after + 0.5) {
      const el = $('equation'), c = parseFloat(el.style.getPropertyValue('--eqSize')) || 56;
      el.style.setProperty('--eqSize', Math.floor(c * after / before) + 'px');
    }
  }
  addEventListener('resize', () => { if (!cur || !cur.act5 || (typeof animating !== 'undefined' && animating)) return; if ($('equation').classList.contains('sys5')) fit5(); });

  // ================================================================ prompts
  const PR = {
    sub: ['Solve the system by substitution.', 'Use substitution to solve the system.', 'Solve by substitution.'],
    elim: ['Solve the system by elimination.', 'Use elimination to solve the system.', 'Solve by elimination.'],
    any: ['Solve the system.', 'Solve the system of equations.', 'Find the solution of the system.'],
    count: ['How many solutions does the system have?', 'Does the system have one solution, no solution, or infinitely many?'],
    graph: ['Solve the system by graphing.', 'Use the graph to solve the system.', 'Where do the two lines cross? Solve by graphing.'],
    ineq: ['Graph the system of inequalities.', 'Graph the solution set of the system.', 'Shade the solution of the system.'],
  };
  const lastPr = {};
  function prompt(s) {
    let key = s.k5 === 'ineq5' ? 'ineq' : s.ask === 'solve' ? s.method : s.ask;
    let all = PR[key].slice();
    if (s.k5 === 'sys' && s.ask === 'solve' && s.skill === 'special5') all = all.filter(t => !t.startsWith('Find'));
    const fresh = all.filter(t => t !== lastPr[key]);
    let t = (lastPr[key] = pick(fresh.length ? fresh : all));
    if (s.k5 === 'ineq5' && s.askPt) t += ` Is <i>${ptText(s.askPt)}</i> a solution?`;
    return t;
  }

  // ================================================================ animations
  // The game's timing: the written operation fades in fast, hold() (scaled by the speed setting), the
  // calculation runs fast (quick()), the result shows, hold().
  const eqq = sel => $('equation').querySelector(sel);
  const rowToks = i => [...$('equation').querySelectorAll(`.tok[data-row="${i}"]:not(.eq)`)];
  async function fly(html, fromEl, toEl, ms = 450) {
    if (!fromEl || !toEl) return;
    const from = fromEl.getBoundingClientRect(), dest = toEl.getBoundingClientRect();
    const chip = document.createElement('div'); chip.className = 'fly4 fly5'; chip.innerHTML = html;
    chip.style.left = (from.left + from.width / 2) + 'px'; chip.style.top = (from.top + from.height / 2) + 'px';
    document.body.appendChild(chip); void chip.offsetWidth;
    chip.style.transform = `translate(${dest.left + dest.width / 2 - from.left - from.width / 2}px, ${dest.top + dest.height / 2 - from.top - from.height / 2}px)`;
    await quick(ms); chip.remove();
  }
  async function animIso(c, s, ns, ref) {
    const i = rowOf(ref), toks = rowToks(i);
    caption(`Get ${c.v} alone in ${rowName(i)}: ${c.v} has no number in front, so no fractions`);
    mark(toks, 'hot4');
    const n = note(`solve for ${c.v}`, toks); n.classList.add('lift4');
    await quick(150); await hold(); dropNote(n);
  }
  async function animSubst(c, s, ns, ref) {
    const i = rowOf(ref), j = 1 - i, expr = exprOf(s.eqs[j], c.v), ex = sideText(expr);
    const src = [...$('equation').querySelectorAll(`.tok[data-row="${j}"]`)].filter(t => t.dataset.lit !== c.v && !t.classList.contains('eq'));
    const vt = rowToks(i).filter(t => t.dataset.lit === c.v);
    caption(`${rowName(j)} says ${c.v} = ${ex}, so put (${ex}) in place of ${c.v} in ${rowName(i)}`);
    mark(src, 'hot4');
    await quick(150); await hold();
    for (const t of vt) {
      await fly(`(${sideHtml(expr)})`, src[Math.floor(src.length / 2)] || src[0], t, 520);
      const term = [...s.eqs[i].L, ...s.eqs[i].R].find(o => o.lit === c.v), k = term ? term.k : F(1);
      const lead = t.dataset.ref.endsWith('0');
      const kk = fIs(fAbs(k), 1) ? (k.n < 0 ? (lead ? MINUS : MINUS + ' ') : (lead ? '' : '+ ')) : (k.n < 0 ? (lead ? MINUS : MINUS + ' ') : (lead ? '' : '+ ')) + fracHtml(fAbs(k));
      t.innerHTML = `${kk}(${sideHtml(expr)})`; t.classList.add('swap5'); kickClass(t, 'pop');
    }
    caption(`Now there's only one letter: ${eqText(s.eqs[i]).replace(new RegExp(c.v, 'g'), `(${ex})`)}`);
    await quick(250); await hold();
  }
  async function animPlugv(c, s, ns, ref) {
    const i = rowOf(ref), vt = rowToks(i).filter(t => t.dataset.lit === c.v);
    const from = document.querySelector('#a4top .vals5 b') || $('a4top');
    caption(`Plug ${c.v} = ${fracText(c.val)} into ${rowName(i)}: every ${c.v} becomes ${fracText(c.val)}`);
    await quick(150);
    for (const t of vt) {
      await fly(fracHtml(c.val), from, t);
      const term = [...s.eqs[i].L, ...s.eqs[i].R].find(o => o.lit === c.v), k = term ? term.k : F(1), lead = t.dataset.ref.endsWith('0');
      const sign = k.n < 0 ? (lead ? MINUS : MINUS + ' ') : (lead ? '' : '+ ');
      t.innerHTML = `${sign}${fIs(fAbs(k), 1) ? '' : fracHtml(fAbs(k))}(${fracHtml(c.val)})`; kickClass(t, 'pop');
      await quick(150); await hold();
      const pr = fMul(k, c.val);
      t.innerHTML = `${pr.n < 0 ? (lead ? MINUS : MINUS + ' ') : (lead ? '' : '+ ')}${fracHtml(fAbs(pr))}`; kickClass(t, 'pop');
      caption(`${fracText(k)} ${TIMES} ${paren(c.val)} = ${fracText(pr)}. Now solve for ${other(c.v)}`);
    }
    await quick(200); await hold();
  }
  async function animScale(c, s, ns, ref) {
    const i = rowOf(ref), toks = rowToks(i);
    caption(`Multiply ${rowName(i)} by ${numText(c.k)}: every term on both sides`);
    const notes_ = toks.map(t => note(`${TIMES} ${c.k < 0 ? `(${numText(c.k)})` : c.k}`, [t]));
    await quick(150); await hold();
    notes_.forEach(n => n.classList.add('merge')); await quick(220);
    const q = ns.eqs[i];
    for (const s_ of ['L', 'R']) q[s_].forEach((t, j) => { const tk = eqq(`.tok[data-ref="q${i}${s_}${j}"]`); if (tk) { tk.innerHTML = fTermStr(t, j === 0, true, ''); kickClass(tk, 'pop'); } });
    notes_.forEach(dropNote);
    caption(`${rowName(i)} is now ${eqText(q)}: the same line, new numbers`);
    await quick(200); await hold();
  }
  // Add or subtract a term on both sides of one equation: the chip is written under each side, the
  // term it matches cancels, and the other side gains it.
  async function animMove(c, s, ns, ref) {
    const i = rowOf(ref), q = s.eqs[i], chip = `${c.sgn === '+' ? '+' : MINUS} ${moveTerm(c)}`;
    const sideToks = sd => rowToks(i).filter(t => t.dataset.side === sd);
    const hit = sd => sideToks(sd).find(t => t.dataset.lit === c.t.lit && (() => { const o = q[sd][+t.dataset.ref.slice(-1)]; return o && fEq(fAbs(o.k), c.t.k); })());
    caption(`${c.sgn === '+' ? 'Add' : 'Subtract'} ${moveTerm(c)} ${c.sgn === '+' ? 'to' : 'from'} both sides of ${rowName(i)}`);
    const notes_ = ['L', 'R'].map(sd => { const at = hit(sd) || sideToks(sd).slice(-1)[0]; return at ? { sd, at, n: note(chip, [at]) } : null; }).filter(Boolean);
    await quick(150); await hold();
    const gone = notes_.filter(m => hit(m.sd));
    if (gone.length) {
      caption(`${fTermStr(q[gone[0].sd][+gone[0].at.dataset.ref.slice(-1)], true, false, '')} and ${chip.replace(' ', '')} cancel out`);
      gone.forEach(m => mark([m.at, m.n], 'cancel')); await quick(380);
    }
    notes_.forEach(m => dropNote(m.n));
    $('equation').innerHTML = ''; $('equation').appendChild(rowsEl(ns.eqs)); fit5();
    rowToks(i).forEach(t => kickClass(t, 'pop'));
    caption(isStd(ns.eqs[i]) ? `${rowName(i)} is lined up: ${eqText(ns.eqs[i])}` : `${rowName(i)}: ${eqText(ns.eqs[i])}`);
    await quick(200); await hold();
  }
  // Elimination: a line is drawn under the two rows, the columns are added (or subtracted) and the
  // column that comes to 0 cancels.
  async function animCombine(c, s, ns) {
    const sign = c.op === 'addeq' ? 1 : -1, sum = sumCols(s.eqs, sign), grid = eqq('.rows5');
    const s0 = std(s.eqs[0]), s1 = std(s.eqs[1]);
    const L_ = fz(sum.a) ? 'x' : 'y';
    caption(`${sign > 0 ? 'Add' : 'Subtract'} the equations, column by column: ${fracText(s0[L_ === 'x' ? 'a' : 'b'])}${L_} ${sign > 0 ? '+' : MINUS} ${paren(s1[L_ === 'x' ? 'a' : 'b'])}${L_} = 0, so the ${L_}'s cancel`);
    if (grid) {
      const bar = document.createElement('div'); bar.className = 'bar5'; bar.innerHTML = `<span>${sign > 0 ? '+' : MINUS}</span>`;
      grid.appendChild(bar);
      const lab = document.createElement('div'); lab.className = 'lab5';
      const sumEq = { L: [T(sum.a, 'x'), T(sum.b, 'y')], R: [T(sum.c)] };
      const mk = (s_, items) => { const box = document.createElement('div'); box.className = 'side5 ' + s_; items.forEach((t, j) => { const d = TOK(fTermStr(t, j === 0, true, '') || '0', 't5', null, 't5 sum5'); if (fz(t.k) && t.lit) { d.innerHTML = `${j ? '+ ' : ''}0${t.lit}`; d.classList.add('zero5'); } box.appendChild(d); }); return box; };
      const rel = EQTOK('=');
      grid.append(lab, mk('L', sumEq.L), rel, mk('R', sumEq.R));
      [...grid.querySelectorAll('.sum5')].forEach((t, j) => { t.style.animationDelay = (j * 0.12) + 's'; t.classList.add('drop4'); });
      await quick(500); await hold();
      const z = grid.querySelector('.zero5');
      if (z) { const n = note('cancels', [z]); n.classList.add('stamp4'); mark([z], 'cancel'); await quick(400); z.classList.add('melt4'); dropNote(n); }
      await quick(250);
    }
    const w = ns.work;
    // Playtest fix: a sum like x = 3 is solved already, so there is no work left to name.
    caption(!w ? 'One letter cancelled, and the other is already alone' : isStmt(w) ? `Both letters cancelled: ${stmtText(w)}` : `One letter left: solve for ${w.v}`);
    await hold();
  }
  async function animVerdict(c, s, ns) {
    const t = eqq('.tok:not(.eq)') || $('equation');
    const word = c.op === 'snone' ? 'No solution' : c.op === 'sall' ? 'Infinitely many' : 'One solution';
    const why = c.op === 'snone' ? 'the lines are parallel: they never meet' : c.op === 'sall' ? 'both equations are the same line: every point on it works' : 'the slopes are different, so the lines cross exactly once';
    caption(`${word}: ${why}`);
    const n = note(word, [...$('equation').querySelectorAll('.tok:not(.eq)')]); n.classList.add('stamp4');
    await quick(200);
    const g = graphOf(ns); if (g) drawGraph(g);
    await quick(700); await hold(); dropNote(n);
    void t;
  }
  async function animSlopes(c, s, ns) {
    const notes_ = [];
    s.eqs.forEach((q, i) => {
      const l = lineOf(q), toks = rowToks(i);
      const xt = toks.find(t => t.dataset.lit === 'x'), ct = toks.find(t => t.dataset.side === 'R' && !t.dataset.lit);
      if (xt) notes_.push(note(`m = ${fracHtml(l.m)}`, [xt]));
      if (ct) notes_.push(note(`b = ${fracHtml(l.b)}`, [ct]));
      if (!xt) notes_.push(note(`m = 0`, toks.slice(-1)));
    });
    notes_.forEach(n => n.classList.add('lift4'));
    caption('In y = mx + b, m (the number in front of x) is the slope and b is where the line crosses the y-axis');
    await quick(150); await hold(); await hold();
    notes_.forEach(dropNote);
  }
  async function animReadPt(c, s, ns, ref) {
    const dot = document.querySelector(`#graph [data-ref="${ref}"]`), p = ns.vals;
    caption(`The lines cross at (${fracText(p.x)}, ${fracText(p.y)}): that point is on both lines, so it works in both equations`);
    if (dot) { dot.classList.add('ok4'); }
    await quick(200); await hold();
  }
  async function animLine(c, s, ns, ref) {
    const i = rowOf(ref), r = s.rows[i];
    caption(c.op === 'dashed' ? `${r.rel}: points on the line don't count, so the boundary of ${rowName(i)} is dashed` : `${r.rel}: points on the line count, so the boundary of ${rowName(i)} is solid`);
    mark(rowToks(i), 'hot4');
    drawGraph(graphOf(ns));
    await quick(750); await hold();
  }
  async function animShade(c, s, ns, ref) {
    const i = rowOf(ref), r = s.rows[i], side = sideOf(r);
    if (c.op === 'test') {
      // The test point drops onto the graph and the numbers go in; the player then calls it true or false.
      const p = c.p, { a, b, c: cc } = std(r);
      const lhs = `${fracText(a)}(${fracText(p.x)}) + ${fracText(b)}(${fracText(p.y)})`.replace('+ ' + MINUS, MINUS + ' ');
      drawGraph(graphOf(ns));
      const dot = document.querySelector('#graph .test5'); if (dot) kickClass(dot, 'anim');
      mark(rowToks(i), 'hot4');
      caption(`Test ${ptText(p)} in ${rowName(i)}: ${lhs} ${r.rel} ${fracText(cc)}`);
      await quick(300); await hold();
      caption(`${fracText(fAdd(fMul(a, p.x), fMul(b, p.y)))} ${r.rel} ${fracText(cc)}: true or false?`);
      await quick(250); await hold();
      return;
    }
    if (TVERDICT.includes(c.op)) {
      const p = s.st[i].tested;
      caption(c.op === 'ttrue' ? `True, so ${ptText(p)} is on the right side: shade ${side} the line, where it is` : `False, so ${ptText(p)} is on the wrong side: shade the other side, ${side} the line`);
      const dot = document.querySelector('#graph .test5'); if (dot) kickClass(dot, c.op === 'ttrue' ? 'ok4' : 'bad5');
      await quick(300);
    } else caption(`Shade ${side} ${rowName(i)}'s line: those points make ${eqText(r, r.rel)} true`);
    drawGraph(graphOf(ns));
    await quick(750);
    if (ns.st.every(q => q.shade)) { caption('Where the two shaded regions overlap is the solution of the system'); await quick(500); }
    await hold();
  }
  async function animYesNo(c, s, ns) {
    const p = s.askPt;
    caption(c.op === 'yes' ? `${ptText(p)} is in the overlap: it makes both inequalities true` : `${ptText(p)} is outside the overlap: it fails at least one inequality`);
    const d = document.querySelector('#graph .gDot.ask5'); if (d) kickClass(d, 'anim');
    await quick(200); await hold();
  }
  async function animResolve(s, ns, nw) {
    if (ns.done) { caption(`(${fracText(ns.vals.x)}, ${fracText(ns.vals.y)}) works in both equations: it's where the lines cross`); const g = graphOf(ns); if (g) drawGraph(g); await quick(600); await hold(); return; }
    const w = s.work;
    if (w.k4 === 'formula') { caption(`${rowName(w.row)} is now ${eqText(ns.eqs[w.row])}`); await hold(); return; }
    if (!ns.work && nw && !nw.k4) { caption(`${nw.v} = ${fracText(ns.vals[nw.v])}: one letter found. Now the other`); await hold(); }
  }
  function animFor(card) {
    return async (c, s, ns, ref) => {
      if (s.k5 === 'sys' && s.work && !c.a5) {
        const w = s.work, nw = w.k4 === 'formula' ? fApply(w, c, ref) : A2.apply(w, c, ref);
        if (w.k4 === 'formula') await K.animFormula(c, w, nw, ref); else await A2.animFor(c)(c, w, nw, ref);
        if (!ns.work || ns.done) await animResolve(s, ns, nw);
        return;
      }
      switch (c.op) {
        case 'iso': return animIso(c, s, ns, ref);
        case 'subst': return animSubst(c, s, ns, ref);
        case 'plugv': await animPlugv(c, s, ns, ref); if (ns.done) await animResolve(s, ns, null); return;
        case 'scale': return animScale(c, s, ns, ref);
        case 'move': return animMove(c, s, ns, ref);
        case 'addeq': case 'subeq': await animCombine(c, s, ns); if (ns.vals.x !== s.vals.x || ns.vals.y !== s.vals.y) await animResolve({ ...s, work: ns.work || { L: [], R: [] } }, ns, combineA2(s.eqs, c.op === 'addeq' ? 1 : -1)); return;
        case 'snone': case 'sall': case 'sone': return animVerdict(c, s, ns);
        case 'slopes': return animSlopes(c, s, ns);
        case 'readpt': return animReadPt(c, s, ns, ref);
        case 'solid': case 'dashed': return animLine(c, s, ns, ref);
        case 'above': case 'below': case 'left': case 'right': case 'test': case 'ttrue': case 'tfalse': return animShade(c, s, ns, ref);
        case 'yes': case 'no': return animYesNo(c, s, ns);
      }
    };
  }

  // ================================================================ generators
  const COEF = [5, 6, 8, 10], RANGE = [6, 8, 10, 12], CMAX = [45, 70, 100, 140];
  function sv(L, tut) {        // one value of the solution: every level gets negatives and zero sometimes
    const r = tut ? 5 : RANGE[L], v = rand(1, r);
    if (tut) return v;
    const roll = Math.random();
    if (roll < 0.08) return 0;
    return roll < [0.35, 0.45, 0.5, 0.5][L] ? -v : v;
  }
  const co = (C, L, tut, neg = true) => (tut || !neg || (L === 0 && Math.random() < 0.6) ? rand(1, C) : nonZero(-C, C));
  const det = (s0, s1) => fSub(fMul(s0.a, s1.b), fMul(s1.a, s0.b));
  const small = (eqs, L) => eqs.every(q => { const s = std(q); return [s.a, s.b, s.c].every(f => Math.abs(fv(f)) <= CMAX[L]); });
  const withRows = (st, eqs) => ({ ...st, eqs });

  // Stage 18. Cases: one equation already has y (or x) alone, both have y alone (set them equal),
  // neither does (get a letter with no number in front alone first), and a substitution into a term with
  // a minus sign (the minus hits every term in the brackets).
  const SUB_CASES = ['ysolved', 'xsolved', 'both', 'iso', 'neg'];
  function genSub(cs, tut = isTutorial()) {
    const L = lvl(tut), C = tut ? 4 : COEF[L];
    cs = cs || pick(SUB_CASES);
    for (let n = 0; n < 500; n++) {
      let x = F(sv(L, tut)), y = F(sv(L, tut)), eqs;
      // Hard and Expert: some slopes are fractions (y = x/2 + 3), with x a multiple of the bottom
      const fr = !tut && L >= 2 && (cs === 'ysolved' || cs === 'both' || cs === 'neg') && Math.random() < 0.3;
      const mk = () => { if (fr) { const d = pick([2, 3]); x = F(d * rand(-3, 3)); return F(sgn() * pick([1, d - 1 || 1]), d); } return F(L === 0 || tut ? rand(1, 4) * (Math.random() < 0.25 && !tut ? -1 : 1) : nonZero(-4, 4)); };
      if (cs === 'ysolved' || cs === 'neg') {
        const m = mk(), b = fSub(y, fMul(m, x));
        const a = co(C, L, tut), k = cs === 'neg' ? -rand(2, C) : co(C, L, tut);
        if (cs === 'neg' && fz(b)) continue;
        const one = yEq(m, b), two = stdEq(a, k, fAdd(fMul(F(a), x), fMul(F(k), y)));
        // Hard and Expert sometimes hand the first equation over with y not yet alone (y − 3x = 4)
        eqs = [!tut && L >= 2 && cs !== 'neg' && Math.random() < 0.4 ? EQ([T(1, 'y'), T(fNeg(m), 'x')], [T(b)]) : one, two];
      } else if (cs === 'xsolved') {
        const nn = L === 0 || tut ? rand(1, 3) : nonZero(-3, 3), d = fSub(x, fMul(F(nn), y));
        const a = co(C, L, tut), k = co(C, L, tut);
        eqs = [xEq(F(nn), d), stdEq(a, k, fAdd(fMul(F(a), x), fMul(F(k), y)))];
      } else if (cs === 'both') {
        const m1 = mk(), m2 = mk();
        if (fEq(m1, m2)) continue;
        eqs = [yEq(m1, fSub(y, fMul(m1, x))), yEq(m2, fSub(y, fMul(m2, x)))];
      } else {   // iso: exactly one letter in one equation has no number in front
        const v = pick(LET), u = sgn() > 0 || tut || L === 0 ? 1 : -1, w = co(C, L, tut);
        if (Math.abs(w) < 2) continue;
        const a0 = v === 'x' ? u : w, b0 = v === 'x' ? w : u;
        let a1 = co(C, L, tut), b1 = co(C, L, tut);
        if (Math.abs(a1) < 2 || Math.abs(b1) < 2) continue;
        eqs = [stdEq(a0, b0, fAdd(fMul(F(a0), x), fMul(F(b0), y))), stdEq(a1, b1, fAdd(fMul(F(a1), x), fMul(F(b1), y)))];
      }
      const s0 = std(eqs[0]), s1 = std(eqs[1]);
      if (fz(det(s0, s1)) || !small(eqs, L) || !isInt(x) || !isInt(y)) continue;
      if (cs === 'iso' && subOpts(sysState(eqs)).length !== 1) continue;
      return { sys: sysState(eqs, { method: 'sub', skill: 'subst', sol: { x, y } }), enemy: 'swapper' };
    }
    return { sys: sysState([yEq(F(2), F(0)), stdEq(1, 1, 9)], { method: 'sub', skill: 'subst', sol: { x: F(3), y: F(6) } }), enemy: 'swapper' };
  }

  // Stage 19. Cases: a column already opposite (add), already equal (subtract), one equation to
  // multiply first, both to multiply, and one equation that has to be lined up first.
  const ELIM_CASES = ['add', 'sub', 'scale1', 'scale2', 'lineup'];
  const FRAC5 = [0.1, 0.12, 0.15, 0.25];
  function unline(eq) {   // the same equation, not lined up: 3y = 7 − 2x, 2x = 7 − 3y, or 2x + 3y − 7 = 0 style (2x − 7 = −3y)
    const { a, b, c } = std(eq);
    return pick([EQ([T(b, 'y')], [T(c), T(fNeg(a), 'x')]), EQ([T(a, 'x')], [T(c), T(fNeg(b), 'y')]), EQ([T(a, 'x'), T(fNeg(c))], [T(fNeg(b), 'y')])]);
  }
  function genElim(cs, tut = isTutorial()) {
    const L = lvl(tut), C = tut ? 5 : COEF[L];
    cs = cs || pick(ELIM_CASES);
    for (let n = 0; n < 600; n++) {
      const base = cs === 'lineup' ? pick(['add', 'sub', 'scale1']) : cs;
      const frac = !tut && base !== 'scale2' && Math.random() < FRAC5[L];
      const x = frac ? F(2 * rand(-3, 3) + 1, 2) : F(sv(L, tut)), y = F(sv(L, tut));
      const even = k => (frac ? k * 2 : k);
      let a0, b0, a1, b1;
      const col = pick(['a', 'b']);
      const pickNZ = () => co(C, L, tut);
      if (base === 'add' || base === 'sub') {
        const p = Math.abs(pickNZ()) || 1, q = pickNZ(), r = pickNZ();
        const m = p * (Math.random() < 0.5 ? 1 : -1);
        if (col === 'a') { a0 = even(m); a1 = even(base === 'add' ? -m : m); b0 = q; b1 = r; }
        else { b0 = m; b1 = base === 'add' ? -m : m; a0 = even(q); a1 = even(r); }
      } else if (base === 'scale1') {
        const p = Math.abs(pickNZ()) || 1, k = rand(2, tut ? 3 : 4) * (tut || L === 0 ? 1 : sgn());
        if (Math.abs(p * k) > C * 2) continue;
        if (col === 'a') { a0 = even(p); a1 = even(p * k); b0 = pickNZ(); b1 = pickNZ(); }
        else { b0 = p; b1 = p * k; a0 = even(pickNZ()); a1 = even(pickNZ()); }
        if (Math.random() < 0.5) { [a0, a1] = [a1, a0]; [b0, b1] = [b1, b0]; }
      } else {   // scale2: no number in either column divides the other
        a0 = pickNZ(); a1 = pickNZ(); b0 = pickNZ(); b1 = pickNZ();
        const nd = (p, q) => { p = Math.abs(p); q = Math.abs(q); return p >= 2 && q >= 2 && p % q && q % p; };
        if (!nd(a0, a1) || !nd(b0, b1)) continue;
      }
      if ([a0, b0, a1, b1].some(k => !k)) continue;
      let eqs = [stdEq(a0, b0, fAdd(fMul(F(a0), x), fMul(F(b0), y))), stdEq(a1, b1, fAdd(fMul(F(a1), x), fMul(F(b1), y)))];
      const s0 = std(eqs[0]), s1 = std(eqs[1]);
      if (fz(det(s0, s1)) || !small(eqs, L)) continue;
      // exactly the intended situation: add and subtract never both cancel, and the scale cases start with nothing cancelling
      const st = sysState(eqs, { method: 'elim' }), o = elimOpts(st);
      if (base === 'add' && !(o.length === 1 && o[0].op === 'addeq')) continue;
      if (base === 'sub' && !(o.length === 1 && o[0].op === 'subeq')) continue;
      if ((base === 'scale1' || base === 'scale2') && o[0].op !== 'scale') continue;
      if (base === 'scale1' && o.some(q => q.k > 4)) continue;
      if (base === 'scale2' && (o[0].k > 5 || Math.abs(fv(s0.c)) * o[0].k > CMAX[L] * 2)) continue;
      if (cs === 'lineup' || (!tut && L >= 2 && Math.random() < 0.35)) { const i = rand(0, 1); eqs = eqs.map((q, j) => (j === i ? unline(q) : q)); }
      return { sys: sysState(eqs, { method: 'elim', skill: 'elim', sol: { x, y } }), enemy: 'canceller' };
    }
    return { sys: sysState([stdEq(2, 3, 12), stdEq(2, -1, 4)], { method: 'elim', skill: 'elim', sol: { x: F(3), y: F(2) } }), enemy: 'canceller' };
  }

  // Stage 20. Parallel lines (no solution) and the same line twice (infinitely many), reached by
  // substitution or elimination; "how many solutions?" by comparing slopes; and solving by graphing.
  const SPECIAL_CASES = ['nonesub', 'infelim', 'noneelim', 'infsub', 'count', 'graph'];
  function genSpecial(cs, tut = isTutorial()) {
    const L = lvl(tut), C = tut ? 4 : COEF[L];
    cs = cs || pick(SPECIAL_CASES);
    for (let n = 0; n < 500; n++) {
      if (cs === 'nonesub' || cs === 'infsub') {
        const m = L === 0 || tut ? rand(1, 4) : nonZero(-4, 4), b = rand(-6, 6), k = (tut ? rand(1, 2) : rand(1, 3)) * (L && !tut ? sgn() : 1);
        const b2 = cs === 'infsub' ? b : b + nonZero(-5, 5);
        const eqs = [yEq(F(m), F(b)), stdEq(-k * m, k, k * b2)];
        if (!small(eqs, L)) continue;
        return { sys: sysState(eqs, { method: 'sub', skill: 'special5' }), enemy: 'parallax' };
      }
      if (cs === 'noneelim' || cs === 'infelim') {
        const a = co(C, L, tut), b = co(C, L, tut), c = rand(-12, 12), k = cs === 'infelim' ? rand(2, 3) * (L && !tut ? sgn() : 1) : pick([1, 2, 2, 3]) * (L && !tut ? sgn() : 1);
        const c2 = cs === 'infelim' ? k * c : k * c + nonZero(-6, 6);
        let eqs = [stdEq(a, b, c), stdEq(k * a, k * b, c2)];
        if (!small(eqs, L) || (Math.abs(a) === 1 && Math.abs(b) === 1 && k === 1)) continue;
        if (!tut && L >= 2 && Math.random() < 0.35) { const i = rand(0, 1); eqs = eqs.map((q, j) => (j === i ? unline(q) : q)); }
        return { sys: sysState(eqs, { method: 'elim', skill: 'special5' }), enemy: 'parallax' };
      }
      if (cs === 'count') {
        const kind = pick(['one', 'none', 'inf']);
        const m1 = L === 0 || tut ? rand(1, 4) : nonZero(-4, 4), b1 = rand(-6, 6);
        const m2 = kind === 'one' ? m1 + nonZero(-3, 3) : m1, b2 = kind === 'inf' ? b1 : kind === 'none' ? b1 + nonZero(-5, 5) : rand(-6, 6);
        let eqs = [yEq(F(m1), F(b1)), yEq(F(m2), F(b2))];
        // Normal and up: one equation isn't in y = mx + b form yet (get y alone first)
        if (!tut && L >= 1) { const i = rand(0, 1), k = rand(2, 3) * sgn(); eqs[i] = Math.random() < 0.5 ? stdEq(-k * [m1, m2][i], k, k * [b1, b2][i]) : EQ([T(k, 'y')], [T(k * [m1, m2][i], 'x'), T(k * [b1, b2][i])]); }
        if (!small(eqs, L)) continue;
        return { sys: sysState(eqs, { method: 'any', ask: 'count', skill: 'special5' }), enemy: 'parallax' };
      }
      // graph: two lines crossing at a whole-number point; the candidate points are the crossing and each
      // line's y-intercept (and, from Normal, one more point on a line).
      const x = F(rand(-4, 4)), y = F(rand(-4, 4));
      const m1 = nonZero(-3, 3), m2 = nonZero(-3, 3);
      if (m1 === m2) continue;
      const b1 = fSub(y, fMul(F(m1), x)), b2 = fSub(y, fMul(F(m2), x));
      if (Math.abs(fv(b1)) > 7 || Math.abs(fv(b2)) > 7) continue;
      const cands = [{ x, y }, { x: F(0), y: b1 }, { x: F(0), y: b2 }];
      if (!tut && L >= 1) { const px = fAdd(x, F(sgn() * 2)); cands.push({ x: px, y: fAdd(fMul(F(m1), px), b1) }); }
      const keys = cands.map(p => fracText(p.x) + ',' + fracText(p.y));
      if (new Set(keys).size !== keys.length || cands.some(p => Math.abs(fv(p.y)) > 8 || Math.abs(fv(p.x)) > 8)) continue;
      const eqs = [yEq(F(m1), b1), yEq(F(m2), b2)];
      const win = K.windowFor(cands.map(p => p.x), cands.map(p => p.y));
      return { sys: sysState(eqs, { method: 'any', ask: 'graph', skill: 'special5', sol: { x, y }, cands: shuffle(cands), win }), enemy: 'parallax' };
    }
    return { sys: sysState([yEq(F(2), F(1)), stdEq(-4, 2, 6)], { method: 'sub', skill: 'special5' }), enemy: 'parallax' };
  }

  // Stage 21. Two inequalities: both with y alone, one with y not alone (the classic slip: 2x − y < 4 is
  // shaded above, not below), a horizontal or vertical boundary, a line through (0, 0) (testing (0, 0)
  // tells you nothing), and a point to check at the end.
  const INEQ_CASES = ['yy', 'std', 'hv', 'origin', 'point'];
  const RELS = ['<', '≤', '>', '≥'];
  const yRow = (m, b, rel) => ({ ...yEq(m, b), rel, form: 'y' });
  function genIneq(cs, tut = isTutorial()) {
    const L = lvl(tut);
    cs = cs || pick(INEQ_CASES);
    const win = { x0: -7, x1: 7, y0: -7, y1: 7 };
    const slope = () => (!tut && L >= 2 && Math.random() < 0.3 ? F(sgn(), 2) : F(nonZero(-3, 3)));
    for (let n = 0; n < 500; n++) {
      const r1 = () => yRow(slope(), F(rand(-4, 4)), pick(RELS));
      let rows;
      if (cs === 'yy' || tut) rows = [r1(), r1()];
      if (cs === 'std' && !tut) {
        const A = nonZero(-4, 4), B = Math.random() < 0.7 ? -rand(1, 3) : rand(1, 3), Cc = rand(-6, 6);
        const row = { ...stdEq(A, B, Cc), rel: pick(RELS), form: 'std' };
        if (Math.abs(fv(lineOf(row).b)) > 6) continue;
        rows = [row, r1()];
      }
      if (cs === 'hv' && !tut) rows = [Math.random() < 0.5 ? { ...EQ([T(1, 'y')], [T(rand(-4, 4))]), rel: pick(RELS), form: 'y' } : { ...EQ([T(1, 'x')], [T(rand(-4, 4))]), rel: pick(RELS), form: 'v' }, r1()];
      if (cs === 'origin' && !tut) rows = [yRow(slope(), F(0), pick(RELS)), r1()];
      if (cs === 'point' && !tut) rows = [r1(), Math.random() < 0.5 ? r1() : { ...stdEq(nonZero(-3, 3), -rand(1, 2), rand(-5, 5)), rel: pick(RELS), form: 'std' }];
      if (!rows) continue;
      const l0 = lineOf(rows[0]), l1 = lineOf(rows[1]);
      if (!l0 || !l1) continue;
      if (l0.x === undefined && l1.x === undefined && fEq(l0.m, l1.m)) continue;
      if (l0.x !== undefined && l1.x !== undefined) continue;
      if (rows.some(r => r.form === 'y' && r.L[0].lit === 'y' && r.R.some(t => t.lit === 'x') && Math.abs(fv(lineOf(r).b)) > 5)) continue;
      // the overlap has to show on the grid, away from the lines
      let inside = 0; for (let gx = -6; gx <= 6; gx++) for (let gy = -6; gy <= 6; gy++) { const p = { x: F(gx), y: F(gy) }; if (rows.every(r => valAt(r, p) !== 0 && inRow(r, p))) inside++; }
      if (inside < 8 || inside > 120) continue;
      if (cs === 'origin' && rows.slice(1).some(r => onLine(r, O))) continue;
      if (cs !== 'origin' && rows.some(r => onLine(r, O) && r.form === 'std')) continue;
      const st = ineqState(rows, { win, skill: 'sysineq' });
      if (cs === 'point' && !tut) {
        const want = Math.random() < 0.5;
        let p = null;
        for (let k = 0; k < 200 && !p; k++) {
          const q = { x: F(rand(-5, 5)), y: F(rand(-5, 5)) };
          if (rows.some(r => onLine(r, q) && !(L >= 1 && strict(r.rel)))) continue;
          if (inBoth({ rows }, q) === want && !(fz(q.x) && fz(q.y))) p = q;
        }
        if (!p) continue;
        st.askPt = p;
      }
      return { sys: st, enemy: 'umbra' };
    }
    return { sys: ineqState([yRow(F(1), F(1), '>'), yRow(F(-2), F(4), '≤')], { win, skill: 'sysineq' }), enemy: 'umbra' };
  }

  // ---------------------------------------------------------------- elite and boss
  function genAny() {
    const g = Math.random() < 0.5 ? genElim(pick(['scale1', 'scale2', 'lineup'])) : genSub(pick(['iso', 'neg', 'both']));
    g.sys.method = 'any'; g.sys.skill = g.sys.skill || 'subst';
    return g;
  }
  function genStacked5(list) {
    const act5 = list.filter(id => (SKILL[id].act || 1) === 5), newest = act5[act5.length - 1];
    if (newest === 'sysineq') { const g = genIneq('point'); return { ...g, enemy: 'eclipse' }; }
    if (newest === 'special5') { const g = genSpecial(pick(['count', 'noneelim', 'infsub'])); return { ...g, enemy: 'eclipse' }; }
    if (newest === 'elim') { const g = genElim(pick(['scale2', 'lineup'])); return { ...g, enemy: 'eclipse' }; }
    return { ...genSub(pick(['iso', 'neg'])), enemy: 'eclipse' };
  }
  function buildFight5(node, list) {
    const act5 = list.filter(id => (SKILL[id].act || 1) === 5);
    if (node.type === 'elite') return { phases: [() => genStacked5(list)], handSize: difficulty.hand, enemy: 'eclipse' };
    // Boss: one phase per Act 5 stage, then a system to solve any way you like.
    const phases = act5.map(id => () => GENS[id](pick(SKILL[id].cases)));
    phases.push(() => genAny());
    return { phases, handSize: difficulty.hand, enemy: 'twinmoons' };
  }
  const GENS = { subst: genSub, elim: genElim, special5: genSpecial, sysineq: genIneq };

  // ---------------------------------------------------------------- variety
  function textOf5(e) {
    if (e.k5 === 'ineq5') return `ineq ${e.rows.map(r => eqText(r, r.rel)).join(' ; ')}${e.askPt ? ' @' + ptText(e.askPt) : ''}`;
    return `sys ${e.method} ${e.ask} ${e.eqs.map(q => eqText(q)).join(' ; ')}`;
  }
  const mirror5 = e => (e.k5 === 'ineq5' ? { ...e, rows: [e.rows[1], e.rows[0]], st: [e.st[1], e.st[0]] } : { ...e, eqs: [e.eqs[1], e.eqs[0]] });
  if (typeof ENGINES === 'object') ENGINES.sys = { text: textOf5, mirror: mirror5 };
  const applyDifficulty = g => g;   // generators read the difficulty themselves; tutorials stay on Easy

  // ================================================================ skills, enemies, act
  SKILLS.push(
    { id: 'subst', stage: 18, act: 5, name: 'Substitution', cases: SUB_CASES, gen: cycled('subst', c => genSub(c)),
      title: 'Stage 18: Substitution',
      intro: 'A system is two equations that share x and y. The solution is the point (x, y) that works in both: where their lines cross. Substitution: when one equation says y = ..., drop ◎ Sub in y on the other equation, and that expression takes y\'s place (in brackets). Now there\'s only one letter: solve it. Then plug the value back in to find the other letter. No letter alone yet? ◎ Solve for gets one alone: pick a letter with no number in front.',
      example: 'y = 2x, x + y = 9<br>Sub in y → x + 2x = 9<br>Combine → 3x = 9 → x = 3<br>Plug x = 3 into y = 2x → y = 6<br>Solution (3, 6)',
      tutorial: [() => genSub('ysolved', true), () => genSub('iso', true)] },
    { id: 'elim', stage: 19, act: 5, name: 'Elimination', cases: ELIM_CASES, gen: cycled('elim', c => genElim(c)),
      title: 'Stage 19: Elimination',
      intro: 'Elimination makes one letter cancel. Line the equations up (x over x, y over y, numbers on the right): if a term is on the wrong side, add or subtract it on both sides of that equation. If a column has opposite numbers, like 3y and −3y, ⇔ ① + ② adds the equations; if it has the same numbers, ⇔ ① − ② subtracts them. If no column matches, drop ◎ Scale on one (or both) to make one match. One letter cancels; solve for the other, then plug it back in.',
      example: '2x + 3y = 12<br>2x − y = 4<br>Subtract → 4y = 8 → y = 2<br>Plug y = 2 into 2x − y = 4 → 2x − 2 = 4 → x = 3',
      tutorial: [() => genElim('add', true), () => genElim('scale1', true)] },
    { id: 'special5', stage: 20, act: 5, name: 'Special systems', cases: SPECIAL_CASES, gen: cycled('special5', c => genSpecial(c)),
      title: 'Stage 20: Special systems and graphing',
      intro: 'Sometimes both letters cancel. If what\'s left is false, like 0 = 5, the lines are parallel and never meet: No solution. If it\'s true, like 0 = 0, both equations are the same line: All points (infinitely many solutions). You can also tell from y = mx + b: different slopes cross once; the same slope with a different b never meets. And on a graph, the solution is simply where the lines cross.',
      example: 'y = 2x + 1, −4x + 2y = 6<br>Substitute → −4x + 2(2x + 1) = 6<br>→ −4x + 4x + 2 = 6 → 2 = 6<br>False: No solution (parallel lines)',
      tutorial: [() => genSpecial('nonesub', true), () => genSpecial('count', true)] },
    { id: 'sysineq', stage: 21, act: 5, name: 'Systems of inequalities', cases: INEQ_CASES, gen: cycled('sysineq', c => genIneq(c)),
      title: 'Stage 21: Systems of inequalities',
      intro: 'Graph each inequality: first its boundary line, solid for ≤ and ≥ (the line counts) or dashed for < and > (it doesn\'t). Then shade the side that works: with y alone, > and ≥ mean above, < and ≤ below. If y isn\'t alone, test a point off the line like (0, 0), then say whether it makes the inequality True or False: true means shade its side, false means shade the other side. The solution of the system is where the two shadings overlap.',
      example: 'y > x + 1: dashed line, shade above<br>y ≤ −2x + 4: solid line, shade below<br>The overlap is the solution',
      tutorial: [() => genIneq('yy', true), () => genIneq('yy', true)] },
  );
  for (const s of SKILLS) SKILL[s.id] = s;
  progress = loadProgress();     // the save was first read before these skills existed

  Object.assign(ENEMIES, {
    swapper:   { name: 'Swapper',      rank: 'Normal', color: '#90be6d', size: 84 },
    canceller: { name: 'Canceller',    rank: 'Normal', color: '#f94144', size: 84 },
    parallax:  { name: 'Parallax',     rank: 'Normal', color: '#577590', size: 84 },
    umbra:     { name: 'Umbra',        rank: 'Normal', color: '#9d4edd', size: 84 },
    eclipse:   { name: 'Eclipse Knight', rank: 'Elite', color: '#43aa8b', size: 100, horns: true },
    twinmoons: { name: 'The Twin Moons', rank: 'Boss',  color: '#e0e1dd', size: 120, crown: true },
  });
  ACTS[5] = { name: 'The Twin Observatory', sub: 'Systems of equations and inequalities', boss: 'The Twin Moons', firstSkill: 'subst',
    blurb: 'In the Twin Observatory every enemy is two equations at once. Find the point that satisfies both: substitute, eliminate, read the graph, or shade the overlap, and defeat The Twin Moons.' };

  const svgI = body => `<svg viewBox="0 0 24 24" width="1em" height="1em" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round">${body}</svg>`;
  Object.assign(CARD_ICONS, {
    iso5:    { name: 'Get one letter alone', svg: svgI('<circle cx="12" cy="12" r="4"/><path d="M3 12h3M18 12h3"/>') },
    subst5:  { name: 'Substitute into the other equation', svg: svgI('<path d="M4 7h11l-3-3M20 17H9l3 3"/>') },
    scale5:  { name: 'Multiply a whole equation', svg: svgI('<path d="M5 5l6 6M11 5l-6 6"/><path d="M14 9h7M14 15h7"/>') },
    lineup5: { name: 'Line an equation up (ax + by = c)', svg: svgI('<path d="M4 6h16M4 12h16M4 18h16"/><path d="M14 4v16"/>') },
    addeq5:  { name: 'Add the equations', svg: svgI('<path d="M4 6h12M4 11h12M4 15h16"/><path d="M19 3v6M16 6h6"/>') },
    subeq5:  { name: 'Subtract the equations', svg: svgI('<path d="M4 6h12M4 11h12M4 15h16"/><path d="M16 6h6"/>') },
    one5:    { name: 'Declare: one solution / yes', svg: svgI('<path d="M4 4l16 16M20 4L4 20"/><circle cx="12" cy="12" r="2.5"/>') },
    cross5:  { name: 'Read where the lines cross', svg: svgI('<path d="M3 20L21 6M3 6l18 14"/><circle cx="12" cy="13" r="3"/>') },
    solid5:  { name: 'Solid boundary (≤, ≥)', svg: svgI('<path d="M3 19L21 5"/>') },
    dashed5: { name: 'Dashed boundary (<, >)', svg: svgI('<path d="M3 19l3-2.3M9 14.3l3-2.3M15 9.7l3-2.3"/>') },
    shade5:  { name: 'Shade a side', svg: svgI('<path d="M3 19L21 5"/><path d="M5 9l4-4M5 14l9-9M10 15l9-7"/>') },
    test5:   { name: 'Test a point', svg: svgI('<circle cx="12" cy="12" r="3"/><path d="M12 3v3M12 18v3M3 12h3M18 12h3"/>') },
  });

  const css = document.createElement('style');
  css.textContent = `
    #equation.sys5 { flex-wrap:nowrap; gap:0; max-width:100%; }
    .sys5wrap { display:flex; align-items:stretch; max-width:100%; }
    .brace5 { width:.28em; border:.07em solid var(--muted); border-right:none; border-radius:.35em 0 0 .35em; margin:.15em .25em .15em 0; flex:none; }
    .rows5 { display:grid; grid-template-columns:auto auto auto auto; align-items:center; row-gap:.05em; }
    .lab5 { font-size:.38em; padding-right:.35em; color:#7bdff2; font-weight:bold; }
    .lab5.r1 { color:#ff9ad5; }
    .side5 { display:flex; align-items:center; }
    .side5.L { justify-content:flex-end; } .side5.R { justify-content:flex-start; }
    .tok.t5 { min-height:calc(var(--eqSize) * 1.25); padding:2px 4px; }
    .rows5 .tok.eq { min-height:calc(var(--eqSize) * 1.25); padding:2px 6px; min-width:0; }   /* playtest fix: the shared 96px min-height made each row 96px tall and shrank the font */
    .tok.t5 .lv, #a4top .t5top .lv, .tok.res5 i { font-style:normal; color:var(--accent); }
    .tok.t5.swap5 { color:#7bdff2; }
    .tok.res5 { color:var(--good); max-width:none; white-space:nowrap; }
    .bar5 { grid-column:1 / 5; height:.08em; min-height:3px; background:var(--muted); margin:.05em 0; position:relative; animation: grow .3s ease-out; transform-origin:left; }
    .bar5 span { position:absolute; left:-.1em; top:-.75em; font-size:.6em; color:var(--muted); }
    .tok.t5.sum5 { color:var(--good); }
    .tok.t5.zero5 { color:var(--bad); }
    .tok.ok5, #graph .gtarget.ok5 { border-color: var(--good) !important; background:#06d6a022 !important; }
    #graph .gtarget.ok5 { stroke:var(--good); stroke-width:3; fill:#06d6a033; }
    #a4top .sys5top { display:inline-flex; flex-wrap:wrap; gap:4px 10px; align-items:center; justify-content:center; }
    #a4top .lab5 { font-size:.8em; padding-right:2px; }
    #a4top .t5top { color:var(--ink); }
    #a4top .vals5 { margin-left:10px; color:var(--ink); white-space:nowrap; }
    #a4top .vals5 i { color:var(--accent); }
    #a4top .note5 { display:block; font-size:.85em; color:var(--muted); }
    #graph .g5r0 { stroke:#7bdff2; opacity:.95; } #graph .g5r1 { stroke:#ff9ad5; opacity:.95; }
    #graph .gRef.g5 { stroke-dasharray:none; stroke-width:3; }
    #graph .gLineLab.g5r1 { fill:#ff9ad5; }
    #graph .gHalf.h50 { fill:#7bdff2; } #graph .gHalf.h51 { fill:#ff9ad5; }
    #graph .gDot.ask5 { fill:#ffffff; } #graph .gDot.test5 { fill:var(--accent); } #graph .gDot.test5.ok4 { fill:#5ad17a; } #graph .gDot.test5.bad5 { fill:#ff6b6b; }
    @media (max-width: 640px) {
      .tok.t5 { min-height:calc(var(--eqSize) * 1.3); padding:2px 3px; }
      .rows5 .tok.eq { min-height:calc(var(--eqSize) * 1.3); padding:2px 3px; }
      #a4top .vals5 { display:block; margin:0; }
    }
  `;
  document.head.appendChild(css);

  window.ACT5 = { apply: apply5, isSolved: isSolved5, makeEquation: makeEquation5, refreshPath, render, prefit, clear, makeHand: makeHand5,
    isCorrect, whyWrong, animFor, applyDifficulty, label, text, kind, icon, slot, targetSel, onDrag, autoTarget, buildFight: buildFight5, prompt,
    gens: GENS, eqText: textOf5,
    // test hooks
    _canon: canon5, _correct: correct5, _options: options, _apply: apply5 };
})();
