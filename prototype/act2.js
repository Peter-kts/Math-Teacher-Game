// =====================================================================
//  Act 2: The Bracket Halls (Rearranging)
// =====================================================================
// Act 1 equations always have the shape coef·x + b = c. Act 2 needs more: several terms per side,
// parentheses, x on both sides and fractions with x on top. So Act 2 uses its own equation model,
// generators, hand builder and animations, all in this file. index.html only switches engines when a
// generator returns { eq } instead of { s }. Act 1 fights (including review fights inside an Act 2
// run) still use the Act 1 engine unchanged.
//
// This file loads after the main script and uses its helpers (F, fAdd, fMul, rand, pick, note...).
//
// Equation model
//   eq   = { L: [item...], R: [item...], result: null | 'none' | 'all' }
//   item = { t: 'n', k: F }                  a number
//        | { t: 'x', k: F }                  an x-term, k·x (k can be a fraction: x/3)
//        | { t: 'g', m: F, items: [n|x] }    m(...) parentheses
//   An empty side means 0.
//
// Cards (besides the Act 1 ones: + − × ÷ by n, neg, frac)
//   { op: '+'|'-', n, x: true }   add or subtract n·x on both sides                ⇔
//   { op: 'comb', scope: 'part' } combine like terms; drop on one of them          ◎
//   { op: 'dist', scope: 'part' } distribute; drop on the parentheses             ◎
//   { op: 'none'|'all', scope: 'part' } declare no solution / every number works  ◎
'use strict';
(function () {
  const N = k => ({ t: 'n', k: typeof k === 'number' ? F(k) : k });
  const X = k => ({ t: 'x', k: typeof k === 'number' ? F(k) : k });
  const G = (m, items) => ({ t: 'g', m: typeof m === 'number' ? F(m) : m, items });
  const noZero = side => side.filter(i => !(i.t === 'n' && i.k.n === 0));
  const E = (L, R) => ({ L: noZero(L), R: noZero(R), result: null });   // "+ 0" is left out; an empty side shows 0
  const fZero = a => a.n === 0;
  const fEq = (a, b) => a.n === b.n && a.d === b.d;
  const fLess = (a, b) => a.n * b.d < b.n * a.d;
  const lcm = (a, b) => a / gcd(a, b) * b;
  const clone = e => JSON.parse(JSON.stringify(e));
  const sideOf = (e, s) => (s === 'L' ? e.L : e.R);
  const parseRef = ref => [ref[0], +ref.slice(1)];
  const swapSides = e => ({ L: e.R, R: e.L, result: e.result });
  const maybeSwap = (e, p = 0.3) => (Math.random() < p ? swapSides(e) : e);
  const constOf = side => { const c = side.find(i => i.t === 'n'); return c ? c.k : F(0); };
  const isPart = c => c.scope === 'part';
  const isDeclare = c => c.op === 'none' || c.op === 'all';
  const hasGroup = e => [...e.L, ...e.R].some(i => i.t === 'g');
  const isStatement = e => !e.result && ![...e.L, ...e.R].some(i => i.t !== 'n');   // no x left: "1 = 5"
  const statementTrue = e => fEq(constOf(e.L), constOf(e.R));
  const fracItems = e => [...e.L, ...e.R].filter(i => i.t !== 'g' && i.k.d > 1);

  // ---------------------------------------------------------------- moves
  // Adds a term to a side, merging it into the last like term (so "x + 3 − 3" becomes "x").
  function addTerm(side, term) {
    let idx = -1; side.forEach((it, i) => { if (it.t === term.t) idx = i; });
    if (idx < 0) { side.push({ ...term }); return; }
    const k = fAdd(side[idx].k, term.k);
    if (fZero(k)) side.splice(idx, 1); else side[idx] = { t: term.t, k };
  }
  function scaleSide(side, m) {
    side.forEach(it => { if (it.t === 'g') it.m = fMul(it.m, m); else it.k = fMul(it.k, m); });
    for (let i = side.length - 1; i >= 0; i--) if (side[i].t === 'g' && fIs(side[i].m, 1)) side.splice(i, 1, ...side[i].items);   // 1(x + 2) is just x + 2
  }
  function combineSide(side, kind) {
    let sum = F(0); side.forEach(it => { if (it.t === kind) sum = fAdd(sum, it.k); });
    const out = []; let placed = false;
    for (const it of side) {
      if (it.t !== kind) { out.push(it); continue; }
      if (!placed && !fZero(sum)) out.push({ t: kind, k: sum });
      placed = true;
    }
    return out;
  }
  function apply(e0, c, ref) {
    const e = clone(e0);
    if (c.op === '+' || c.op === '-') {
      const k = F(c.op === '+' ? c.n : -c.n), term = c.x ? X(k) : N(k);
      addTerm(e.L, term); addTerm(e.R, term);
    } else if (c.op === '*' || c.op === '/' || c.op === 'neg' || c.op === 'frac') {
      const m = cardFactor(c); scaleSide(e.L, m); scaleSide(e.R, m);
    } else if (c.op === 'dist') {
      const [s, i] = parseRef(ref), side = sideOf(e, s), g = side[i];
      side.splice(i, 1, ...g.items.map(t => ({ t: t.t, k: fMul(t.k, g.m) })));
    } else if (c.op === 'comb') {
      const [s, i] = parseRef(ref), side = sideOf(e, s);
      e[s] = combineSide(side, side[i].t);
    } else if (isDeclare(c)) e.result = c.op;
    return e;
  }
  // Is this ◎ card allowed on that part? (Combine needs a like term on the same side; Distribute needs parentheses.)
  function legalPart(e, c, ref) {
    if (isDeclare(c)) return true;
    if (!ref || !/^[LR]\d+$/.test(ref)) return false;
    const [s, i] = parseRef(ref), side = sideOf(e, s), it = side[i];
    if (!it) return false;
    if (c.op === 'dist') return it.t === 'g';
    if (c.op === 'comb') return it.t !== 'g' && side.filter(o => o.t === it.t).length >= 2;
    return false;
  }

  const isSolved = e => {
    if (e.result) return true;
    const done = (a, b) => a.length === 1 && a[0].t === 'x' && fIs(a[0].k, 1) && b.length <= 1 && b.every(i => i.t === 'n');
    return done(e.L, e.R) || done(e.R, e.L);
  };

  // The move the game expects next. Order: clear parentheses, clear fractions, combine like terms,
  // gather x on one side, then finish the Act 1 way (undo + and − first, then × and ÷).
  function canon(e) {
    if (isSolved(e)) return null;
    for (const s of ['L', 'R']) { const i = sideOf(e, s).findIndex(it => it.t === 'g'); if (i >= 0) return { op: 'dist', scope: 'part', ref: s + i }; }
    const fr = fracItems(e);
    if (fr.length >= 2) return { op: '*', n: fr.reduce((a, it) => lcm(a, it.k.d), 1) };
    for (const kind of ['x', 'n']) for (const s of ['L', 'R']) {
      const idx = sideOf(e, s).map((it, j) => (it.t === kind ? j : -1)).filter(j => j >= 0);
      if (idx.length >= 2) return { op: 'comb', scope: 'part', ref: s + idx[0] };
    }
    const xL = e.L.find(it => it.t === 'x'), xR = e.R.find(it => it.t === 'x');
    if (xL && xR) {                                   // remove the smaller x-term, so x keeps a positive number in front
      const k = fLess(xL.k, xR.k) ? xL.k : xR.k, n = k.n / k.d;
      return n > 0 ? { op: '-', n, x: true } : { op: '+', n: -n, x: true };
    }
    if (!xL && !xR) return { op: statementTrue(e) ? 'all' : 'none', scope: 'part' };
    const xs = xL ? e.L : e.R, b = xs.find(it => it.t === 'n');
    if (b) { const n = b.k.n / b.k.d; return n > 0 ? { op: '-', n } : { op: '+', n: -n }; }
    return correctMove({ coef: (xL || xR).k, b: F(0) });      // the Act 1 rule for the number in front of x
  }
  function pathFrom(e0) {
    const path = []; let e = e0;
    while (path.length < 20) { const m = canon(e); if (!m) break; path.push({ state: e, move: m }); e = apply(e, m, m.ref); }
    const tail = path.filter(p => !isPart(p.move) && !p.move.x && !(p.move.op === '*' && fracItems(p.state).length >= 2)).length;
    for (const p of path) p.skill = skillOf(p, tail);
    return { path, end: e };
  }
  const steps = e => pathFrom(e).path.length;
  function skillOf(p, tail) {
    const m = p.move;
    if (m.op === 'dist') return 'distribute';
    if (m.op === 'comb') return 'liketerms';
    if (m.x) return 'xboth';
    if (isDeclare(m)) return 'special';
    if (m.op === '*' && fracItems(p.state).length >= 2) return 'clearfrac';
    if (isNegFracMove(m)) return 'negfrac';
    return tail > 1 ? 'twostep' : 'onestep';
  }

  function makeEquation2(eq, enemy) {
    const { path, end } = pathFrom(eq);
    let answer = F(0), answerText;
    if (end.result === 'none') answerText = 'No solution';
    else if (end.result === 'all') answerText = 'Every number works';
    else { const other = end.L.length === 1 && end.L[0].t === 'x' ? end.R : end.L; answer = constOf(other); answerText = 'x = ' + fracText(answer); }
    return { start: eq, path, answer, answerText, enemy, skills: [...new Set(path.map(p => p.skill))], act2: true };
  }
  // After each move the rest of the path is worked out again, because a ◎ card can be played on any
  // valid part (e.g. combining the numbers before the x-terms), not only the one the path picked.
  function refreshPath(cur) {
    cur.path = cur.path.slice(0, cur.step).concat(pathFrom(cur.state).path);
  }

  // ---------------------------------------------------------------- text
  const XV = '<i class="xv">x</i>';
  function body(it, html) {      // the term without its sign
    if (it.t === 'n') return html ? fracHtml(fAbs(it.k)) : fracText(fAbs(it.k));
    if (it.t === 'x') {
      const { n, d } = fAbs(it.k);
      const top = html ? (n === 1 ? '' : `<span class="cf">${n}</span>`) + XV : (n === 1 ? '' : n) + 'x';
      if (d === 1) return top;
      return html ? `<span class="frac"><span>${top}</span><span class="den">${d}</span></span>` : `${top}/${d}`;
    }
    const m = fAbs(it.m), mm = fIs(m, 1) ? '' : (html ? fracHtml(m) : fracText(m));
    const inner = it.items.map((t, j) => (html ? `<span class="gi">${termStr(t, j === 0, true)}</span>` : termStr(t, j === 0, false))).join(' ');
    // One wrapper span: .tok is a flex box, which would drop the spaces between loose spans.
    return html ? `<span class="gw"><span class="gm">${mm}</span><span class="gp">(</span>${inner}<span class="gp">)</span></span>` : `${mm}(${inner})`;
  }
  function termStr(it, first, html) {
    const neg = (it.t === 'g' ? it.m : it.k).n < 0;
    return (neg ? (first ? MINUS : MINUS + ' ') : (first ? '' : '+ ')) + body(it, html);
  }
  const sideStr = (side, html) => (side.length ? side.map((it, i) => termStr(it, i === 0, html)).join(' ') : '0');
  const eqText = e => (e.result === 'none' ? 'No solution' : e.result === 'all' ? 'Every number works' : `${sideStr(e.L)} = ${sideStr(e.R)}`);
  const plain = it => termStr(it, true, false);

  // ---------------------------------------------------------------- rendering
  function render(e) {
    const el = $('equation'); if (typeof clearNotes === 'function') clearNotes(); el.innerHTML = '';
    // Long equations (lots of terms) get a smaller font so they stay on one or two lines on phones.
    el.classList.toggle('a2long', e.L.length + e.R.length > 4 || [...e.L, ...e.R].some(i => i.t === 'g') && e.L.length + e.R.length > 2);
    if (e.result) { el.appendChild(mkTok(e.result === 'none' ? 'No solution' : 'Every number works', 'Lr', 'result')); return; }
    for (const s of ['L', 'R']) {
      const side = sideOf(e, s);
      if (!side.length) el.appendChild(mkTok('0', s + 'z', 'zero'));
      side.forEach((it, i) => el.appendChild(mkTok(termStr(it, i === 0, true), s + i, it.t)));
      if (s === 'L') { const q = document.createElement('div'); q.className = 'tok eq'; q.dataset.role = 'eq'; q.textContent = '='; el.appendChild(q); }
    }
  }
  function mkTok(html, ref, kind) {
    const d = document.createElement('div');
    d.className = 'tok term a2 k-' + kind;
    d.dataset.role = kind === 'g' ? 'group' : kind === 'x' ? 'xterm' : 'const';
    d.dataset.ref = ref; d.dataset.side = ref[0];
    d.innerHTML = html;
    return d;
  }
  // When the first term on a side disappears, the new first term drops its "+ " (and "− 4" becomes "−4").
  function fixLeadingSign(sd) {
    const first = sideToks(sd)[0]; if (!first) return;
    first.innerHTML = first.innerHTML.replace(/^\+ /, '').replace(new RegExp('^' + MINUS + ' '), MINUS);
  }
  const tokAt = ref => $('equation').querySelector(`.tok[data-ref="${ref}"]`);
  const sideToks = s => [...$('equation').querySelectorAll(`.tok[data-side="${s}"]`)];

  // ---------------------------------------------------------------- cards
  function label(c) {
    if (c.op === 'comb') return '<span class="clong">Combine</span>';
    if (c.op === 'dist') return '<span class="clong">Distribute</span>';
    if (c.op === 'none') return '<span class="clong">No solution</span>';
    if (c.op === 'all') return '<span class="clong">All x</span>';
    if (c.x) return opSym(c.op) + (c.n === 1 ? '' : c.n) + 'x';
    return null;
  }
  function text(c) {
    if (c.op === 'comb') return 'Combine like terms';
    if (c.op === 'dist') return 'Multiply into the parentheses';
    if (c.op === 'none') return 'Declare: no solution';
    if (c.op === 'all') return 'Declare: every number works';
    if (c.x) { const t = (c.n === 1 ? '' : c.n) + 'x'; return c.op === '+' ? `Add ${t} to both sides` : `Subtract ${t} from both sides`; }
    return null;
  }
  function kind(c) {
    if (c.op === 'comb') return 'Combine';
    if (c.op === 'dist') return 'Distribute';
    if (isDeclare(c)) return 'Declare';
    if (c.x) return c.op === '+' ? 'Add x-term' : 'Subtract x-term';
    return null;
  }

  // Hand: the expected card plus wrong cards that are legal but don't get x closer to alone.
  // Cards that would also make real progress are left out, so the hand has exactly one right answer.
  // A card only turns up as a wrong card once the player has met it (its tutorial is done, or under way),
  // so a stage 4 tutorial never deals Distribute or No solution.
  const known = id => isUnlocked(id) && (progress.tutorialsDone.includes(id) || (typeof fight !== 'undefined' && fight && fight.node && fight.node.skill === id) || SKILL[id].stage <= 3);
  function makeHand2(e, correct, size) {
    const base = steps(e);
    const useful = c => {
      if (isDeclare(c)) return isStatement(e) && (c.op === 'all') === statementTrue(e);
      if (c.op === 'dist') return hasGroup(e);
      if (c.op === 'comb') return ['L', 'R'].some(s => ['x', 'n'].some(k => sideOf(e, s).filter(i => i.t === k).length >= 2));
      return steps(apply(e, c)) < base;
    };
    const classic = [], rest = [];
    if (correct.op === '+' || correct.op === '-') classic.push({ ...correct, op: correct.op === '+' ? '-' : '+' });
    if (correct.op === '/') classic.push({ op: '*', n: correct.n });
    if (correct.op === '*') classic.push({ op: '/', n: correct.n });
    if (correct.op === 'none') classic.push({ op: 'all', scope: 'part' });
    if (correct.op === 'all') classic.push({ op: 'none', scope: 'part' });
    // ◎ cards turn up as wrong cards only when there's nowhere they could go.
    if (known('distribute')) classic.push({ op: 'dist', scope: 'part' });
    if (known('liketerms')) classic.push({ op: 'comb', scope: 'part' });
    if (known('special') && !isDeclare(correct) && Math.random() < 0.5) classic.push({ op: pick(['none', 'all']), scope: 'part' });
    const nums = new Set(), xs = new Set();
    const see = (f, set) => { if (isInt(f) && f.n !== 0) set.add(Math.abs(f.n)); };
    for (const it of [...e.L, ...e.R]) {
      if (it.t === 'g') { see(it.m, nums); it.items.forEach(t => see(t.k, nums)); }
      else if (it.t === 'x') { see(it.k, nums); see(it.k, xs); if (it.k.d > 1) nums.add(it.k.d); }
      else { see(it.k, nums); if (it.k.d > 1) nums.add(it.k.d); }
    }
    for (const n of nums) for (const op of ['+', '-', '*', '/']) rest.push({ op, n });
    if (known('xboth')) for (const n of xs) rest.push({ op: '+', n, x: true }, { op: '-', n, x: true });
    if (isUnlocked('negfrac')) rest.push({ op: 'neg' });
    const legal = c => {
      if (isPart(c) || c.op === 'neg') return true;
      if (!c.n) return false;
      if ((c.op === '*' || c.op === '/') && Math.abs(c.n) < 2) return false;
      return true;
    };
    const seen = new Set([cardLabel(correct)]), hand = [correct];
    const fallback = shuffle([2, 3, 4, 5, 6, 7, 8, 9]).flatMap(n => [{ op: '+', n }, { op: '-', n }]);
    for (const c of [...shuffle(classic), ...shuffle(rest), ...fallback]) {
      if (hand.length >= size) break;
      if (!legal(c) || seen.has(cardLabel(c)) || useful(c)) continue;
      seen.add(cardLabel(c)); hand.push(c);
    }
    return shuffle(hand);
  }

  // ---------------------------------------------------------------- rules
  const refOf = t => (t && t.dataset ? t.dataset.ref : t) || null;
  function isCorrect(cur, card, target) {
    const e = cur.state, ref = refOf(target);
    if (isDeclare(card)) return isStatement(e) && (card.op === 'all') === statementTrue(e);
    if (isPart(card) && !legalPart(e, card, ref)) return false;
    return steps(apply(e, card, ref)) < steps(e);
  }
  function whyWrong(cur, card, target) {
    const e = cur.state, ref = refOf(target), want = cur.path[cur.step].move;
    if (isDeclare(card)) {
      if (!isStatement(e)) return 'x is still in the equation, so it is too early to declare. Keep solving.';
      return statementTrue(e) ? `${eqText(e)} is always true, so every number works.` : `${eqText(e)} is never true, so no number works.`;
    }
    if (card.op === 'dist') return 'Distribute goes on a number in front of parentheses.';
    if (card.op === 'comb') {
      if (ref && /^[LR]\d+$/.test(ref)) {
        const [s, i] = parseRef(ref), it = sideOf(e, s)[i];
        if (it && it.t === 'g') return 'Clear the parentheses before combining what is inside.';
        if (it) return `${plain(it)} has no like term on its side. x-terms combine with x-terms, numbers with numbers.`;
      }
      return 'Drop Combine on one of two like terms on the same side.';
    }
    const after = eqText(apply(e, card, ref));
    if (want.op === 'dist') return `That's allowed, but clear the parentheses first. It would give ${after}`;
    if (want.op === 'comb') return `That's allowed, but combine the like terms first. It would give ${after}`;
    if (want.x) return `That's allowed, but get the x-terms onto one side first. It would give ${after}`;
    if (want.op === '*' && fracItems(e).length >= 2) return `That's allowed, but clear the fractions first: multiply by a number every bottom number goes into. It would give ${after}`;
    if (isDeclare(want)) return `x is gone. Is what's left true or false?`;
    const xs = e.L.some(i => i.t === 'x') ? e.L : e.R;
    if (xs.some(i => i.t === 'n') && (card.op === '*' || card.op === '/' || card.op === 'frac' || card.op === 'neg'))
      return `That's allowed, but undo the + or ${MINUS} part first, then the ${TIMES} or ${DIV}.`;
    return `That's allowed, but x still isn't alone: ${after}`;
  }

  // ---------------------------------------------------------------- animations
  // Each takes (card, before, after, ref). The operation is written under (or over) the term it acts
  // on, the way you'd do it by hand. When it finishes, the equation is re-rendered from `after`.
  const ANIMS = { dist: animDistribute, comb: animCombine, none: animDeclare, all: animDeclare, '+': animAddBoth, '-': animAddBoth };
  const animFor = c => ANIMS[c.op] || animScale;
  const kickClass = (el, cls) => { el.classList.remove(cls); void el.offsetWidth; el.classList.add(cls); };
  const relRect = el => { const r = el.getBoundingClientRect(), q = $('equation').getBoundingClientRect(); return { x: r.left - q.left, y: r.top - q.top, w: r.width, h: r.height }; };
  const glyphRect = el => { const rg = document.createRange(); rg.selectNodeContents(el); const r = rg.getBoundingClientRect(), q = $('equation').getBoundingClientRect(); return { x: r.left - q.left, y: r.top - q.top, w: r.width, h: r.height }; };

  // Add or subtract a number or an x-term on both sides: written under the like term on each side
  // (or at the end of a side that has none). It cancels on one side and combines on the other.
  //   5x + 3 = 2x + 12, subtract 2x  ->  "− 2x" under 5x and under 2x  ->  2x cancels, 5x − 2x = 3x
  async function animAddBoth(card, s, ns) {
    const kindT = card.x ? 'x' : 'n', delta = F(card.op === '+' ? card.n : -card.n);
    const chipT = (card.op === '+' ? '+ ' : MINUS + ' ') + (card.x ? (card.n === 1 ? '' : card.n) + XV : card.n);
    const chipPlain = (card.op === '+' ? '+' : MINUS) + (card.x ? (card.n === 1 ? '' : card.n) + 'x' : card.n);
    caption(text(card) || cardText(card));
    const marks = [];
    for (const sd of ['L', 'R']) {
      const side = sideOf(s, sd); let idx = -1; side.forEach((it, i) => { if (it.t === kindT) idx = i; });
      const toks = sideToks(sd), tk = idx >= 0 ? tokAt(sd + idx) : toks[toks.length - 1];
      marks.push({ sd, idx, tk, n: note(chipT, [tk]) });
    }
    await sleep(1100);
    const cancels = marks.filter(m => m.idx >= 0 && fZero(fAdd(sideOf(s, m.sd)[m.idx].k, delta)));
    if (cancels.length) {
      const it = sideOf(s, cancels[0].sd)[cancels[0].idx];
      caption(`${plain(it)} and ${chipPlain} cancel out (they make 0)`);
      cancels.forEach(m => mark([m.tk, m.n], 'cancel'));
      await sleep(1000);
      cancels.forEach(m => dropNote(m.n));
      await removeTok(cancels.map(m => m.tk));
      ['L', 'R'].forEach(fixLeadingSign);
    }
    const hows = [];
    for (const m of marks) {
      if (cancels.includes(m)) continue;
      mark([m.n], 'merge');
      if (m.idx >= 0) {
        const old = sideOf(s, m.sd)[m.idx], k = fAdd(old.k, delta), nt = { t: kindT, k };
        hows.push(`${plain(old)} ${chipPlain.replace(/^(.)/, '$1 ')} = ${plain(nt)}`);
        m.tk.classList.add('merge');
      }
    }
    if (hows.length) caption(hows.join(',  '));
    await sleep(800);
    for (const m of marks) {
      if (cancels.includes(m)) continue;
      dropNote(m.n);
      if (m.idx >= 0) {
        const old = sideOf(s, m.sd)[m.idx], k = fAdd(old.k, delta);
        // The term's position on its side may change once a term in front of it cancels, so take
        // the sign style from the new state.
        const nside = sideOf(ns, m.sd), ni = nside.findIndex(it => it.t === kindT && fEq(it.k, k));
        m.tk.classList.remove('merge');
        m.tk.innerHTML = termStr({ t: kindT, k }, ni <= 0, true);
        kickClass(m.tk, 'pop');
      }
    }
    await sleep(700);
  }

  // Multiply or divide both sides (also × −1, × reciprocal, × the common denominator).
  //   ÷: a fraction bar with the divisor slides in under each whole side, then every term divides.
  //   ×: the multiplier is stamped under every term; denominators it clears pop away.
  async function animScale(card, s, ns) {
    const m = cardFactor(card);
    caption(cardText(card));
    const ns_ = [];
    if (card.op === '/') {
      for (const sd of ['L', 'R']) ns_.push(note(paren(F(card.n)), sideToks(sd), { bar: true }));
    } else {
      for (const t of $('equation').querySelectorAll('.tok.a2')) { ns_.push(note(chipHtml(card), [t])); await sleep(160); }
    }
    await sleep(1000);
    // Captions: what happens to the x-term, and to the other side if it is one number.
    const sides = ['L', 'R'].map(sd => ({ sd, side: sideOf(s, sd), nside: sideOf(ns, sd) }));
    const fr = fracItems(s).length >= 2;
    if (fr) caption(`${card.n} is a multiple of every bottom number, so the fractions clear`);
    else if (card.op === '/') {
      const xt = sides.find(o => o.side.length === 1 && o.side[0].t === 'x');
      caption(xt ? `${plain(xt.side[0])} over ${card.n} is ${plain(xt.nside[0] || X(0))}` : `Every term is divided by ${card.n}`);
    } else if (card.op === 'neg') caption(`Multiplying by ${MINUS}1 flips the sign of every term`);
    else caption(`Every term is multiplied by ${fracText(m)}`);
    // Denominators that clear pop away first.
    let popped = false;
    for (const t of $('equation').querySelectorAll('.tok.a2 .den')) { t.classList.add('cancel'); popped = true; }
    for (const t of $('equation').querySelectorAll('.tok.a2 .cf')) if (card.op === '/' || card.op === 'frac') t.classList.add('cancel');
    if (popped || card.op === '/') await sleep(800);
    ns_.forEach(n => mark([n], 'merge'));
    for (const o of sides) {
      // Terms keep their positions when scaled, unless parentheses with a 1 in front opened up.
      const same = o.side.length === o.nside.length && o.side.every((it, i) => it.t === o.nside[i].t);
      if (!same) continue;
      o.side.forEach((it, i) => {
        const tk = tokAt(o.sd + i); if (!tk) return;
        tk.innerHTML = termStr(o.nside[i], i === 0, true);
        kickClass(tk, card.op === 'neg' ? 'flip' : 'pop');
      });
    }
    await sleep(500);
    ns_.forEach(dropNote);
    await sleep(500);
  }

  // Distribute: arrows sweep from the number in front to each term inside, the products are written
  // under each term, then the parentheses dissolve.
  //   3(x + 2)  ->  3·x and 3·2  ->  3x + 6
  async function animDistribute(card, s, ns, ref) {
    const [sd, i] = parseRef(ref), g = sideOf(s, sd)[i], tk = tokAt(ref);
    const prods = g.items.map(t => ({ t: t.t, k: fMul(t.k, g.m) }));
    caption(`Distribute: multiply ${fracText(g.m)} by each term inside the parentheses`);
    const gm = tk.querySelector('.gm'), gis = [...tk.querySelectorAll('.gi')];
    // Arrows: drawn over the group, from the multiplier to each inner term.
    const a = glyphRect(gm.textContent ? gm : tk.querySelector('.gp'));
    const svgNS = 'http://www.w3.org/2000/svg', svg = document.createElementNS(svgNS, 'svg');
    svg.setAttribute('class', 'a2arrows');
    const box = relRect(tk), gl = glyphRect(tk), top = gl.y - 34;
    Object.assign(svg.style, { left: box.x + 'px', top: top + 'px', width: box.w + 'px', height: '40px' });
    svg.setAttribute('viewBox', `0 0 ${box.w} 40`);
    svg.innerHTML = '<defs><marker id="a2head" viewBox="0 0 10 10" refX="7" refY="5" markerUnits="userSpaceOnUse" markerWidth="14" markerHeight="14" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="currentColor"/></marker></defs>';
    const x0 = a.x + a.w / 2 - box.x, y0 = 38;
    for (const gi of gis) {
      const r = glyphRect(gi), x1 = r.x + r.w * 0.6 - box.x;
      const p = document.createElementNS(svgNS, 'path');
      p.setAttribute('d', `M${x0},${y0} Q${(x0 + x1) / 2},${-14} ${x1},${y0}`);
      p.setAttribute('marker-end', 'url(#a2head)');
      svg.appendChild(p);
    }
    $('equation').appendChild(svg);
    gm.classList.add('hot');
    await sleep(1000);
    const notesHere = gis.map((gi, j) => note(termStr(prods[j], j === 0 && i === 0, true), [gi]));
    caption(g.items.map((t, j) => { const f = termStr(t, true, false); return `${paren(g.m)} ${TIMES} ${t.k.n < 0 ? '(' + f + ')' : f} = ${plain(prods[j])}`; }).join(',  '));
    await sleep(1300);
    tk.querySelectorAll('.gp, .gm').forEach(el => el.classList.add('fade'));
    svg.classList.add('fade');
    await sleep(500);
    notesHere.forEach(n => mark([n], 'merge'));
    tk.innerHTML = `<span>${prods.map((t, j) => termStr(t, j === 0 && i === 0, true)).join(' ')}</span>`;
    kickClass(tk, 'pop');
    notesHere.forEach(dropNote);
    await sleep(700);
    svg.remove();
  }

  // Combine like terms: the matching terms light up, slide together, and their numbers add.
  //   3x + 2x − 4  ->  5x − 4
  async function animCombine(card, s, ns, ref) {
    const [sd, i] = parseRef(ref), side = sideOf(s, sd), kindT = side[i].t;
    const idxs = side.map((it, j) => (it.t === kindT ? j : -1)).filter(j => j >= 0);
    const toks = idxs.map(j => tokAt(sd + j));
    let sum = F(0); idxs.forEach(j => { sum = fAdd(sum, side[j].k); });
    const sumT = { t: kindT, k: sum };
    caption(`Like terms: ${idxs.map((j, n) => termStr(side[j], n === 0, false)).join(' ')} = ${fZero(sum) ? '0' : plain(sumT)}`);
    mark(toks, 'like');
    await sleep(900);
    const r0 = relRect(toks[0]);
    toks.slice(1).forEach(t => { const r = relRect(t); t.style.transform = `translateX(${r0.x - r.x}px) scale(.6)`; t.style.opacity = '0'; });
    await sleep(600);
    toks.slice(1).forEach(t => t.remove());
    toks[0].classList.remove('like');
    fixLeadingSign(sd);
    if (fZero(sum)) { mark([toks[0]], 'cancel'); await sleep(600); await removeTok([toks[0]]); return; }
    toks[0].innerHTML = termStr(sumT, idxs[0] === 0, true);
    kickClass(toks[0], 'pop');
    await sleep(700);
  }

  // Declare: a false statement (1 = 5) cracks and shatters; a true one (6 = 6) glows.
  async function animDeclare(card, s) {
    const toks = [...$('equation').querySelectorAll('.tok')];
    if (card.op === 'none') {
      caption(`${eqText(s)} is never true, so no number can be x: no solution`);
      const r = relRect(toks[0]), last = relRect(toks[toks.length - 1]);
      const svgNS = 'http://www.w3.org/2000/svg', svg = document.createElementNS(svgNS, 'svg');
      svg.setAttribute('class', 'a2crack');
      Object.assign(svg.style, { left: r.x + 'px', top: r.y + 'px', width: (last.x + last.w - r.x) + 'px', height: r.h + 'px' });
      const w = last.x + last.w - r.x, h = r.h; let d = `M0,${h / 2}`;
      for (let k = 1; k <= 8; k++) d += ` L${(w * k) / 8},${h / 2 + (k % 2 ? -1 : 1) * h * 0.22}`;
      svg.setAttribute('viewBox', `0 0 ${w} ${h}`);
      svg.innerHTML = `<path d="${d}"/>`;
      $('equation').appendChild(svg);
      kickClass($('equation'), 'shake');
      await sleep(900);
      svg.remove();
      toks.forEach(t => { t.style.transform = `translate(${rand(-50, 50)}px, ${rand(60, 140)}px) rotate(${rand(-70, 70)}deg)`; t.style.opacity = '0'; });
      await sleep(800);
    } else {
      caption(`${eqText(s)} is always true, so every number works for x`);
      mark(toks, 'glow');
      await sleep(1700);
    }
  }

  // ---------------------------------------------------------------- generators
  // Every generator returns { eq, enemy } with a whole-number answer.
  function genLike(type) {
    for (;;) {
      const t = type || pick(['xx', 'xxc', 'xxc', 'cc', 'split', 'rhs']);
      const x = rand(1, 9);
      if (t === 'xx') { const a = rand(2, 7), b = rand(1, 6); return { eq: E([X(a), X(b)], [N((a + b) * x)]), enemy: 'clutter' }; }
      if (t === 'xxc') {
        const a = rand(2, 8), b = pick([1, -1]) * rand(1, 6), c = nonZero(-9, 9);
        if (a + b < 2) continue;
        return { eq: maybeSwap(E([X(a), X(b), N(c)], [N((a + b) * x + c)])), enemy: 'clutter' };
      }
      if (t === 'cc') {
        const a = rand(2, 6), c1 = rand(1, 9), c2 = pick([1, -1]) * rand(1, 9);
        if (c1 + c2 === 0) continue;
        return { eq: maybeSwap(E([X(a), N(c1), N(c2)], [N(a * x + c1 + c2)])), enemy: 'clutter' };
      }
      if (t === 'split') { const a = rand(2, 6), b = rand(1, 5), c = nonZero(-9, 9); return { eq: maybeSwap(E([X(a), N(c), X(b)], [N((a + b) * x + c)])), enemy: 'clutter' }; }
      const a = rand(1, 5), b = rand(2, 6); return { eq: E([N((a + b) * x)], [X(a), X(b)]), enemy: 'clutter' };
    }
  }
  function genDist(type) {
    for (;;) {
      const t = type || pick(['plain', 'plain', 'neg', 'inner', 'plus', 'plusx']);
      const x = type ? rand(1, 9) : rand(-3, 9), a = rand(2, 6), b = nonZero(-8, 9);   // tutorials keep x positive
      if (x + b === 0) continue;
      if (t === 'plain') return { eq: maybeSwap(E([G(a, [X(1), N(b)])], [N(a * (x + b))])), enemy: 'distributor' };
      if (t === 'minus') { const bb = rand(1, 8); if (x - bb === 0) continue; return { eq: E([G(a, [X(1), N(-bb)])], [N(a * (x - bb))]), enemy: 'distributor' }; }
      if (t === 'neg') { const m = -rand(2, 5); return { eq: E([G(m, [X(1), N(b)])], [N(m * (x + b))]), enemy: 'distributor' }; }
      if (t === 'inner') { const p = rand(2, 4), q = nonZero(-6, 6), aa = rand(2, 4); if (p * x + q === 0) continue; return { eq: E([G(aa, [X(p), N(q)])], [N(aa * (p * x + q))]), enemy: 'distributor' }; }
      if (t === 'plus') { const c = nonZero(-9, 9); return { eq: maybeSwap(E([G(a, [X(1), N(b)]), N(c)], [N(a * (x + b) + c)])), enemy: 'distributor' }; }
      return { eq: maybeSwap(E([G(a, [X(1), N(b)]), X(1)], [N(a * (x + b) + x)])), enemy: 'distributor' };
    }
  }
  function genXBoth(type) {
    for (;;) {
      const t = type || pick(['basic', 'basic', 'basic', 'noconst']);
      const x = t === 'tut' ? rand(1, 9) : nonZero(-6, 10);
      if (t === 'tut') { const c = rand(1, 4), a = c + rand(1, 5), b = rand(1, 9), d = a * x + b - c * x; if (d <= 0) continue; return { eq: E([X(a), N(b)], [X(c), N(d)]), enemy: 'twin' }; }
      const a = rand(1, 9), c = rand(1, 9); if (a === c) continue;
      if (t === 'noconst' || t === 'tut2') { const d = (a - c) * x; if (t === 'tut2' && (a < c || d <= 0)) continue; return { eq: E([X(a)], [X(c), N(d)]), enemy: 'twin' }; }
      const b = nonZero(-12, 12), d = a * x + b - c * x;
      return { eq: E([X(a), N(b)], d ? [X(c), N(d)] : [X(c)]), enemy: 'twin' };
    }
  }
  const FRAC_PAIRS = [[2, 3], [3, 4], [2, 5], [2, 4], [3, 6], [4, 6], [2, 6], [3, 5], [4, 5]];
  function genClearFrac(type) {
    for (;;) {
      const t = type || pick(['sum', 'sum', 'diff', 'const', 'coef']);
      const [p, q] = pick(FRAC_PAIRS), L = lcm(p, q), x = L * rand(1, 3);
      if (t === 'sum') return { eq: E([X(F(1, p)), X(F(1, q))], [N(x / p + x / q)]), enemy: 'clutter' };
      if (t === 'diff') { const v = x / p - x / q; if (!v) continue; return { eq: E([X(F(1, p)), X(F(-1, q))], [N(v)]), enemy: 'clutter' }; }
      if (t === 'const') { const d = nonZero(-6, 6); return { eq: E([X(F(1, p)), X(F(1, q)), N(d)], [N(x / p + x / q + d)]), enemy: 'clutter' }; }
      const a = rand(2, 3); if (gcd(a, p) !== 1) continue;
      return { eq: E([X(F(a, p)), X(F(1, q))], [N((a * x) / p + x / q)]), enemy: 'clutter' };
    }
  }
  function genSpecial(type) {
    for (;;) {
      const t = type || pick(['none', 'all', 'nonec', 'allc', 'one', 'one']);
      const a = rand(2, 6), b = nonZero(-9, 9);
      if (t === 'none') { const d = nonZero(-9, 9); if (d === b) continue; return { eq: maybeSwap(E([X(a), N(b)], [X(a), N(d)])), enemy: 'twin' }; }
      if (t === 'all') return { eq: E([G(a, [X(1), N(b)])], [X(a), N(a * b)]), enemy: 'twin' };
      if (t === 'nonec') { const c = nonZero(-12, 12); if (c === a * b) continue; return { eq: E([G(a, [X(1), N(b)])], [X(a), N(c)]), enemy: 'twin' }; }
      if (t === 'allc') { const p = rand(1, a - 1); return { eq: maybeSwap(E([X(p), X(a - p), N(b)], [X(a), N(b)])), enemy: 'twin' }; }
      return genXBoth();       // an ordinary one with a single answer, so declaring can't be a habit
    }
  }

  // Elites stack two recent concepts in one equation; the newest Act 2 concept decides the shape.
  function genStacked2(recent) {
    const newest = [...recent].reverse().find(id => (SKILL[id].act || 1) === 2);
    for (;;) {
      const x = nonZero(-5, 9);
      if (newest === 'liketerms') {        // like terms whose total is negative: 2x − 5x + 4 = 13
        const a = rand(1, 5), b = -rand(a + 1, a + 6), c = nonZero(-9, 9);
        return { eq: maybeSwap(E([X(a), X(b), N(c)], [N((a + b) * x + c)])), enemy: 'bracketknight' };
      }
      if (newest === 'distribute') {
        const a = rand(2, 5), b = nonZero(-6, 6), c = rand(2, 4);
        if (pick([0, 1])) { const m = -a, k = nonZero(-9, 9); if (x + b === 0) continue; return { eq: E([G(m, [X(1), N(b)]), N(k)], [N(m * (x + b) + k)]), enemy: 'bracketknight' }; }
        return { eq: maybeSwap(E([G(a, [X(1), N(b)]), X(c)], [N(a * (x + b) + c * x)])), enemy: 'bracketknight' };
      }
      if (newest === 'xboth') {           // 3(x + 2) = 2x + 9
        const a = rand(2, 6), b = nonZero(-6, 6), c = rand(1, 7); if (a === c) continue;
        const d = a * (x + b) - c * x;
        return { eq: maybeSwap(E([G(a, [X(1), N(b)])], d ? [X(c), N(d)] : [X(c)])), enemy: 'bracketknight' };
      }
      if (newest === 'clearfrac') {       // x/2 = x/3 + 1
        const [p, q] = pick(FRAC_PAIRS), L = lcm(p, q), xx = L * rand(1, 3), c = xx / p - xx / q;
        if (pick([0, 1])) { const d = nonZero(-6, 6); return { eq: E([X(F(1, p)), X(F(1, q)), N(d)], [N(xx / p + xx / q + d)]), enemy: 'bracketknight' }; }
        return { eq: maybeSwap(E([X(F(1, p))], [X(F(1, q)), N(c)])), enemy: 'bracketknight' };
      }
      // special: a(x + b) + c = ax + d, none or all
      const a = rand(2, 5), b = nonZero(-6, 6), c = nonZero(-9, 9), all = Math.random() < 0.5;
      const d = all ? a * b + c : a * b + c + nonZero(-5, 5);
      return { eq: maybeSwap(E([G(a, [X(1), N(b)]), N(c)], [X(a), N(d)])), enemy: 'bracketknight' };
    }
  }

  // Act 2 elite and boss fights. list = the unlocked skills this run can use, oldest first.
  function buildFight2(node, list) {
    const act2 = list.filter(id => (SKILL[id].act || 1) === 2);
    if (node.type === 'elite') return { phases: [() => genStacked2(list.slice(-2))], handSize: 4, enemy: 'bracketknight' };
    // Boss: one phase per Act 2 stage (sides swap from phase 2), then two concepts at once.
    const phases = act2.map((id, i) => () => { const g = SKILL[id].gen(); if (i > 0) g.eq = swapSides(g.eq); return g; });
    phases.push(() => { const g = genStacked2(list.slice(-2)); if (Math.random() < 0.5) g.eq = swapSides(g.eq); return g; });
    if (act2.length === 1) phases.splice(1, 0, () => { const g = genStacked2(list.slice(-2)); return g; });
    return { phases, handSize: 4, enemy: 'archivist' };
  }

  // ---------------------------------------------------------------- skills and enemies
  SKILLS.push(
    { id: 'liketerms', stage: 4, act: 2, name: 'Like terms', gen: () => genLike(),
      title: 'Stage 4: Like terms',
      intro: 'New ◎ card: Combine. Terms of the same kind can be added together: x-terms with x-terms, numbers with numbers. Drop Combine on one of them and they merge into one.',
      example: '3x + 2x − 4 = 11<br>Combine 3x and 2x → 5x − 4 = 11<br>Add 4 to both sides → 5x = 15<br>Divide both sides by 5 → x = 3',
      tutorial: [() => genLike('xx'), () => genLike('cc')] },
    { id: 'distribute', stage: 5, act: 2, name: 'Distributing', gen: () => genDist(),
      title: 'Stage 5: The distributive property',
      intro: 'New ◎ card: Distribute. A number in front of parentheses multiplies everything inside. Drop Distribute on the parentheses to multiply it in and clear them.',
      example: '3(x + 2) = 15<br>Distribute → 3x + 6 = 15<br>Subtract 6 from both sides → 3x = 9<br>Divide both sides by 3 → x = 3',
      tutorial: [() => genDist('plain'), () => genDist('minus')] },
    { id: 'xboth', stage: 6, act: 2, name: 'x on both sides', gen: () => genXBoth(),
      title: 'Stage 6: x on both sides',
      intro: 'Now x appears on both sides. Subtract the smaller x-term from both sides: it cancels on one side and combines on the other. Then solve as before.',
      example: '5x + 3 = 2x + 12<br>Subtract 2x from both sides → 3x + 3 = 12<br>Subtract 3 → 3x = 9<br>Divide by 3 → x = 3',
      tutorial: [() => genXBoth('tut'), () => genXBoth('tut2')] },
    { id: 'clearfrac', stage: 7, act: 2, name: 'Clearing fractions', gen: () => genClearFrac(),
      title: 'Stage 7: Clearing fractions',
      intro: 'Several fractions? Multiply both sides by a number that every bottom number goes into (the common denominator). Every fraction clears at once.',
      example: '<span class="frac"><span>x</span><span>3</span></span> + <span class="frac"><span>x</span><span>4</span></span> = 7<br>Multiply both sides by 12 → 4x + 3x = 84<br>Combine → 7x = 84<br>Divide by 7 → x = 12',
      tutorial: [() => genClearFrac('sum'), () => genClearFrac('sum')] },
    { id: 'special', stage: 8, act: 2, name: 'No solution / every x', gen: () => genSpecial(),
      title: 'Stage 8: No solution, or every number',
      intro: 'Sometimes the x-terms cancel completely. If what is left is false (1 = 5), no number works: play ◎ No solution. If it is true (6 = 6), every number works: play ◎ All x. Drop them on the statement.',
      example: '2x + 1 = 2x + 5<br>Subtract 2x → 1 = 5<br>Never true → No solution<br><br>3(x + 1) = 3x + 3<br>Distribute → 3x + 3 = 3x + 3<br>Subtract 3x → 3 = 3<br>Always true → every number works',
      tutorial: [() => genSpecial('none'), () => genSpecial('all')] },
  );
  for (const s of SKILLS) SKILL[s.id] = s;
  progress = loadProgress();     // the save was first read before these skills existed

  Object.assign(ENEMIES, {
    clutter:       { name: 'Clutter Golem', rank: 'Normal', color: '#b08968', size: 84 },
    distributor:   { name: 'Distributor',   rank: 'Normal', color: '#c77dff', size: 84 },
    twin:          { name: 'Twin',          rank: 'Normal', color: '#4cc9f0', size: 84 },
    bracketknight: { name: 'Bracket Knight', rank: 'Elite', color: '#adb5bd', size: 100, horns: true },
    archivist:     { name: 'The Archivist', rank: 'Boss',   color: '#9d4edd', size: 120, crown: true },
  });
  ACTS[2] = { name: 'The Bracket Halls', sub: 'Rearranging', boss: 'The Archivist', firstSkill: 'liketerms',
    blurb: 'The equations here hide x inside parentheses, scatter it across both sides and split it into fractions. Gather the pieces and get x alone. Defeat The Archivist.' };

  // Act 2 styles live here so index.html only needs the script tag.
  const css = document.createElement('style');
  css.textContent = `
    #equation.a2long { font-size: calc(var(--eqSize) * .78); }
    @media (max-width: 640px) { .tok.a2 { min-width:0; padding-left:3px; padding-right:3px; } }
    .card .clong { font-size:.62em; white-space:nowrap; }
    .tok.a2 .xv { font-style:normal; color:var(--accent); }
    .tok.a2.k-g { max-width:none; }
    .tok.a2 .gp, .tok.a2 .gm { display:inline-block; transition: opacity calc(.45s * var(--k)), transform calc(.45s * var(--k)), color calc(.3s * var(--k)); }
    .tok.a2 .gm.hot { color:#7bdff2; }
    .tok.a2 .fade { opacity:0; transform:scale(.4); }
    .tok.a2 .frac .den.cancel, .tok.a2 .cf.cancel { color:var(--bad); text-decoration:line-through; }
    .tok.a2.like { color:#7bdff2; background:#7bdff222; border-color:#7bdff2; }
    .tok.a2.k-result { color:var(--good); font-size:.7em; max-width:none; white-space:normal; }
    .tok.glow { animation: a2glow calc(.8s * var(--k)) ease-in-out 2; color:var(--good); }
    @keyframes a2glow { 50% { text-shadow: 0 0 22px #06d6a0, 0 0 6px #fff; transform: scale(1.08); } }
    .a2arrows { position:absolute; pointer-events:none; overflow:visible; color:#7bdff2; z-index:2; }
    .a2arrows path { fill:none; stroke:currentColor; stroke-width:4; stroke-linecap:round; stroke-dasharray:400; stroke-dashoffset:400; animation: a2draw calc(.7s * var(--k)) ease-out forwards; }
    .a2arrows.fade { opacity:0; transition: opacity calc(.4s * var(--k)); }
    @keyframes a2draw { to { stroke-dashoffset:0; } }
    .a2crack { position:absolute; pointer-events:none; overflow:visible; z-index:2; }
    .a2crack path { fill:none; stroke:var(--bad); stroke-width:5; stroke-linejoin:bevel; stroke-dasharray:1200; stroke-dashoffset:1200; animation: a2draw calc(.6s * var(--k)) ease-in forwards; }
    .tok.a2 { transition: background .15s, border-color .15s, max-width calc(.45s * var(--k)), min-width calc(.45s * var(--k)), padding calc(.45s * var(--k)), opacity calc(.6s * var(--k)), transform calc(.6s * var(--k)), color calc(.3s * var(--k)); }
  `;
  document.head.appendChild(css);

  window.ACT2 = { apply, canon, steps, isSolved, makeEquation: makeEquation2, refreshPath, render, eqText, makeHand: makeHand2,
    isCorrect, whyWrong, animFor, label, text, kind, buildFight: buildFight2, genStacked: genStacked2,
    gens: { liketerms: genLike, distribute: genDist, xboth: genXBoth, clearfrac: genClearFrac, special: genSpecial } };
})();
