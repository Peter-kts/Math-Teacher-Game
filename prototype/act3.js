// =====================================================================
//  Act 3: The Leaning Stacks (Inequalities)
// =====================================================================
// Stage 10: linear inequalities. They are solved with the same moves as equations, plus one rule:
// multiplying or dividing both sides by a negative number flips the sign (< becomes >).
//
// The equation model is Act 2's (see act2.js) with one more field:
//   ineq = { L: [item...], R: [item...], result: null, rel: '<' | '≤' | '>' | '≥' }
// Act 2's engine does the algebra (apply, the expected path, hands, animations). This file adds the
// relation on top: it flips the sign on a negative × or ÷, renders it, labels those cards "flip the
// sign", draws the answer on a number line, and has its own wrong-move messages, Why? text and traps.
//
// Generators return { ineq } and index.html picks this engine for them (cur.act3). ENGINES.ineq plugs it
// into the shared variety system (no repeats in a run, shapes rotate, sides mirrored).
//
// The number line (drawLine) is a reusable system for the rest of the act: it draws any set made of
// intervals, so compound inequalities (between, or outside) and absolute value can use it later.
'use strict';
(function () {
  const A2 = window.ACT2;
  if (!A2) return;
  const N = k => ({ t: 'n', k: typeof k === 'number' ? F(k) : k });
  const X = k => ({ t: 'x', k: typeof k === 'number' ? F(k) : k });
  const G = (m, items) => ({ t: 'g', m: typeof m === 'number' ? F(m) : m, items });
  const noZero = side => side.filter(i => !(i.t === 'n' && i.k.n === 0));
  const FLIP = { '<': '>', '>': '<', '≤': '≥', '≥': '≤' };
  const RELS = ['<', '≤', '>', '≥'];
  const I = (L, R, rel) => ({ L: noZero(L), R: noZero(R), result: null, rel: rel || pick(RELS) });
  const swapI = e => ({ ...e, L: e.R, R: e.L, rel: FLIP[e.rel] });         // 9 > 2x + 1 is the same as 2x + 1 < 9
  const constOf = side => { const c = side.find(i => i.t === 'n'); return c ? c.k : F(0); };
  const isDeclare = c => c.op === 'none' || c.op === 'all';
  const SCALE_OPS = ['*', '/', 'neg', 'frac'];
  // Does this card multiply or divide both sides by a negative number? Those flip the sign.
  const negScale = c => SCALE_OPS.includes(c.op) && !c.lcd && cardFactor(c).n < 0;

  // ---------------------------------------------------------------- moves
  function apply(e, c, ref) {
    const a = A2.apply(e, c, ref);
    a.rel = negScale(c) ? FLIP[e.rel] : e.rel;
    return a;
  }
  const isSolved = e => A2.isSolved(e);
  // The answer, written with x first: "3 < x" reads as x > 3.
  function solution(e) {
    if (!isSolved(e)) return null;
    const xLeft = e.L.length === 1 && e.L[0].t === 'x';
    return { v: constOf(xLeft ? e.R : e.L), rel: xLeft ? e.rel : FLIP[e.rel] };
  }
  // The answer as a set of intervals for the number line. lo/hi can be ±Infinity.
  function segmentsOf(sol) {
    const v = sol.v.n / sol.v.d, closed = sol.rel === '≤' || sol.rel === '≥';
    return sol.rel === '<' || sol.rel === '≤'
      ? [{ lo: -Infinity, hi: v, hiC: closed, hiF: sol.v }]
      : [{ lo: v, hi: Infinity, loC: closed, loF: sol.v }];
  }

  // Path skills: plain steps (+ − × ÷) in an inequality fight practise the inequality stage, so the
  // fight's mastery goes to it. Act 2 moves (Distribute, Combine, x on both sides) keep their own skill.
  const PLAIN = ['onestep', 'twostep', 'negfrac'];
  function retag(path, main) { for (const p of path) if (PLAIN.includes(p.skill)) p.skill = main; }

  function makeEquation3(eq, enemy) {
    const c = A2.makeEquation(eq, enemy);
    const main = eq.skill || 'ineq';
    retag(c.path, main);
    let e = eq; for (const p of c.path) e = apply(e, p.move, p.move.ref);
    const sol = solution(e);
    return { ...c, end: e, main, skills: [...new Set(c.path.map(p => p.skill))], act2: true, act3: true,
      answerText: sol ? `x ${sol.rel} ${fracText(sol.v)}` : eqText(e) };
  }
  function refreshPath(cur) { A2.refreshPath(cur); retag(cur.path, cur.main); }

  // ---------------------------------------------------------------- text
  const eqText = e => A2.eqText(e).replace(' = ', ` ${e.rel} `);
  const eqH = e => `<span class="whyEq"><span>${A2.sideStr(e.L, true)}</span><span>${e.rel}</span><span>${A2.sideStr(e.R, true)}</span></span>`;
  function scaleBase(c) {
    if (c.op === 'neg') return TIMES + '(' + MINUS + '1)';
    if (c.op === 'frac') return TIMES + paren(F(c.n, c.d));
    return (c.op === '/' ? DIV : TIMES) + paren(F(c.n));
  }
  // A card that multiplies or divides by a negative says so on its face: "flip ≥ to ≤". The Expert trap
  // looks the same but says "keep ≥". The small text is the plain "Divide both sides by −3" on both.
  function label(c) {
    if (c.flip) return `${scaleBase(c)}<span class="ftag">flip ${c.rel ? `${c.rel} to ${FLIP[c.rel]}` : 'sign'}</span>`;
    if (c.op === 'trap' && c.trap === 'no flip') return `${c.label}<span class="ftag keep">keep ${c.rel}</span>`;
    return null;
  }
  const byText = c => (c.op === 'neg' ? MINUS + '1' : c.op === 'frac' ? fracText(F(c.n, c.d)) : numText(c.n));
  const scaleText = c => `${c.op === '/' ? 'Divide both sides by' : 'Multiply both sides by'} ${byText(c)}`;
  function text(c) {
    if (c.flip) return scaleText(c);
    if (c.op === 'trap' && c.trap === 'no flip') return scaleText({ ...c, op: c.scaleOp });
    return null;
  }
  function kind(c) {
    if (!c.flip) return null;
    return c.op === '/' ? 'Divide by a negative (flip)' : 'Multiply by a negative (flip)';
  }

  // ---------------------------------------------------------------- hands
  const isTutorial = () => typeof fight !== 'undefined' && fight && fight.node && fight.node.type === 'tutorial';
  // Expert trap: the same × or ÷ by a negative, but keeping the sign. It is the classic inequality mistake.
  function noFlipTrap(e, correct) {
    const wrongRel = e.rel, wrong = A2.apply(e, correct, correct.ref);   // Act 2's apply leaves the sign alone
    wrong.rel = wrongRel;
    const sol = solution(wrong), right = solution(apply(e, correct, correct.ref));
    let test = '';
    if (sol && right) {
      // A number that fits the wrong answer but not the real one: just past the boundary on the wrong side.
      const v = sol.v.n / sol.v.d, t = sol.rel === '<' || sol.rel === '≤' ? Math.floor(v) - 1 : Math.ceil(v) + 1;
      const l = evalSide(e.L, t), r = evalSide(e.R, t);
      test = ` Check with x = ${numText(t)}: it fits x ${sol.rel} ${fracText(sol.v)}, but in ${eqH(e)} it gives ${fracText(l)} ${e.rel} ${fracText(r)}, which is false. The real answer is x ${right.rel} ${fracText(right.v)}.`;
    }
    return { op: 'trap', trap: 'no flip', rel: e.rel, n: correct.n, d: correct.d, scaleOp: correct.op, label: scaleBase(correct), text: scaleText(correct),
      why: `<p>Multiplying or dividing both sides by a negative number flips the order of everything: 2 &lt; 3, but ${MINUS}2 &gt; ${MINUS}3. So the sign has to flip too. Keeping it gives an answer that isn't true.${test}</p>` };
  }
  // The value of one side when x = t.
  function evalSide(side, t) {
    const val = it => (it.t === 'n' ? it.k : it.t === 'x' ? fMul(it.k, F(t)) : fMul(it.m, it.items.reduce((a, i) => fAdd(a, val(i)), F(0))));
    return side.reduce((a, it) => fAdd(a, val(it)), F(0));
  }
  function makeHand3(e, correct, size) {
    const tut = isTutorial();
    let hand = A2.makeHand(e, correct, size).filter(c => !isDeclare(c) && !(c.op === 'trap' && (tut || c.trap === 'lost sign')));
    if (!tut && difficulty.level >= 3 && negScale(correct) && size > 2) hand.splice(1, 0, noFlipTrap(e, correct));
    // Top up with + and − cards that don't help, if filtering made the hand short.
    const labels = new Set(hand.map(cardLabel));
    for (const n of shuffle([2, 3, 4, 5, 6, 7, 8, 9])) for (const op of ['+', '-']) {
      if (hand.length >= size) break;
      const c = { op, n };
      if (labels.has(cardLabel(c)) || A2.isCorrect({ state: e }, c)) continue;
      labels.add(cardLabel(c)); hand.push(c);
    }
    // The trap pushed the hand one over: drop a wrong card (never the right one or the trap).
    while (hand.length > size) { const i = hand.findIndex(c => c.op !== 'trap' && !isCorrect({ state: e }, c)); if (i < 0) break; hand.splice(i, 1); }
    return shuffle(hand.map(c => (negScale(c) ? { ...c, flip: true, rel: e.rel } : c)));
  }

  // ---------------------------------------------------------------- rules
  const isCorrect = (cur, card, target) => card.op !== 'trap' && !isDeclare(card) && A2.isCorrect(cur, card, target);
  function whyWrong(cur, card, target) {
    const e = cur.state, want = cur.path[cur.step].move, ref = target && target.dataset ? target.dataset.ref : target;
    if (card.op === 'trap' && card.trap === 'no flip') return `That's a trap: dividing or multiplying by a negative flips the sign. Tap Why? to see why.`;
    if (card.op === 'trap') return `That's a trap: it isn't true. Tap Why? to see why.`;
    if (isDeclare(card)) return 'x is still here, so keep solving.';
    if (card.op === 'dist' || card.op === 'comb') return A2.whyWrong(cur, card, target);
    const after = eqText(apply(e, card, ref));
    if (want.op === 'dist') return `That's allowed, but clear the parentheses first. It would give ${after}`;
    if (want.op === 'comb') return `That's allowed, but combine the like terms first. It would give ${after}`;
    if (want.x) return `That's allowed, but get the x-terms onto one side first. It would give ${after}`;
    const xs = e.L.some(i => i.t === 'x') ? e.L : e.R;
    if (xs.some(i => i.t === 'n') && SCALE_OPS.includes(card.op))
      return `That's allowed, but undo the + or ${MINUS} part first, then the ${TIMES} or ${DIV}.`;
    return `That's allowed, but x still isn't alone: ${after}`;
  }

  // "Why?" for inequalities. Trap cards carry their own text (card.why).
  function explain3({ state: e, card, correct, ref }) {
    if (!e || !e.rel || !card || !correct) return null;
    const P = t => `<p>${t}</p>`, out = [];
    if (card.op === 'comb') out.push(P('Like terms have the same letter part: x-terms combine with x-terms, and plain numbers with plain numbers. Combine needs two of the same kind on the same side, outside any parentheses.'));
    else if (card.op === 'dist') out.push(P('Distribute multiplies the number in front of a pair of parentheses into every term inside, so it has to be dropped on the parentheses.'));
    else if (isDeclare(card)) out.push(P('x is still in the inequality, so there is nothing to declare yet. Keep solving.'));
    else {
      const after = apply(e, card, ref);
      out.push(P(`${cardText(card)} is allowed, but it turns it into ${eqH(after)}, which is no closer to x alone.`));
      if (negScale(card)) out.push(P(`It ${card.op === '/' ? 'divides' : 'multiplies'} by a negative number, so the sign flipped from ${e.rel} to ${after.rel}. That part was right, but it wasn't the move needed here.`));
    }
    const m = correct;
    let how;
    if (m.op === 'dist') how = 'Clear the parentheses first: multiply the number in front into each term inside.';
    else if (m.op === 'comb') how = 'Two like terms are on the same side. Combine them first.';
    else if (m.x) how = `x is on both sides. ${A2.text(m)} so x is left on one side only. Adding or subtracting never flips the sign.`;
    else if (m.op === '+' || m.op === '-') how = `Undo the number added to x first: ${cardText(m).toLowerCase()}. Adding or subtracting the same number on both sides keeps the sign as it is.`;
    else if (negScale(m)) how = `x has a negative number in front of it. ${scaleText(m)} and flip the sign: dividing or multiplying by a negative reverses the order of numbers (2 &lt; 3, but ${MINUS}2 &gt; ${MINUS}3), so ${e.rel} becomes ${FLIP[e.rel]}.`;
    else how = `x is alone apart from the number in front of it. ${cardText(m)} turns it into 1. It's a positive number, so the sign stays ${e.rel}.`;
    out.push(P(`<b>What works here:</b> ${how}`));
    return out.join('');
  }
  if (typeof registerWhy === 'function') registerWhy(explain3);

  // ---------------------------------------------------------------- rendering and the number line
  let line = null;
  function lineEl() {
    if (line && line.isConnected) return line;
    line = document.createElement('div'); line.id = 'numline';
    $('equation').insertAdjacentElement('afterend', line);
    return line;
  }
  function clearLine() { const l = $('numline'); if (l) { l.innerHTML = ''; l.dataset.key = ''; l.classList.remove('show'); } }
  // Act 2 sizes the equation once before an animation by laying out the result and then the current
  // equation again (its own render, which writes "="), so the sign is put back afterwards.
  function prefit(s, ns) {
    A2.prefit(s, ns);
    const q = $('equation').querySelector('.tok.eq');
    if (q) { q.textContent = s.rel; q.classList.add('rel'); }
  }
  function render(e) {
    A2.render(e);
    const q = $('equation').querySelector('.tok.eq');
    if (q) { q.textContent = e.rel; q.classList.add('rel'); }
    const sol = solution(e);
    if (sol) drawLine(segmentsOf(sol), false); else clearLine();
  }

  // Draws a set of intervals on a number line. segs: [{ lo, hi, loC, hiC, loF, hiF }] where lo/hi are
  // numbers or ±Infinity, loC/hiC say whether the end is included (filled dot) or not (open dot), and
  // loF/hiF are the ends as fractions, for labels. animate: the dots pop in and the shading grows.
  function drawLine(segs, animate) {
    const el = lineEl(), key = JSON.stringify(segs);
    if (!animate && el.dataset.key === key) return;
    el.dataset.key = key;
    const ends = segs.flatMap(s => [s.lo, s.hi]).filter(Number.isFinite);
    const mid = ends.length ? (Math.min(...ends) + Math.max(...ends)) / 2 : 0;
    const spread = ends.length ? Math.max(...ends) - Math.min(...ends) : 0;
    const half = Math.max(6, Math.ceil(spread / 2) + 3);
    const a = Math.round(mid) - half, b = Math.round(mid) + half;
    const W = 360, H = 62, pad = 18, y = 30;
    const px = v => pad + ((Math.max(a - 0.6, Math.min(b + 0.6, v)) - a) / (b - a)) * (W - 2 * pad);
    const step = b - a > 16 ? 2 : 1, endVals = ends.map(v => Math.round(v * 1000));
    let svg = `<svg viewBox="0 0 ${W} ${H}" class="${animate ? 'anim' : ''}" role="img" aria-label="Number line">`;
    svg += `<defs><marker id="nlA" viewBox="0 0 10 10" refX="5" refY="5" markerUnits="userSpaceOnUse" markerWidth="12" markerHeight="12" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="currentColor"/></marker>
      <marker id="nlS" viewBox="0 0 10 10" refX="4" refY="5" markerUnits="userSpaceOnUse" markerWidth="16" markerHeight="16" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="nlShadeHead"/></marker></defs>`;
    svg += `<line class="nlAxis" x1="4" y1="${y}" x2="${W - 4}" y2="${y}" marker-start="url(#nlA)" marker-end="url(#nlA)"/>`;
    for (let v = a; v <= b; v++) {
      const x = px(v), labelled = v % step === 0 && !endVals.includes(v * 1000);
      svg += `<line class="nlTick" x1="${x}" y1="${y - 5}" x2="${x}" y2="${y + 5}"/>`;
      if (labelled) svg += `<text class="nlNum" x="${x}" y="${y + 20}">${numText(v)}</text>`;
    }
    segs.forEach((s, i) => {
      const x1 = Number.isFinite(s.lo) ? px(s.lo) : 6, x2 = Number.isFinite(s.hi) ? px(s.hi) : W - 6;
      const len = Math.abs(x2 - x1);
      const mStart = Number.isFinite(s.lo) ? '' : ' marker-start="url(#nlS)"', mEnd = Number.isFinite(s.hi) ? '' : ' marker-end="url(#nlS)"';
      // The shading grows out from the dot (from the left end if both ends are dots).
      const fromRight = !Number.isFinite(s.lo) && Number.isFinite(s.hi);
      svg += `<line class="nlShade" x1="${fromRight ? x2 : x1}" y1="${y}" x2="${fromRight ? x1 : x2}" y2="${y}"${fromRight ? mEnd.replace('end', 'start') + mStart.replace('start', 'end') : mStart + mEnd}
        style="stroke-dasharray:${len + 20}; --len:${len + 20}; animation-delay:${0.35 + i * 0.25}s"/>`;
      for (const [v, c, f] of [[s.lo, s.loC, s.loF], [s.hi, s.hiC, s.hiF]]) {
        if (!Number.isFinite(v)) continue;
        svg += `<circle class="nlDot ${c ? 'closed' : 'open'}" cx="${px(v)}" cy="${y}" r="6.5" style="transform-origin:${px(v)}px ${y}px"/>`;
        svg += `<text class="nlEnd" x="${px(v)}" y="${y - 12}">${f ? fracText(f) : numText(v)}</text>`;
      }
    });
    el.innerHTML = svg + '</svg>';
    el.classList.add('show');
  }
  // The answer in words, for the caption while the number line draws.
  function lineCaption(sol) {
    const v = fracText(sol.v), closed = sol.rel === '≤' || sol.rel === '≥';
    return closed ? `Every number ${sol.rel} ${v} works, ${v} too (filled dot)` : `Every number ${sol.rel} ${v} works, but not ${v} (open dot)`;
  }

  // ---------------------------------------------------------------- animations
  // Positive × and ÷, + and −, Distribute and Combine use Act 2's animations unchanged (the sign stays put).
  // A negative × or ÷ runs Act 2's scale animation, then the sign spins around and turns over:
  //   −3x ≥ 12  ->  ÷(−3) under both sides  ->  x ... −4  ->  ≥ spins and lands as ≤
  // When the move solves it, the answer is then shaded on the number line.
  async function spinRel(card, s, ns) {
    const q = $('equation').querySelector('.tok.eq'); if (!q) return;
    caption(`${card.op === '/' ? 'Dividing' : 'Multiplying'} by a negative flips the sign: ${s.rel} becomes ${ns.rel}`);
    q.classList.add('rel', 'relflip');
    await quick(260);                      // halfway through the turn, the sign shows its new direction
    q.textContent = ns.rel;
    await quick(300);
    q.classList.remove('relflip'); q.classList.add('relnew');
    await hold();
  }
  async function showAnswerLine(ns) {
    const sol = solution(ns); if (!sol) return;
    caption(lineCaption(sol));
    drawLine(segmentsOf(sol), true);
    await quick(1100);
    await hold();
  }
  function animFor(card) {
    const base = A2.animFor(card);
    return async (c, s, ns, ref) => {
      await base(c, s, ns, ref);
      if (negScale(c)) await spinRel(c, s, ns);
      if (isSolved(ns)) await showAnswerLine(ns);
    };
  }

  // ---------------------------------------------------------------- generators
  // Every generator returns { ineq, enemy } with a whole-number boundary. Shapes (Easy):
  //   add/sub   x + a < b, x − a ≥ b              mul/div  ax > b, x/a ≤ b
  //   two/twom  ax + b ≤ c, ax − b > c
  //   negx      −x < a           (× −1, flip)      negmul   −ax ≥ b       (÷ −a, flip)
  //   negtwo    b − ax > c       (− b, ÷ −a, flip) negtwo2  −ax + b ≤ c
  //   negdiv    x/(−a) < b       (× −a, flip)
  // About half of normal fights need a flip, since that's the new idea. The variety system writes about
  // half of them the other way round (9 > 2x + 1).
  const FLIPS = ['negx', 'negmul', 'negtwo', 'negtwo2', 'negdiv'], KEEPS = ['add', 'sub', 'mul', 'div', 'two', 'twom'];
  function genIneq(type) {
    const tut = !!type;
    for (;;) {
      const t = type || (Math.random() < 0.55 ? pick(FLIPS) : pick(KEEPS));
      const x = tut ? rand(1, 8) : nonZero(-8, 9), a = rand(2, 6), b = rand(1, 12), rel = pick(RELS);
      const enemy = FLIPS.includes(t) ? 'flipjack' : 'tilter';
      let e;
      if (t === 'add') e = I([X(1), N(b)], [N(x + b)], rel);
      else if (t === 'sub') e = I([X(1), N(-b)], [N(x - b)], rel);
      else if (t === 'mul') e = I([X(a)], [N(a * x)], rel);
      else if (t === 'div') e = I([X(F(1, a))], [N(rand(1, 9) * (x > 0 ? 1 : -1))], rel);
      else if (t === 'two') e = I([X(a), N(b)], [N(a * x + b)], rel);
      else if (t === 'twom') e = I([X(a), N(-b)], [N(a * x - b)], rel);
      else if (t === 'negx') e = I([X(-1)], [N(-x)], rel);
      else if (t === 'negmul') e = I([X(-a)], [N(-a * x)], rel);
      else if (t === 'negtwo') e = I([N(b), X(-a)], [N(b - a * x)], rel);
      else if (t === 'negtwo2') e = I([X(-a), N(b)], [N(-a * x + b)], rel);
      else e = I([X(F(-1, a))], [N(rand(1, 9) * pick([1, -1]))], rel);
      if ([...e.L, ...e.R].length < 2) continue;
      return { ineq: e, enemy };
    }
  }

  // Elites stack inequalities with an Act 2 move, and usually still need a flip at the end:
  //   −2(x − 3) < 10    3x − 5x + 4 ≥ 10    2x + 5 > 5x − 4 (written so the x-term left over is negative)
  function genStacked3() {
    for (;;) {
      const t = pick(['distneg', 'distneg', 'dist', 'like', 'xboth']);
      const x = nonZero(-6, 8), rel = pick(RELS);
      let e;
      if (t === 'distneg') { const m = -rand(2, 4), b = nonZero(-6, 6); e = I([G(m, [X(1), N(b)])], [N(m * (x + b))], rel); }
      else if (t === 'dist') { const m = rand(2, 4), b = nonZero(-6, 6), c = nonZero(-8, 8); e = I([G(m, [X(1), N(b)]), N(c)], [N(m * (x + b) + c)], rel); }
      else if (t === 'like') { const p = rand(1, 4), q = -rand(p + 1, p + 5), c = nonZero(-9, 9); e = I([X(p), X(q), N(c)], [N((p + q) * x + c)], rel); }
      else { const p = rand(1, 5), q = rand(1, 5), c = nonZero(-9, 9); if (p === q) continue; const d = p * x + c - q * x; e = I([X(p), N(c)], d ? [X(q), N(d)] : [X(q)], rel); }
      return { ineq: e, enemy: 'boundwarden' };
    }
  }

  // Act 3 elite and boss fights. list = the unlocked skills this run can use, oldest first.
  function buildFight3(node, list) {
    const act3 = list.filter(id => (SKILL[id].act || 1) === 3);
    if (node.type === 'elite') return { phases: [genStacked3], handSize: difficulty.hand, enemy: 'boundwarden' };
    // Boss: an inequality that keeps its sign, one that flips (written the other way round), then a stacked one.
    const phases = [() => genIneq(pick(KEEPS)), () => genIneq(pick(FLIPS))];
    for (const id of act3.slice(1)) phases.push(SKILL[id].gen);
    phases.push(genStacked3);
    return { phases, handSize: difficulty.hand, enemy: 'leaningtower' };
  }

  // The shared variety system (index.html freshEquation): writes an inequality and mirrors it (sides swap,
  // the sign turns around so it means the same thing).
  if (typeof ENGINES === 'object') ENGINES.ineq = { text: e => eqText(e), mirror: swapI };

  // Difficulty: Act 2's rules (bigger numbers, negatives, extra steps, fraction answers on Expert) fit
  // inequalities as they are. They only scale plain numbers, so a negative x-coefficient (the flip) stays.
  function applyDifficulty3(g, regen) {
    const asEq = r => { const { ineq, ...rest } = r; return { ...rest, eq: ineq }; };
    const { eq, ...rest } = A2.applyDifficulty(asEq(g), () => asEq(regen()));
    return { ...rest, ineq: eq.rel ? eq : { ...eq, rel: g.ineq.rel } };
  }

  // ---------------------------------------------------------------- skills, enemies, act
  SKILLS.push(
    { id: 'ineq', stage: 10, act: 3, name: 'Inequalities', gen: () => genIneq(),
      title: 'Stage 10: Inequalities',
      intro: 'An inequality uses &lt;, &gt;, ≤ or ≥ instead of =, and its answer is a whole range of numbers. Solve it the same way as an equation, with one new rule: multiplying or dividing both sides by a <b>negative</b> number flips the sign. Those cards say "flip sign". The answer is then shaded on a number line.',
      example: '2x + 1 &lt; 9<br>Subtract 1 from both sides → 2x &lt; 8<br>Divide both sides by 2 → x &lt; 4<br><br>−3x ≥ 12<br>Divide both sides by −3 and flip the sign → x ≤ −4',
      tutorial: [() => genIneq('two'), () => genIneq('negmul')] },
  );
  for (const s of SKILLS) SKILL[s.id] = s;
  progress = loadProgress();     // the save was first read before this skill existed

  Object.assign(ENEMIES, {
    tilter:       { name: 'Tilter',         rank: 'Normal', color: '#90be6d', size: 84 },
    flipjack:     { name: 'Flip-Jack',      rank: 'Normal', color: '#f9844a', size: 84 },
    boundwarden:  { name: 'Bound Warden',   rank: 'Elite',  color: '#577590', size: 100, horns: true },
    leaningtower: { name: 'The Leaning Tower', rank: 'Boss', color: '#f94144', size: 120, crown: true },
  });
  ACTS[3] = { name: 'The Leaning Stacks', sub: 'Inequalities', boss: 'The Leaning Tower', firstSkill: 'ineq',
    blurb: 'The shelves here lean one way or the other, and so do the equations: their answers are whole ranges of numbers. Watch out for negatives, which flip the sign. Defeat The Leaning Tower.' };

  const css = document.createElement('style');
  css.textContent = `
    .tok.eq.rel { color:var(--ink); transition: transform .26s ease-in, color .2s; }
    .tok.eq.relflip { transform: rotateY(90deg) scale(1.25); color:#7bdff2; }
    .tok.eq.relnew { color:var(--accent); transform: scale(1.15); }
    .card .ftag { display:block; font-size:max(10px, .45em); letter-spacing:1px; color:#b00045; text-transform:uppercase; margin-top:2px; white-space:nowrap; }
    .card .ftag.keep { color:#4a4470; }
    #numline { display:none; width:min(360px, 92%); color:var(--muted); line-height:0; }
    #numline.show { display:block; }
    #numline svg { width:100%; height:auto; overflow:visible; }
    #numline .nlAxis { stroke:currentColor; stroke-width:2.5; }
    #numline .nlTick { stroke:currentColor; stroke-width:2; }
    #numline .nlNum { fill:currentColor; font: bold 11px "Courier New", monospace; text-anchor:middle; }
    #numline .nlEnd { fill:var(--accent); font: bold 14px "Courier New", monospace; text-anchor:middle; }
    #numline .nlShade { stroke:var(--good); stroke-width:7; stroke-linecap:round; opacity:.9; }
    #numline .nlShadeHead { fill:var(--good); }
    #numline .nlDot { stroke:var(--good); stroke-width:3; }
    #numline .nlDot.closed { fill:var(--good); }
    #numline .nlDot.open { fill:var(--panel); }
    #numline svg.anim .nlShade { stroke-dashoffset:var(--len); animation: nlGrow .7s ease-out forwards; }
    #numline svg.anim .nlDot, #numline svg.anim .nlEnd { animation: nlPop .35s cubic-bezier(.2,1.6,.4,1) both; }
    @keyframes nlGrow { to { stroke-dashoffset:0; } }
    @keyframes nlPop { from { transform: scale(0); opacity:0; } }
    @media (max-width: 640px) {
      #numline { width:min(330px, 96%); }
      .card .ftag { margin-top:0; font-size:9px; }
      /* a flip tag is one more line on the card, so phone hands with one get a little taller */
      #hand.many:has(.ftag) .card { height:clamp(92px, 14.5vh, 120px); }
      #hand:not(.many):has(.ftag) .card { height:clamp(122px, 21vh, 156px); }
    }
    @media (orientation: landscape) and (max-height: 520px) { #numline { width:min(300px, 80%); } }
  `;
  document.head.appendChild(css);

  window.ACT3 = { apply, isSolved, solution, segmentsOf, drawLine, clearLine, makeEquation: makeEquation3, refreshPath, render, prefit,
    eqText, makeHand: makeHand3, isCorrect, whyWrong, animFor, applyDifficulty: applyDifficulty3, label, text, kind,
    buildFight: buildFight3, genStacked: genStacked3, gens: { ineq: genIneq } };
})();
