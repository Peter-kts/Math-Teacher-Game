// =====================================================================
//  Act 3: The Leaning Stacks (Inequalities and absolute value)
// =====================================================================
// Stage 10  Inequalities              2x + 1 < 9, −3x ≥ 12
// Stage 11  Compound inequalities     −3 < 2x + 1 ≤ 7, 2x + 1 < −3 or 3x − 2 > 7
// Stage 12  Absolute value equations  |x − 3| = 5
// Stage 13  Absolute value inequalities  |2x − 1| < 7, |x + 2| ≥ 4
//
// Four kinds of state (kindOf):
//   single  Act 2's equation model plus a relation: { L, R, result: null, rel: '<'|'≤'|'>'|'≥'|'=', owe }
//           Act 2's engine does the algebra (apply, the expected path, hands, animations); this file adds the sign.
//   chain   a three-part compound: { chain: true, lo, rel1, coef, b, constFirst, rel2, hi, owe }
//   abs     before the split: { abs: true, m, a, b, c, rel, d, result }  meaning  m|ax + b| + c  rel  d
//           Once the bars are alone: Split (=), Between (< ≤) or Outside (> ≥) if d > 0; if d < 0, the
//           verdict No solution (= < ≤) or All x (> ≥), which sets result.
//   board   two cases joined by "or": { board: true, join: 'or', branches: [single, single], active }
//
// The flip is its own move. Multiplying or dividing by a negative leaves the sign as it was and marks
// the state `owe`; the player then has to drop the ◎ "Flip sign" card on the sign. Every inequality hand
// has that card. Playing it when nothing needs flipping is a wrong move, and so is any other card while a
// flip is owed.
//
// index.html picks this engine for generators that return { ineq } (cur.act3). ENGINES.ineq plugs it into
// the shared variety system. The number line (drawLine) draws any set of intervals or points.
'use strict';
(function () {
  const A2 = window.ACT2;
  if (!A2) return;
  const N = k => ({ t: 'n', k: typeof k === 'number' ? F(k) : k });
  const X = k => ({ t: 'x', k: typeof k === 'number' ? F(k) : k });
  const G = (m, items) => ({ t: 'g', m: typeof m === 'number' ? F(m) : m, items });
  const noZero = side => side.filter(i => !(i.t === 'n' && i.k.n === 0));
  const FLIP = { '<': '>', '>': '<', '≤': '≥', '≥': '≤', '=': '=' };
  const RELS = ['<', '≤', '>', '≥'];
  const I = (L, R, rel) => ({ L: noZero(L), R: noZero(R), result: null, rel: rel || pick(RELS) });
  const swapI = e => ({ ...e, L: e.R, R: e.L, rel: FLIP[e.rel] });         // 9 > 2x + 1 is the same as 2x + 1 < 9
  const constOf = side => { const c = side.find(i => i.t === 'n'); return c ? c.k : F(0); };
  const isDeclare = c => c.op === 'none' || c.op === 'all';
  const isPart = c => c.scope === 'part';
  const isFlip = c => c.op === 'flip';
  const SCALE_OPS = ['*', '/', 'neg', 'frac'];
  // Does this card multiply or divide both sides by a negative number? Then the sign has to flip next.
  const negScale = c => SCALE_OPS.includes(c.op) && !c.lcd && cardFactor(c).n < 0;
  const clone = o => JSON.parse(JSON.stringify(o));
  const kickClass = (el, cls) => { if (!el) return; el.classList.remove(cls); void el.offsetWidth; el.classList.add(cls); };
  const roleOf = t => (t && t.dataset ? t.dataset.role : t);
  const onSign = t => ['eq', 'rel1', 'rel2', 'rel'].includes(roleOf(t));
  const isTutorial = () => typeof fight !== 'undefined' && fight && fight.node && fight.node.type === 'tutorial';
  const kindOf = e => (e.board ? 'board' : e.abs ? 'abs' : e.chain ? 'chain' : 'single');
  const FLIP_CARD = { op: 'flip', scope: 'part', ref: 'rel' };
  const showHint = () => typeof difficulty !== 'undefined' && difficulty.highlight === 'on';
  const fLess = (a, b) => a.n * b.d < b.n * a.d;
  // Split comes in three: two cases for |u| = d, "between" (one chain) for |u| < d, "outside" (two cases)
  // for |u| > d. For inequalities both Between and Outside are in the hand, and choosing is the skill.
  const gtRel = rel => rel === '>' || rel === '≥';
  const wayFor = rel => (rel === '=' ? 'two' : gtRel(rel) ? 'outside' : 'between');
  const SPLIT = (way, d) => ({ op: 'split', scope: 'part', ref: 'abs', way, d });

  // Cases. Every difficulty covers every case of a stage (the difficulty only changes how hard each one
  // is to solve). Normal fights go through them with index.html's shared cycle (SKILL.cases + cycled():
  // the generator gets the case, and a stage isn't mastered until each case is solved once).
  // applyDifficulty3 checks that a question is still its case after the difficulty changes.
  const CASES = {
    ineq: ['keep-pos', 'keep-neg', 'keep-frac', 'flip-pos', 'flip-neg', 'flip-frac'],
    compound: ['keep-pos', 'keep-neg', 'keep-frac', 'flip-pos', 'flip-neg', 'flip-frac', 'or'],
    absval: ['two-int', 'two-frac', 'none'],
    absineq: ['between-int', 'between-frac', 'outside-int', 'outside-frac', 'none', 'all'],
  };
  // Elites and boss phases pick a case at random (they don't take one from the cycle).
  const anyCase = (skill, only = () => true) => pick(CASES[skill].filter(only));
  // pos / neg / frac for a set of answer numbers: frac if any is a fraction, neg if any is negative.
  const ansKind = vs => (vs.some(v => !isInt(v)) ? 'frac' : vs.some(v => v.n < 0) ? 'neg' : 'pos');

  // Path skills: plain steps (+ − × ÷ and Flip) practise the fight's own stage, so its mastery goes there.
  // Act 2 moves (Distribute, Combine, x on both sides) keep their own skill.
  const PLAIN = ['onestep', 'twostep', 'negfrac'];
  function retag(path, main) { for (const p of path) if (PLAIN.includes(p.skill)) p.skill = main; }

  // ================================================================ single inequalities (stage 10)
  function sApply(e, c, ref) {
    if (isFlip(c)) return { ...e, rel: FLIP[e.rel], owe: false };
    const a = A2.apply(e, c, ref);
    a.rel = e.rel; a.owe = negScale(c) && e.rel !== '=';
    return a;
  }
  const sSolved = e => !e.owe && A2.isSolved(e);
  // The answer, written with x first: "3 < x" reads as x > 3.
  function solution(e) {
    if (!e || kindOf(e) !== 'single' || !sSolved(e)) return null;
    const xLeft = e.L.length === 1 && e.L[0].t === 'x';
    return { v: constOf(xLeft ? e.R : e.L), rel: xLeft ? e.rel : FLIP[e.rel] };
  }
  // The answer as intervals for the number line. lo/hi can be ±Infinity; x = v is a single point.
  function segmentsOf(sol) {
    const v = sol.v.n / sol.v.d, closed = sol.rel === '≤' || sol.rel === '≥';
    if (sol.rel === '=') return [{ lo: v, hi: v, loC: true, hiC: true, loF: sol.v, hiF: sol.v }];
    return sol.rel === '<' || sol.rel === '≤'
      ? [{ lo: -Infinity, hi: v, hiC: closed, hiF: sol.v }]
      : [{ lo: v, hi: Infinity, loC: closed, loF: sol.v }];
  }
  // Act 2's path, with a Flip step after every × or ÷ by a negative.
  function sPath(e, main) {
    if (sSolved(e)) return [];
    if (e.owe) return [{ state: e, move: FLIP_CARD, skill: main }, ...sPath(sApply(e, FLIP_CARD), main)];
    const p = A2.makeEquation(e).path;
    retag(p, main);
    return p.flatMap(s => (negScale(s.move) && e.rel !== '=' ? [s, { state: s.state, move: FLIP_CARD, skill: main }] : [s]));
  }
  function sCorrect(e, c, target) {
    if (e.owe) return isFlip(c) && onSign(target);
    if (isFlip(c) || c.op === 'trap' || isDeclare(c)) return false;
    return A2.isCorrect({ state: e }, c, target);
  }
  const eqText = e => A2.eqText(e).replace(' = ', ` ${e.rel} `);
  const eqH = e => `<span class="whyEq"><span>${A2.sideStr(e.L, true)}</span><span>${e.rel}</span><span>${A2.sideStr(e.R, true)}</span></span>`;

  // ---------------------------------------------------------------- cards
  function scaleBase(c) {
    if (c.op === 'neg') return TIMES + '(' + MINUS + '1)';
    if (c.op === 'frac') return TIMES + paren(F(c.n, c.d));
    return (c.op === '/' ? DIV : TIMES) + paren(F(c.n));
  }
  const byText = c => (c.op === 'neg' ? MINUS + '1' : c.op === 'frac' ? fracText(F(c.n, c.d)) : numText(c.n));
  const scaleText = c => (c.parts3 ? `${c.op === '/' ? 'Divide' : 'Multiply'} all three parts by ${byText(c)}`
    : `${c.op === '/' ? 'Divide both sides by' : 'Multiply both sides by'} ${byText(c)}`);
  function label(c) {
    if (isFlip(c)) return '<span class="clong">Flip ⇅</span>';
    if (c.op === 'split') return `<span class="clong">${c.way === 'between' ? 'Between' : c.way === 'outside' ? 'Outside' : 'Split | |'}</span>`;
    if (c.op === 'trap' && c.trap === 'flip negative') return `${scaleBase({ ...c, op: c.scaleOp })}<span class="ftag">and flip</span>`;
    if (c.op === 'trap' && c.trap === 'drop bars') return '<span class="clong">Drop | |</span>';
    return null;
  }
  // Stage 11: every ⇔ card on a chain says it hits all three parts.
  function text(c) {
    if (isFlip(c)) return c.parts3 ? 'Flip both signs' : 'Flip the inequality sign';
    if (c.op === 'split') {
      const d = c.d ? fracText(c.d) : 'd', nd = c.d ? fracText(fMul(c.d, F(-1))) : `${MINUS}d`;
      if (c.way === 'between') return `Split: between ${nd} and ${d} (one chain)`;
      if (c.way === 'outside') return `Split: below ${nd} or above ${d} (two cases)`;
      return 'Split into two cases';
    }
    if (c.op === 'trap') return c.text || null;
    if (c.parts3 && (c.op === '+' || c.op === '-')) return c.op === '+' ? `Add ${c.n} to all three parts` : `Subtract ${c.n} from all three parts`;
    if (c.parts3) return scaleText(c);
    return null;
  }
  function kind(c) {
    if (isFlip(c)) return 'Flip sign';
    if (c.op === 'split') return 'Split';
    return null;
  }

  // ---------------------------------------------------------------- hands
  // Wrong cards for when a flip is owed: anything but Flip is wrong then, so any legal-looking card will do.
  function decoys(nums, n, have) {
    const out = [], seen = new Set(have.map(cardLabel));
    const pool = [...shuffle([...nums].flatMap(k => [{ op: '+', n: k }, { op: '-', n: k }, { op: '*', n: k }, { op: '/', n: k }])), ...shuffle([2, 3, 4, 5, 6, 7]).flatMap(k => [{ op: '+', n: k }, { op: '-', n: k }])];
    for (const c of pool) { if (out.length >= n) break; if (c.n < 2 && (c.op === '*' || c.op === '/')) continue; const k = cardLabel(c); if (seen.has(k)) continue; seen.add(k); out.push(c); }
    return out;
  }
  const numsOf = e => new Set([...e.L, ...e.R].flatMap(it => (it.t === 'g' ? [it.m, ...it.items.map(t => t.k)] : [it.k])).filter(f => isInt(f) && f.n).map(f => Math.abs(f.n)));
  // The classic mix-up of flipping because a negative number shows up, when the division is by a positive.
  // It's a rule decoy: in the hand at every difficulty (outside tutorials) whenever the answer is negative.
  function flipNegTrap(correct, before, after, parts3) {
    const by = byText(correct);
    return { op: 'trap', trap: 'flip negative', scaleOp: correct.op, n: correct.n, d: correct.d, parts3,
      text: `${correct.op === '/' ? 'Divide' : 'Multiply'} by ${by} and flip (a number is negative)`,
      why: `<p>Only multiplying or dividing by a <b>negative</b> number flips the sign. Here you ${correct.op === '*' ? 'multiply' : 'divide'} by ${by}, which is positive, so the sign stays: ${before} becomes ${after}. A negative number on the other side doesn't matter: x &lt; ${MINUS}4 is a perfectly good answer.</p>` };
  }
  // plain: a case on a board (one x-term, one number each side), where Act 2's Combine, Distribute and
  // x-term decoys make no sense; number cards fill in instead.
  function sHand(e, correct, size, plain) {
    const tut = isTutorial();
    const keep = c => !isDeclare(c) && c.op !== 'trap' && !(plain && (c.op === 'comb' || c.op === 'dist' || c.x));
    if (e.owe) return shuffle([FLIP_CARD, ...decoys(numsOf(e), size - 1, [FLIP_CARD])]);
    let hand = A2.makeHand(e, correct, e.rel === '=' ? size : size - 1).filter(keep);
    if (e.rel !== '=') hand.push(FLIP_CARD);
    if (!tut && e.rel !== '=' && SCALE_OPS.includes(correct.op) && !negScale(correct) && !correct.lcd) {
      const after = sApply(e, correct), sol = solution(after);
      if (sol && sol.v.n < 0) hand.push(flipNegTrap(correct, eqText(e), eqText(after), false));
    }
    const labels = new Set(hand.map(cardLabel));
    for (const c of decoys(numsOf(e), size, hand)) { if (hand.length >= size) break; if (labels.has(cardLabel(c)) || sCorrect(e, c)) continue; labels.add(cardLabel(c)); hand.push(c); }
    while (hand.length > size) { const i = hand.findIndex(c => c !== correct && c !== FLIP_CARD && c.op !== 'trap'); if (i < 0) break; hand.splice(i, 1); }
    return shuffle(hand);
  }

  // ---------------------------------------------------------------- wrong moves
  function sWhyWrong(e, card, want, target) {
    if (isFlip(card)) {
      if (e.owe) return 'Right card: drop Flip on the sign.';
      return `Nothing has flipped the order yet. Only multiplying or dividing by a negative number does that.`;
    }
    if (e.owe) return `You ${'multiplied or divided'} by a negative, so the sign has to flip first. Play Flip on the sign.`;
    if (card.op === 'trap') return `That's a trap: ${card.scaleOp === '*' ? 'multiplying' : 'dividing'} by a positive number never flips the sign. Tap Why? to see why.`;
    if (isDeclare(card)) return 'x is still here, so keep solving.';
    if (card.op === 'dist' || card.op === 'comb') return A2.whyWrong({ state: e, path: [{ move: want }], step: 0 }, card, target);
    const ref = target && target.dataset ? target.dataset.ref : target;
    const after = eqText(sApply(e, card, ref));
    if (want.op === 'dist') return `That's allowed, but clear the parentheses first. It would give ${after}`;
    if (want.op === 'comb') return `That's allowed, but combine the like terms first. It would give ${after}`;
    if (want.x) return `That's allowed, but get the x-terms onto one side first. It would give ${after}`;
    const xs = e.L.some(i => i.t === 'x') ? e.L : e.R;
    if (xs.some(i => i.t === 'n') && SCALE_OPS.includes(card.op)) return `That's allowed, but undo the + or ${MINUS} part first, then the ${TIMES} or ${DIV}.`;
    return `That's allowed, but x still isn't alone: ${after}`;
  }
  const FLIP_IDEA = `multiplying or dividing by a negative number turns the order of numbers around (2 &lt; 3, but ${MINUS}2 &gt; ${MINUS}3), so the sign has to turn around too`;
  function explainSingle(e, card, correct, ref) {
    const P = t => `<p>${t}</p>`, out = [];
    if (isFlip(card)) {
      if (e.owe) return P('Flip was the right card. It goes on the sign itself, so drop it right on the &lt; or &gt;.');
      out.push(P(`The sign only flips right after multiplying or dividing by a <b>negative</b> number: ${FLIP_IDEA}. Nothing like that has happened since the last flip, so ${eqH(e)} keeps its sign.`));
    } else if (e.owe) {
      out.push(P(`The last move ${'multiplied or divided'} by a negative number, and ${FLIP_IDEA}. Right now ${eqH(e)} has the old sign, so it isn't true yet. Flip comes first, before anything else.`));
      out.push(P('<b>What works here:</b> drop Flip on the sign.'));
      return out.join('');
    } else if (card.op === 'comb') out.push(P('Like terms have the same letter part: x-terms combine with x-terms, and plain numbers with plain numbers. Combine needs two of the same kind on the same side, outside any parentheses.'));
    else if (card.op === 'dist') out.push(P('Distribute multiplies the number in front of a pair of parentheses into every term inside, so it has to be dropped on the parentheses.'));
    else if (isDeclare(card)) out.push(P('x is still in the inequality, so there is nothing to declare yet. Keep solving.'));
    else out.push(P(`${cardText(card)} is allowed, but it turns it into ${eqH(sApply(e, card, ref))}, which is no closer to x alone.`));
    const m = correct;
    let how;
    if (m.op === 'dist') how = 'Clear the parentheses first: multiply the number in front into each term inside.';
    else if (m.op === 'comb') how = 'Two like terms are on the same side. Combine them first.';
    else if (m.x) how = `x is on both sides. ${A2.text(m)} so x is left on one side only. Adding or subtracting never flips the sign.`;
    else if (m.op === '+' || m.op === '-') how = `Get the x-term alone first: ${cardText(m).toLowerCase()}. Adding or subtracting the same number on both sides keeps the sign as it is.`;
    else if (negScale(m)) how = `x has a negative number in front of it. ${scaleText(m)}, then play Flip on the sign: ${FLIP_IDEA}.`;
    else how = `x is alone apart from the number in front of it. ${cardText(m)} turns it into 1. It's a positive number, so the sign stays ${e.rel}.`;
    out.push(P(`<b>What works here:</b> ${how}`));
    return out.join('');
  }

  // ---------------------------------------------------------------- rendering
  let line = null;
  function lineEl() {
    if (line && line.isConnected) return line;
    line = document.createElement('div'); line.id = 'numline';
    ($('cases') || $('equation')).insertAdjacentElement('afterend', line);
    return line;
  }
  function clearLine() { const l = $('numline'); if (l) { l.innerHTML = ''; l.dataset.key = ''; l.classList.remove('show'); } }
  function markSign(e) {
    const q = $('equation').querySelector('.tok.eq');
    if (!q) return;
    q.textContent = e.rel; q.classList.add('rel');
    q.classList.toggle('owed', !!e.owe && showHint());
  }
  function renderSingle(e, inBoard) {
    A2.render(e);
    markSign(e);
    if (inBoard) return;
    clearCases();
    const sol = solution(e);
    if (sol) drawLine(segmentsOf(sol), false); else clearLine();
  }
  // Act 2 sizes the equation once before an animation by laying out the result and then the current
  // equation again (its own render, which writes "="), so the sign is put back afterwards.
  function prefit(s, ns) {
    const k = kindOf(s);
    if (k === 'single' && kindOf(ns) === 'single') { A2.prefit(s, ns); markSign(s); }
    else if (k === 'board' && kindOf(ns) === 'board' && !boardSolved(ns)) { A2.prefit(boardActive(s), ns.branches[s.active]); markSign(boardActive(s)); }
    else if ((k === 'chain' || k === 'abs') && kindOf(ns) === k) {   // same idea as Act 2: never bigger than the result
      const px = () => parseFloat(getComputedStyle($('equation')).fontSize);
      render(ns); const after = px(); render(s); const before = px();
      if (before > after + .5) $('equation').style.setProperty('--eqSize', Math.floor(parseFloat($('equation').style.getPropertyValue('--eqSize') || getComputedStyle(document.documentElement).getPropertyValue('--eqSize')) * after / before) + 'px');
    }
  }

  // Draws a set of intervals on a number line. segs: [{ lo, hi, loC, hiC, loF, hiF }] where lo/hi are
  // numbers or ±Infinity, loC/hiC say whether the end is included (filled dot) or not (open dot), and
  // loF/hiF are the ends as fractions, for labels. lo === hi is a single point. animate: the dots pop
  // in and the shading grows.
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
    // Review fix: wide chains (spread 36+ on Hard) used to get a label every 2 units and turn into a smear.
    // The label step now keeps it to about 12 labels, and small ticks thin out the same way.
    const step = [1, 2, 5, 10, 20, 50, 100].find(k => (b - a) / k <= 12) || 200, tickStep = b - a > 40 ? step / (step % 5 === 0 ? 5 : 2) : 1, endVals = ends.map(v => Math.round(v * 1000));
    let svg = `<svg viewBox="0 0 ${W} ${H}" class="${animate ? 'anim' : ''}" role="img" aria-label="Number line">`;
    svg += `<defs><marker id="nlA" viewBox="0 0 10 10" refX="5" refY="5" markerUnits="userSpaceOnUse" markerWidth="12" markerHeight="12" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="currentColor"/></marker>
      <marker id="nlS" viewBox="0 0 10 10" refX="4" refY="5" markerUnits="userSpaceOnUse" markerWidth="16" markerHeight="16" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="nlShadeHead"/></marker></defs>`;
    svg += `<line class="nlAxis" x1="4" y1="${y}" x2="${W - 4}" y2="${y}" marker-start="url(#nlA)" marker-end="url(#nlA)"/>`;
    for (let v = a; v <= b; v++) {
      if (v % tickStep !== 0) continue;
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
    if (sol.rel === '=') return `x = ${v}`;
    return closed ? `Every number ${sol.rel} ${v} works, ${v} too (filled dot)` : `Every number ${sol.rel} ${v} works, but not ${v} (open dot)`;
  }

  // ---------------------------------------------------------------- animations (single)
  // + − × ÷, Distribute and Combine play Act 2's animations unchanged. A × or ÷ by a negative leaves the
  // sign as it was (on Easy and Normal it then glows red, as a hint that it is owed a flip).
  // Flip: the sign spins around and lands the other way.  −3x ≥ 12  ->  ÷(−3)  ->  x ≥ −4  ->  Flip  ->  x ≤ −4
  // When a move solves it, the answer is shaded on the number line.
  async function flipAnim(s, ns) {
    const q = $('equation').querySelector('.tok.eq'); if (!q) return;
    caption(`Flip: ${s.rel} becomes ${ns.rel}, because the last move ${'multiplied or divided'} by a negative`);
    q.classList.remove('owed'); q.classList.add('rel', 'relflip');
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
  async function singleAnim(card, s, ns, ref, inBoard) {
    if (isFlip(card)) await flipAnim(s, ns);
    else {
      await A2.animFor(card)(card, s, ns, ref);
      if (ns.owe) { markSign(ns); if (showHint()) { caption(`That was a negative ${card.op === '/' ? 'divide' : 'multiply'}: now the sign has to flip`); await hold(); } }
    }
    if (!inBoard && sSolved(ns)) await showAnswerLine(ns);
  }

  // ================================================================ chains (stage 11)
  // lo < ax + b ≤ hi says x is between two numbers. It is kept smallest number first (both signs < or ≤).
  // The middle is written like an Act 1 x side (coef·x + b, or b + coef·x). Every ⇔ card does the same
  // thing to all three parts. A × or ÷ by a negative leaves the signs alone (so for a moment the chain is
  // false: 3 < x ≤ 1); Flip then turns both signs around and the chain is read from the other end:
  //   1 ≤ 7 − 2x < 5  ->  −7  ->  −6 ≤ −2x < −2  ->  ÷(−2)  ->  3 ≤ x < 1  ->  Flip  ->  1 < x ≤ 3
  // Review fix: CH also takes fractions as they are. The split of |ax + b| < d passed d.n / d.d as a float,
  // so a fraction d on Expert (e.g. 29/3) became a float-based fraction like 2720924774869675/281474976710656.
  const toF = v => (typeof v === 'number' ? F(v) : v);
  const CH = (lo, rel1, coef, b, rel2, hi, constFirst = false) => ({ chain: true, lo: toF(lo), rel1, coef: toF(coef), b: toF(b), rel2, hi: toF(hi), constFirst: constFirst && toF(b).n !== 0 });
  const toS = e => ({ coef: e.coef, b: e.b, c: F(0), xLeft: true, constFirst: e.constFirst });
  const chainSteps = e => (e.owe ? 1 : 0) + (e.b.n !== 0 ? 1 : 0) + (fIs(e.coef, 1) ? 0 : 1);
  function chainApply(e, c) {
    const r = { ...e };
    if (isFlip(c)) return { ...e, lo: e.hi, hi: e.lo, rel1: e.rel2, rel2: e.rel1, owe: false };   // flipped, then read from the other end
    if (c.op === '+' || c.op === '-') {
      const a = F(c.op === '+' ? c.n : -c.n);
      r.b = fAdd(e.b, a); r.lo = fAdd(e.lo, a); r.hi = fAdd(e.hi, a);
    } else if (SCALE_OPS.includes(c.op)) {
      const m = cardFactor(c);
      r.coef = fMul(e.coef, m); r.b = fMul(e.b, m); r.lo = fMul(e.lo, m); r.hi = fMul(e.hi, m);
      if (m.n < 0) r.owe = true;
    }
    if (r.b.n === 0) r.constFirst = false;
    return r;
  }
  // The expected move: Flip if owed, then undo the + or − first, then the × or ÷.
  const chainCanon = e => (e.owe ? FLIP_CARD : e.b.n !== 0 ? (e.b.n > 0 ? { op: '-', n: e.b.n } : { op: '+', n: -e.b.n }) : correctMove({ coef: e.coef, b: F(0) }));
  function chainPath(e0, main) {
    const path = []; let e = e0;
    while (chainSteps(e) && path.length < 6) { const m = chainCanon(e); path.push({ state: e, move: m, skill: main }); e = chainApply(e, m); }
    return path;
  }
  // Right if it gets x closer to alone, the same test as Act 1's hands.
  function chainCorrect(e, c, target) {
    if (e.owe) return isFlip(c) && onSign(target);
    if (isFlip(c) || c.op === 'trap' || isPart(c)) return false;
    const a = chainApply(e, c);
    if (!isInt(a.b)) return false;
    if (chainSteps(a) - (a.owe ? 1 : 0) < chainSteps(e)) return true;
    if (e.b.n !== 0) return false;
    const size = f => Math.abs(f.n) * f.d;
    return size(a.coef) < size(e.coef) || (size(a.coef) === size(e.coef) && e.coef.n < 0 && a.coef.n > 0);
  }
  const midTokens = e => tokensFor(toS(e)).filter(t => t.role !== 'eq' && t.role !== 'other');
  const midText = e => midTokens(e).map(t => t.text).join(' ').replace(/(\d) x/g, '$1x');
  const chainText = e => `${fracText(e.lo)} ${e.rel1} ${midText(e)} ${e.rel2} ${fracText(e.hi)}`;
  const chainH = e => `<span class="whyEq"><span>${fracHtml(e.lo)}</span><span>${e.rel1}</span><span>${midTokens(e).map(t => t.html || t.text).join(' ')}</span><span>${e.rel2}</span><span>${fracHtml(e.hi)}</span></span>`;
  const chainSegs = e => [{ lo: e.lo.n / e.lo.d, hi: e.hi.n / e.hi.d, loC: e.rel1 === '≤', hiC: e.rel2 === '≤', loF: e.lo, hiF: e.hi }];
  function chainCaption(e) {
    const lo = fracText(e.lo), hi = fracText(e.hi), inc = (v, c) => `${v} ${c ? 'counts (filled dot)' : `doesn't (open dot)`}`;
    return `Every number between ${lo} and ${hi} works: ${inc(lo, e.rel1 === '≤')}, ${inc(hi, e.rel2 === '≤')}`;
  }
  // Chains, bars and finished boards are laid out on one line and shrunk to fit, like Act 2 equations.
  const fit = () => { $('equation').classList.add('a2'); if (A2.fitEq) A2.fitEq(); };
  function renderChain(e) {
    const el = $('equation'); if (typeof clearNotes === 'function') clearNotes(); el.innerHTML = '';
    const relTok = (r, role) => { const q = document.createElement('div'); q.className = 'tok eq rel' + (e.owe && showHint() ? ' owed' : ''); q.dataset.role = role; q.textContent = r; return q; };
    el.appendChild(tokEl({ role: 'lo', text: fracText(e.lo), html: fracHtml(e.lo) }));
    el.appendChild(relTok(e.rel1, 'rel1'));
    midTokens(e).forEach(t => el.appendChild(tokEl(t)));
    el.appendChild(relTok(e.rel2, 'rel2'));
    el.appendChild(tokEl({ role: 'hi', text: fracText(e.hi), html: fracHtml(e.hi) }));
    clearCases(); fit();
    if (chainSteps(e) === 0) drawLine(chainSegs(e), false); else clearLine();
  }
  // Hand: Act 1's hand builder fits, since the middle is an Act 1 x side, plus the Flip card. Every
  // card is marked as hitting all three parts.
  function chainHand(e, correct, size) {
    let hand;
    if (e.owe) hand = [FLIP_CARD, ...decoys(new Set([e.lo, e.hi, e.b, e.coef].filter(f => isInt(f) && f.n).map(f => Math.abs(f.n))), size - 1, [FLIP_CARD])];
    else {
      hand = [...makeHand(toS(e), correct, size - 1), FLIP_CARD];
      if (!isTutorial() && SCALE_OPS.includes(correct.op) && !negScale(correct)) {
        const after = chainApply(e, correct);
        if (chainSteps(after) === 0 && after.lo.n < 0) {
          hand.push(flipNegTrap(correct, chainText(e), chainText(after), true));
          const i = hand.findIndex(c => c !== correct && c !== FLIP_CARD && c.op !== 'trap'); if (i >= 0) hand.splice(i, 1);
        }
      }
    }
    return shuffle(hand.map(c => ({ ...c, parts3: true })));
  }
  function chainWhyWrong(e, card) {
    if (isFlip(card)) return e.owe ? 'Right card: drop Flip on one of the signs.' : 'Nothing has flipped the order yet. Only multiplying or dividing by a negative number does that.';
    if (e.owe) return 'You divided or multiplied by a negative, so both signs have to flip first. Play Flip on a sign.';
    if (card.op === 'trap') return `That's a trap: ${card.scaleOp === '*' ? 'multiplying' : 'dividing'} by a positive number never flips the signs. Tap Why? to see why.`;
    if (e.b.n !== 0 && SCALE_OPS.includes(card.op)) return `That's allowed, but undo the + or ${MINUS} part first, then the ${TIMES} or ${DIV}.`;
    return `That's allowed, but x still isn't alone: ${chainText(chainApply(e, card))}`;
  }
  function explainChain(e, card, correct) {
    const P = t => `<p>${t}</p>`, out = [];
    if (isFlip(card)) {
      if (e.owe) return P('Flip was the right card. It goes on the signs, so drop it on the &lt; or ≤.');
      out.push(P(`The signs only flip right after multiplying or dividing by a <b>negative</b> number: ${FLIP_IDEA}. Nothing like that has happened, so ${chainH(e)} keeps its signs.`));
    } else if (e.owe) {
      out.push(P(`The last move ${'multiplied or divided'} by a negative number, and ${FLIP_IDEA}. Look at ${chainH(e)}: the left number is now bigger than the right one, so it can't be true. Both signs flip first, and then it reads from the other end.`));
      out.push(P('<b>What works here:</b> drop Flip on a sign.'));
      return out.join('');
    } else {
      out.push(P(`${cardText({ ...card, parts3: true })} is allowed: whatever you do happens to all three parts. But it turns it into ${chainH(chainApply(e, card))}, which is no closer to x alone.`));
      if (e.b.n !== 0 && SCALE_OPS.includes(card.op)) out.push(P(`x has ${e.b.n > 0 ? '+' : MINUS} ${fracText(fAbs(e.b))} attached, and that was the last thing done to it, so it comes off first.`));
    }
    let how;
    if (correct.op === '+' || correct.op === '-') how = `${cardText({ ...correct, parts3: true })}. The same number comes off all three parts, so the middle stays between the two ends and the signs don't change.`;
    else if (negScale(correct)) how = `${scaleText({ ...correct, parts3: true })}, then play Flip: ${FLIP_IDEA}.`;
    else how = `${scaleText({ ...correct, parts3: true })}. It is a positive number, so both signs stay as they are.`;
    out.push(P(`<b>What works here:</b> ${how}`));
    return out.join('');
  }
  // Animation: the card splits into three and lands under each part (left, middle, right, one after
  // another). The middle cancels; the two ends work out their new numbers in place.
  async function chainAnim(card, s, ns) {
    if (isFlip(card)) return chainFlipAnim(s, ns);
    const lo = roleEl('lo'), hi = roleEl('hi'), m = SCALE_OPS.includes(card.op) ? cardFactor(card) : null;
    caption(cardText({ ...card, parts3: true }));
    const div = card.op === '/', add = !m;
    const midAnchor = add ? [roleEl('const')] : xSideEls();
    const chip = div ? paren(F(card.n)) : chipHtml(card), opt = div ? { bar: true } : {};
    const nLo = note(chip, [lo], opt); kickClass(nLo, 'split'); await quick(110);
    const nMid = note(chip, midAnchor, opt); kickClass(nMid, 'split'); await quick(110);
    const nHi = note(chip, [hi], opt); kickClass(nHi, 'split');
    await hold();
    const target = add ? roleEl('const') : roleEl('coef');
    if (target) { mark([target, nMid], 'cancel'); await quick(250); dropNote(nMid); await removeTok([target]); }
    else dropNote(nMid);
    refreshXSide(toS(ns));
    if (card.op === 'neg') kickClass(roleEl('x'), 'flip');
    mark([nLo, nHi], 'merge'); await quick(200);
    dropNote(nLo); dropNote(nHi);
    lo.innerHTML = fracHtml(ns.lo); hi.innerHTML = fracHtml(ns.hi); kickClass(lo, 'pop'); kickClass(hi, 'pop');
    const how = (a, v) => (add ? `${fracText(a)} ${card.op === '+' ? '+' : MINUS} ${card.n} = ${fracText(v)}` : `${fracText(a)} ${div ? DIV : TIMES} ${paren(div ? F(card.n) : m)} = ${fracText(v)}`);
    caption(`${how(s.lo, ns.lo)},  ${how(s.hi, ns.hi)}`);
    await quick(300); await hold();
    if (ns.owe) {
      ['rel1', 'rel2'].forEach(r => roleEl(r).classList.toggle('owed', showHint()));
      if (showHint()) { caption(`Now ${fracText(ns.lo)} is on the left of ${fracText(ns.hi)}, which can't be right: the signs have to flip`); await hold(); }
    }
    if (chainSteps(ns) === 0) await chainLine(ns);
  }
  // Flip on a chain: both signs spin around, then the two ends (and the signs) trade places so it reads
  // smallest first again.
  async function chainFlipAnim(s, ns) {
    const lo = roleEl('lo'), hi = roleEl('hi'), r1 = roleEl('rel1'), r2 = roleEl('rel2');
    caption('Flip both signs');
    [r1, r2].forEach(r => { r.classList.remove('owed'); r.classList.add('relflip'); });
    await quick(260);
    r1.textContent = FLIP[s.rel1]; r2.textContent = FLIP[s.rel2];
    await quick(300);
    [r1, r2].forEach(r => { r.classList.remove('relflip'); r.classList.add('relnew'); });
    await hold();
    caption('Read it from the other end, so the smaller number comes first');
    const dx = hi.getBoundingClientRect().left - lo.getBoundingClientRect().left;
    const dr = r2.getBoundingClientRect().left - r1.getBoundingClientRect().left;
    [lo, hi, r1, r2].forEach(t => t.classList.add('chainSwap'));
    lo.style.transform = `translateX(${dx}px)`; hi.style.transform = `translateX(${-dx}px)`;
    r1.style.transform = `translateX(${dr}px) scaleX(-1)`; r2.style.transform = `translateX(${-dr}px) scaleX(-1)`;
    await quick(650);
    await hold();
    if (chainSteps(ns) === 0) await chainLine(ns);
  }
  async function chainLine(ns) {
    renderChain(ns);
    caption(chainCaption(ns));
    drawLine(chainSegs(ns), true);
    await quick(1100); await hold();
  }
  // ================================================================ Stages 12 and 13: absolute value
  // Before the split, an absolute value equation or inequality is  m|ax + b| + c  rel  d.  The bars are
  // a block: + and − (undo c) and ÷ (undo m) work on it like on x. Then the ◎ Split card, dropped on the
  // bars, turns it into what it means:
  //   |u| = d   ->  two cases, u = d or u = −d        (a two-branch board)
  //   |u| < d   ->  −d < u < d                        (a stage 11 chain: "and")
  //   |u| > d   ->  two cases, u < −d or u > d        (a two-branch board: "or")
  //   abs   = { abs: true, m: F, a: F, b: F, c: F, rel: '=' | '<' | '≤' | '>' | '≥', d: F }
  //   board = { board: true, join: 'or', branches: [ineq, ineq], active: 0 }   (each branch an Act 3 inequality, rel '=' allowed)
  // On a board, cards act on the active branch (solved top to bottom); the cases show in a panel under
  // the equation, and the answer is drawn on the number line once every case is done.
  const AB = (m, a, b, c, rel, d) => ({ abs: true, m: F(m), a: F(a), b: F(b), c: F(c), rel, d: F(d) });
  const absS = e => ({ coef: e.m, b: e.c, c: e.d, xLeft: true, constFirst: false });     // the bars as "x", for Act 1's hand builder
  const absSteps = e => (e.result ? 0 : (e.c.n !== 0 ? 1 : 0) + (fIs(e.m, 1) ? 0 : 1) + 1);
  const barsAlone = e => e.c.n === 0 && fIs(e.m, 1);
  // A distance from 0 is never negative. With the bars alone and a negative number on the other side,
  // |u| = −5 and |u| < −5 have no solution, and |u| > −5 is true for every number.
  const negVerdict = e => (gtRel(e.rel) ? 'all' : 'none');
  const innerTokens = e => tokensFor(toS({ coef: e.a, b: e.b, constFirst: false })).filter(t => t.role !== 'eq' && t.role !== 'other');
  const innerText = e => innerTokens(e).map(t => t.text).join(' ').replace(/(\d) x/g, '$1x');
  const innerHtml = e => innerTokens(e).map(t => t.html || t.text).join(' ');
  const innerSide = e => noZero([X(e.a), N(e.b)]);
  function absText(e) {
    if (e.result) return e.result === 'none' ? 'No solution' : 'Every number works';
    const m = fIs(e.m, 1) ? '' : fracText(e.m), c = e.c.n === 0 ? '' : ` ${e.c.n < 0 ? MINUS : '+'} ${fracText(fAbs(e.c))}`;
    return `${m}|${innerText(e)}|${c} ${e.rel} ${fracText(e.d)}`;
  }
  const absH = e => `<span class="whyEq">${absText(e).replace(/\|([^|]*)\|/, (_, i) => `|${innerHtml(e)}|`)}</span>`;
  function absApply(e, c) {
    const r = { ...e };
    if (isDeclare(c)) return { ...e, result: c.op };
    if (c.op === 'split') {
      const u = innerSide(e), d = e.d, nd = fMul(d, F(-1));
      // Review fix: with nothing added inside the bars (|x| > 3), both cases are already solved. The board
      // used to stay on case 1, so the fight ended showing only "x < −3" and no number line.
      const skipSolved = bd => { while (bd.active < bd.branches.length && isSolved(bd.branches[bd.active])) bd.active++; return bd; };
      if (e.rel === '=') return skipSolved({ board: true, join: 'or', active: 0, branches: [I(u, [N(d)], '='), I(clone(u), [N(nd)], '=')] });
      if (e.rel === '<' || e.rel === '≤') return CH(nd, e.rel, e.a, e.b, e.rel, d);
      return skipSolved({ board: true, join: 'or', active: 0, branches: [I(u, [N(nd)], FLIP[e.rel]), I(clone(u), [N(d)], e.rel)] });
    }
    if (c.op === '+' || c.op === '-') { const a = F(c.op === '+' ? c.n : -c.n); r.c = fAdd(e.c, a); r.d = fAdd(e.d, a); }
    else if (SCALE_OPS.includes(c.op)) {
      const k = cardFactor(c); r.m = fMul(e.m, k); r.c = fMul(e.c, k); r.d = fMul(e.d, k);
      if (k.n < 0 && e.rel !== '=') r.rel = FLIP[e.rel];
    }
    return r;
  }
  const absCanon = e => (e.c.n !== 0 ? (e.c.n > 0 ? { op: '-', n: e.c.n } : { op: '+', n: -e.c.n })
    : !fIs(e.m, 1) ? correctMove({ coef: e.m, b: F(0) })
    : e.d.n < 0 ? { op: negVerdict(e), scope: 'part' } : SPLIT(wayFor(e.rel), e.d));
  function absCorrect(e, c, target) {
    if (c.op === 'trap' || isFlip(c)) return false;
    if (isDeclare(c)) return barsAlone(e) && e.d.n < 0 && c.op === negVerdict(e);
    if (c.op === 'split') return barsAlone(e) && e.d.n > 0 && (c.way || 'two') === wayFor(e.rel) && roleOf(target) === 'abs';
    if (isPart(c)) return false;
    const a = absApply(e, c);
    if (!isInt(a.c) || !isInt(a.d)) return false;
    if (absSteps(a) < absSteps(e)) return true;
    if (e.c.n !== 0) return false;
    const size = f => Math.abs(f.n) * f.d;
    return size(a.m) < size(e.m) || (size(a.m) === size(e.m) && e.m.n < 0 && a.m.n > 0);
  }

  // Boards
  const boardActive = e => e.branches[e.active];
  const boardSolved = e => e.active >= e.branches.length;
  function boardApply(e, c, ref) {
    const r = clone(e);
    r.branches[r.active] = apply(boardActive(e), c, ref);
    while (r.active < r.branches.length && isSolved(r.branches[r.active])) r.active++;
    return r;
  }
  const boardText = e => e.branches.map(b => eqText(b)).join(` ${e.join} `);
  const boardSegs = e => e.branches.flatMap(b => segmentsOf(solution(b)));
  const boardAnswer = e => e.branches.map(b => { const s = solution(b); return `x ${s.rel} ${fracText(s.v)}`; }).join(` ${e.join} `);

  // The cases panel under the equation: one row per case, the active one highlighted, solved ones with their answer.
  let casesBox = null;
  function casesEl() {
    if (casesBox && casesBox.isConnected) return casesBox;
    casesBox = document.createElement('div'); casesBox.id = 'cases';
    $('equation').insertAdjacentElement('afterend', casesBox);
    return casesBox;
  }
  function clearCases() { const c = $('cases'); if (c) { c.innerHTML = ''; c.classList.remove('show'); } }
  function drawCases(e, fresh) {
    const box = casesEl();
    box.innerHTML = e.branches.map((b, i) => {
      const s = isSolved(b) ? solution(b) : null, on = i === e.active;
      return `${i ? `<span class="cjoin">${e.join}</span>` : ''}<div class="case ${on ? 'on' : ''} ${s ? 'done' : ''} ${fresh ? 'split' : ''}" style="animation-delay:${i * 0.18}s">
        <span class="clabel">Case ${i + 1}</span> ${s ? `x ${s.rel} ${fracText(s.v)} ✓` : eqText(b)}</div>`;
    }).join('');
    box.classList.add('show');
  }
  const verdictSegs = e => (e.result === 'all' ? [{ lo: -Infinity, hi: Infinity }] : []);
  function renderAbs(e) {
    const el = $('equation'); if (typeof clearNotes === 'function') clearNotes(); el.innerHTML = '';
    if (e.result) {     // the verdict, with an empty number line (no solution) or a fully shaded one (every number)
      el.appendChild(tokEl({ role: 'other', text: absText(e), html: absText(e) }));
      clearCases(); fit(); drawLine(verdictSegs(e), false);
      return;
    }
    if (!fIs(e.m, 1)) el.appendChild(tokEl({ role: 'coef', text: fracText(e.m), html: fracHtml(e.m) }));
    const t = tokEl({ role: 'abs', text: `|${innerText(e)}|`, html: `<span class="bar">|</span>${innerHtml(e)}<span class="bar">|</span>` });
    t.classList.add('absTok'); el.appendChild(t);
    if (e.c.n !== 0) el.appendChild(tokEl({ role: 'const', text: `${e.c.n < 0 ? MINUS : '+'} ${fracText(fAbs(e.c))}`, html: `${e.c.n < 0 ? MINUS : '+'} ${fracHtml(fAbs(e.c))}` }));
    const q = document.createElement('div'); q.className = 'tok eq rel'; q.dataset.role = 'eq'; q.textContent = e.rel; el.appendChild(q);
    el.appendChild(tokEl({ role: 'other', text: fracText(e.d), html: fracHtml(e.d) }));
    clearLine(); clearCases(); fit();
  }
  function renderBoard(e) {
    if (boardSolved(e)) {
      const el = $('equation'); if (typeof clearNotes === 'function') clearNotes(); el.innerHTML = '';
      e.branches.forEach((b, i) => {
        if (i) { const j = document.createElement('div'); j.className = 'tok eq'; j.textContent = e.join; el.appendChild(j); }
        const s = solution(b), t = tokEl({ role: 'other', text: `x ${s.rel} ${fracText(s.v)}`, html: `<i class="xv">x</i> ${s.rel} ${fracHtml(s.v)}` });
        el.appendChild(t);
      });
      clearCases(); fit(); drawLine(boardSegs(e), false);
      return;
    }
    renderSingle(boardActive(e), true);
    drawCases(e);
  }

  // Hands
  // The classic mistake with bars: dropping them. It's a rule decoy, in the hand at every difficulty
  // (outside tutorials) once the bars are alone.
  function dropBars(e) {
    const u = innerText(e), dt = fracText(e.d), nd = fracText(fMul(e.d, F(-1)));
    const lost = e.d.n < 0 ? `that would give ${u} ${e.rel} ${dt}, but a distance from 0 can't be negative, so the bars change everything here`
      : e.rel === '=' ? `x would only get one answer. ${dt} and ${nd} are both ${dt} away from 0, so ${u} can be either one: there are two cases`
      : e.rel === '<' || e.rel === '≤' ? `it would lose the left end. Being less than ${dt} away from 0 means ${u} is between ${nd} and ${dt}, not just below ${dt}`
      : `it would lose half the answer. Being more than ${dt} away from 0 means ${u} is above ${dt} <b>or</b> below ${nd}`;
    return { op: 'trap', trap: 'drop bars', text: `Remove the bars: ${u} ${e.rel} ${dt}`,
      why: `<p>The bars mean "distance from 0", so they can't just be removed. Removing them, ${lost}.</p>` };
  }
  function absHand(e, correct, size) {
    const tut = isTutorial(), alone = barsAlone(e);
    const nums = new Set([e.d, e.a, e.b, e.c, e.m].filter(f => f.n && isInt(f)).map(f => Math.abs(f.n)));
    const splits = e.rel === '=' ? [SPLIT('two', fAbs(e.d))] : [SPLIT('between', fAbs(e.d)), SPLIT('outside', fAbs(e.d))];
    let hand;
    if (alone) {
      // In order of importance, so trimming to the hand size drops number cards first: the right card, the
      // other Split (choosing is the skill), the other verdict, the dropped-bars mistake, then numbers.
      hand = [correct];
      for (const sp of splits) if (sp.way !== correct.way) hand.push(sp);
      if (isDeclare(correct)) hand.push({ op: correct.op === 'none' ? 'all' : 'none', scope: 'part' });
      else if (!tut && Math.random() < 0.4) hand.push({ op: e.rel === '=' || !gtRel(e.rel) ? 'none' : pick(['none', 'all']), scope: 'part' });
      if (!tut) hand.push(dropBars(e));
      hand = hand.slice(0, size);
      hand.push(...decoys(nums, size - hand.length, hand));
    } else {
      // Before the bars are alone they are one block, like x: Act 1's hand builder fits. A Split is a wrong card until then.
      hand = [...makeHand(absS(e), correct, size - 1), pick(splits)];
    }
    return shuffle(hand);
  }
  function absWhyWrong(e, card, target) {
    const alone = barsAlone(e), d = fracText(e.d), u = `|${innerText(e)}|`;
    if (card.op === 'trap') return `That's a trap: the bars can't just be dropped. Tap Why? to see why.`;
    if (isDeclare(card)) {
      if (!alone) return 'Get the bars alone first, then look at the number on the other side.';
      if (e.d.n > 0) return `${u} ${e.rel} ${d} has answers: split the bars into cases.`;
      return gtRel(e.rel) ? `A distance is never negative, so ${u} is always more than ${d}: every number works.`
        : `A distance is never negative, so ${u} can't ${e.rel === '=' ? 'be' : 'be less than'} ${d}: no solution.`;
    }
    if (card.op === 'split') {
      if (!alone) return 'Get the bars alone on their side before splitting.';
      if (e.d.n < 0) return `A distance from 0 can't be negative, so there's nothing to split: ${negVerdict(e) === 'none' ? 'no number works' : 'every number works'}.`;
      if ((card.way || 'two') !== wayFor(e.rel)) return gtRel(e.rel) ? `More than ${d} away from 0 is outside: below ${fracText(fMul(e.d, F(-1)))} or above ${d}. Use Outside.`
        : `Less than ${d} away from 0 is between ${fracText(fMul(e.d, F(-1)))} and ${d}. Use Between.`;
      return 'Drop Split on the bars.';
    }
    if (alone) return e.d.n < 0 ? `That's allowed, but look at the number: ${u} ${e.rel} ${d}. Can a distance be negative?` : `That's allowed, but the bars are alone now: split them into cases.`;
    if (e.c.n !== 0 && SCALE_OPS.includes(card.op)) return `That's allowed, but undo the + or ${MINUS} first, then the ${TIMES} or ${DIV}.`;
    return `That's allowed, but the bars still aren't alone: ${absText(absApply(e, card))}`;
  }
  function explainAbs(e, card, correct) {
    const P = t => `<p>${t}</p>`, out = [], d = fracText(e.d), nd = fracText(fMul(e.d, F(-1))), u = innerText(e);
    const BETWEEN = `Less than ${d} away from 0 means <b>between</b> ${nd} and ${d}: one chain, ${nd} ${e.rel} ${u} ${e.rel} ${d}.`;
    const OUTSIDE = `More than ${d} away from 0 means <b>outside</b>: ${u} ${FLIP[e.rel]} ${nd} or ${u} ${e.rel} ${d}, two cases.`;
    const NEVER = `|${u}| is a distance from 0, and a distance is never negative.`;
    if (isFlip(card)) out.push(P('Flip only comes right after multiplying or dividing by a negative number. Nothing like that has happened here.'));
    else if (isDeclare(card)) out.push(P(!barsAlone(e) ? 'Get the bars alone first. Only then does the number on the other side tell you if there is no solution.'
      : e.d.n > 0 ? `${d} is positive, so |${u}| ${e.rel} ${d} does have answers. ${e.rel === '=' ? `${u} can be ${d} or ${nd}.` : gtRel(e.rel) ? OUTSIDE : BETWEEN}`
      : `${NEVER} So it ${gtRel(e.rel) ? `is always bigger than ${d}, whatever x is: every number works` : `can never ${e.rel === '=' ? 'equal' : 'be below'} ${d}: no number works`}.`));
    else if (card.op === 'split') {
      if (!barsAlone(e)) out.push(P(`Split works on the bars only once they are alone on their side. Here the bars still have ${fIs(e.m, 1) ? '' : `${fracText(e.m)} in front`}${!fIs(e.m, 1) && e.c.n ? ' and ' : ''}${e.c.n ? `${e.c.n < 0 ? MINUS : '+'} ${fracText(fAbs(e.c))} next to them` : ''}. Undo those first, treating |${u}| as one block, like x.`));
      else if (e.d.n < 0) out.push(P(`${NEVER} Splitting |${u}| ${e.rel} ${d} into cases would treat ${d} like a real distance. Look at the sign of the number instead.`));
      else if ((card.way || 'two') !== wayFor(e.rel)) out.push(P(gtRel(e.rel) ? `${OUTSIDE} Between is for "less than": it would keep the numbers close to 0, the opposite of what ${e.rel} asks.` : `${BETWEEN} Outside is for "more than": it would keep the numbers far from 0, the opposite of what ${e.rel} asks.`));
      else out.push(P('Split goes on the bars themselves.'));
    } else out.push(P(`${cardText(card)} is allowed, but it turns it into ${absH(absApply(e, card))}, which doesn't get the bars alone.`));
    let how;
    if (isDeclare(correct)) how = `${NEVER} So |${u}| ${e.rel} ${d} is ${correct.op === 'all' ? 'true for every number: play All x' : 'never true: play No solution'}.`;
    else if (correct.op === 'split') how = e.rel === '=' ? `The bars are alone. |${u}| = ${d} means ${u} is ${d} away from 0, so it is ${d} or ${nd}. Drop Split on the bars to make the two cases.`
      : gtRel(e.rel) ? `The bars are alone. ${OUTSIDE} Drop Outside on the bars.` : `The bars are alone. ${BETWEEN} Drop Between on the bars.`;
    else if (correct.op === '+' || correct.op === '-') how = `Treat the bars as one block and undo the number added to it: ${cardText(correct).toLowerCase()}.`;
    else how = `Treat the bars as one block. ${cardText(correct)} leaves them alone on their side.`;
    out.push(P(`<b>What works here:</b> ${how}`));
    return out.join('');
  }

  // Animations
  // + or − before the split: written under the number next to the bars and under the other side; it cancels.
  // ÷ before the split: a fraction bar under each whole side; the number in front of the bars cancels.
  async function absStepAnim(card, s, ns) {
    const other = roleEl('other'), div = card.op === '/';
    caption(cardText(card));
    const target = card.op === '+' || card.op === '-' ? roleEl('const') : roleEl('coef');
    const leftEls = ['coef', 'abs', 'const'].map(roleEl).filter(Boolean);
    const n1 = div ? note(paren(F(card.n)), leftEls, { bar: true }) : note(chipHtml(card), [target || roleEl('abs')]);
    const n2 = div ? note(paren(F(card.n)), [other], { bar: true }) : note(chipHtml(card), [other]);
    await hold();
    if (target) { mark([target, n1], 'cancel'); await quick(250); dropNote(n1); await removeTok([target]); } else dropNote(n1);
    mark([other, n2], 'merge'); await quick(200); dropNote(n2);
    other.classList.remove('merge'); other.innerHTML = fracHtml(ns.d); kickClass(other, 'pop');
    const how = div ? `${fracText(s.d)} over ${paren(F(card.n))} = ${fracText(ns.d)}` : `${fracText(s.d)} ${card.op === '+' ? '+' : MINUS} ${card.n} = ${fracText(ns.d)}`;
    caption(`${target ? `${target.textContent.replace(/\s/g, '')} and ${cardLabel(card)} cancel, and ` : ''}${how}`);
    await quick(300); await hold();
  }
  // Split: the bars glow and fade, then the cases come out of the equation, one going up, one down (or,
  // for "less than", the chain from −d to d is written around what was inside).
  async function splitAnim(card, s, ns) {
    const t = roleEl('abs'), bars = t ? [...t.querySelectorAll('.bar')] : [];
    const d = fracText(s.d), nd = fracText(fMul(s.d, F(-1))), u = innerText(s);
    caption(s.rel === '=' ? `|${u}| = ${d}: ${u} is ${d} away from 0, so it is ${d} or ${nd}`
      : s.rel === '<' || s.rel === '≤' ? `Less than ${d} away from 0 means between ${nd} and ${d}`
      : `More than ${d} away from 0 means above ${d} or below ${nd}`);
    mark(bars, 'glow'); await quick(500);
    mark(bars, 'fade'); await quick(350);
    await hold();
    if (ns.board && boardSolved(ns)) {     // review fix: both cases solved by the split itself
      renderBoard(ns); caption(`Both cases are already solved: ${boardAnswer(ns)}`);
      drawLine(boardSegs(ns), true); await quick(1100); await hold();
    } else if (ns.board) {
      drawCases(ns, true);
      $('equation').classList.add('absSplitOut'); await quick(450); $('equation').classList.remove('absSplitOut');
      caption('Two cases: solve each one');
      await hold();
    }
  }
  // No solution: a crack runs through the equation and it falls apart. Every number: it glows. Then the
  // number line shows the answer, empty or shaded all the way.
  async function verdictAnim(card, s, ns) {
    const el = $('equation'), toks = [...el.querySelectorAll('.tok')], d = fracText(s.d), u = `|${innerText(s)}|`;
    if (card.op === 'none') {
      caption(`${u} is a distance from 0, and a distance is never negative: ${u} ${s.rel} ${d} never happens, so there is no solution`);
      const box = el.getBoundingClientRect(), r = toks[0].getBoundingClientRect(), last = toks[toks.length - 1].getBoundingClientRect();
      const w = last.right - r.left, h = r.height, svgNS = 'http://www.w3.org/2000/svg', svg = document.createElementNS(svgNS, 'svg');
      svg.setAttribute('class', 'a2crack'); svg.setAttribute('viewBox', `0 0 ${w} ${h}`);
      Object.assign(svg.style, { left: (r.left - box.left + el.scrollLeft) + 'px', top: (r.top - box.top) + 'px', width: w + 'px', height: h + 'px' });
      let path = `M0,${h / 2}`;
      for (let k = 1; k <= 8; k++) path += ` L${(w * k) / 8},${h / 2 + (k % 2 ? -1 : 1) * h * 0.22}`;
      svg.innerHTML = `<path d="${path}"/>`;
      el.appendChild(svg); kickClass(el, 'shake');
      await quick(700); svg.remove();
      toks.forEach(t => { t.style.transform = `translate(${rand(-50, 50)}px, ${rand(60, 140)}px) rotate(${rand(-70, 70)}deg)`; t.style.opacity = '0'; });
      await quick(600);
    } else {
      caption(`${u} is a distance from 0, so it is never negative: it is always more than ${d}, whatever x is. Every number works`);
      mark(toks, 'glow'); await quick(800);
    }
    await hold();
    renderAbs(ns);
    caption(ns.result === 'none' ? 'No number works, so nothing is shaded' : 'Every number works, so the whole line is shaded');
    drawLine(verdictSegs(ns), true);
    await quick(900); await hold();
  }
  // On a board, the active case plays its usual animation; when it's done, the next case comes up.
  async function boardAnim(card, s, ns, ref) {
    const b = boardActive(s), nb = ns.branches[s.active];
    await singleAnim(card, b, nb, ref, true);
    if (!isSolved(nb)) return;
    const sol = solution(nb);
    if (boardSolved(ns)) {
      renderBoard(ns);
      const segs = boardSegs(ns);
      caption(segs.every(g => g.lo === g.hi) ? `Both cases work: ${boardAnswer(ns)}` : `Either case works: ${boardAnswer(ns)}`);
      drawLine(segs, true);
      await quick(1100); await hold();
    } else {
      caption(`Case ${s.active + 1} done: x ${sol.rel} ${fracText(sol.v)}. Now case ${ns.active + 1}.`);
      drawCases({ ...ns, active: s.active });
      await hold();
    }
  }

  // Generators. The two answers (or ends) x1 < x2 are whole numbers on Easy; the inner part is ax + b
  // with a = 1, 2 or 3, so u = d gives x2 and u = −d gives x1.  Shapes:
  //   plain  |ax + b| rel d          front  |ax + b| + c rel d + c       times  m|ax + b| rel m·d
  //   both   m|ax + b| + c rel m·d + c                       (|3x| = 12 has b = 0)
  // Difficulty: Normal and up use bigger spreads and more steps in front; Expert can land on fractions.
  // want picks the case: two-int / two-frac (stage 12), between-* / outside-* (stage 13), none, all. Fraction
  // answers and the no-solution cases come up at every difficulty; harder levels only change the numbers
  // and the steps in front of the bars.
  function absCore(D, frac) {
    const a = frac ? pick([2, 3]) : pick([1, 1, 2, 3]), x1 = rand(D.neg ? -9 : -5, 5), gap = rand(1, D.level >= 2 ? 8 : 5) * (a % 2 ? 2 : 1);
    const x2 = x1 + gap, d = (a * gap) / 2, b = d - a * x2;     // a·x2 + b = d and a·x1 + b = −d
    return frac ? { a, b, d: d + 1 } : { a, b, d };                // d + 1: the answers land on fractions
  }
  function genAbsWith(rel, type, tut, want) {
    const D = tut ? DIFFICULTIES[0] : difficulty;
    const neg = want === 'none' || want === 'all', { a, b, d } = absCore(D, /frac/.test(want || ''));
    const dd = neg ? -rand(1, 6) : d;                              // with the bars alone, |u| rel dd
    const t = type || pick(D.level ? ['plain', 'front', 'times', 'both', 'both'] : ['plain', 'plain', 'front', 'times']);
    const m = t === 'times' || t === 'both' ? rand(2, D.level >= 2 ? 5 : 3) : 1;
    let c = t === 'front' || t === 'both' ? nonZero(-9, 9) * (D.level >= 2 ? 2 : 1) : 0;
    if (c && m * dd + c === 0) c += c > 0 ? 1 : -1;              // keep the right side off 0, so it doesn't look like |u| = 0
    return AB(m, a, b, c, rel, m * dd + c);
  }
  function genAbsEq(type, want, tut = isTutorial()) {
    const w = want || (tut ? 'two-int' : anyCase('absval'));
    return { ineq: { ...genAbsWith('=', type, tut, w), skill: 'absval' }, enemy: 'mirrorling' };
  }
  function genAbsIneq(type, want, tut = isTutorial()) {
    const w = want || (tut ? 'between-int' : anyCase('absineq'));
    const rel = /^between|^none/.test(w) ? pick(['<', '≤']) : pick(['>', '≥']);
    return { ineq: { ...genAbsWith(rel, type, tut, w), skill: 'absineq' }, enemy: 'mirrorling' };
  }
  // Stage 11 also gets "or" compounds now that boards exist: 2x + 1 < −3 or 3x − 2 > 7.
  function genOrCompound() {
    const p = rand(-6, 1), q = p + rand(2, 6), a1 = rand(1, 4), b1 = nonZero(-8, 8), a2 = rand(1, 4), b2 = nonZero(-8, 8);
    const lo = pick(['<', '≤']), hi = pick(['>', '≥']);
    return { ineq: { board: true, join: 'or', active: 0, skill: 'compound', branches: [I([X(a1), N(b1)], [N(a1 * p + b1)], lo), I([X(a2), N(b2)], [N(a2 * q + b2)], hi)] }, enemy: 'clamp' };
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
  // want = a stage 10 case, keep/flip and pos/neg/frac (see CASES); without one, the run's least-seen case.
  // A fraction answer needs a number in front of x: x = 3/2 comes from 2x < 3.
  const FRAC_OK = ['mul', 'two', 'twom', 'negmul', 'negtwo', 'negtwo2'];
  function genIneq(type, want, tut = isTutorial()) {
    const w = want || (type || tut ? null : anyCase('ineq'));
    const [fk, ak] = w ? w.split('-') : [null, tut ? 'pos' : pick(['pos', 'neg'])];
    for (;;) {
      const pool = (fk === 'flip' ? FLIPS : fk === 'keep' ? KEEPS : [...FLIPS, ...KEEPS]).filter(t => ak !== 'frac' || FRAC_OK.includes(t));
      const t = type || pick(pool);
      const a = rand(2, ak === 'frac' ? 4 : 6), b = rand(1, 12), rel = pick(RELS);
      let x;     // the answer
      if (ak === 'frac') { let k; do k = nonZero(-3 * a, 3 * a); while (k % a === 0); x = F(k, a); }
      else x = F(ak === 'neg' ? -rand(1, 8) : rand(1, 8));
      const ax = fMul(F(a), x), sgn = x.n < 0 ? -1 : 1, enemy = FLIPS.includes(t) ? 'flipjack' : 'tilter';
      let e;
      if (t === 'add') e = I([X(1), N(b)], [N(fAdd(x, F(b)))], rel);
      else if (t === 'sub') e = I([X(1), N(-b)], [N(fAdd(x, F(-b)))], rel);
      else if (t === 'mul') e = I([X(a)], [N(ax)], rel);
      else if (t === 'div') e = I([X(F(1, a))], [N(rand(1, 9) * sgn)], rel);
      else if (t === 'two') e = I([X(a), N(b)], [N(fAdd(ax, F(b)))], rel);
      else if (t === 'twom') e = I([X(a), N(-b)], [N(fAdd(ax, F(-b)))], rel);
      else if (t === 'negx') e = I([X(-1)], [N(fMul(x, F(-1)))], rel);
      else if (t === 'negmul') e = I([X(-a)], [N(fMul(ax, F(-1)))], rel);
      else if (t === 'negtwo') e = I([N(b), X(-a)], [N(fAdd(F(b), fMul(ax, F(-1))))], rel);
      else if (t === 'negtwo2') e = I([X(-a), N(b)], [N(fAdd(fMul(ax, F(-1)), F(b)))], rel);
      else e = I([X(F(-1, a))], [N(rand(1, 9) * -sgn)], rel);
      if ([...e.L, ...e.R].length < 2) continue;
      return { ineq: e, enemy };
    }
  }

  // Elites stack inequalities with an Act 2 move, and usually still need a flip at the end:
  //   −2(x − 3) < 10    3x − 5x + 4 ≥ 10    2x + 5 > 5x − 4 (written so the x-term left over is negative)
  function genStacked3() {
    // Once compound inequalities are open, some elites are a chain that needs a flip, with bigger numbers.
    if (isUnlocked('compound') && Math.random() < 0.35) { const g = genCompound(null, anyCase('compound', k => k.startsWith('flip'))); return { ...g, enemy: 'boundwarden' }; }
    if (isUnlocked('absval') && Math.random() < 0.35) { const g = isUnlocked('absineq') && Math.random() < 0.5 ? genAbsIneq('both', null, false) : genAbsEq('both', null, false); return { ...g, enemy: 'boundwarden' }; }
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

  // Generators. Shapes (Easy), with the answer p ≤ x ≤ q between two whole numbers:
  //   one   p+b < x + b ≤ q+b        mul  ap < ax < aq          two  lo < ax + b ≤ hi
  //   div   lo ≤ x/a + b < hi        neg  lo < b − ax ≤ hi (flip)   negmul  lo ≤ −ax < hi (flip)
  //   negx  lo < b − x < hi (flip)
  const FLIPS_C = ['neg', 'negmul', 'negx'], KEEPS_C = ['one', 'mul', 'two', 'div'];
  // want = a stage 11 case (see CASES). The answer runs from P to Q: whole numbers above 0 (pos), starting
  // below 0 (neg), or fractions with a number in front of x (frac, e.g. 3/2 < x ≤ 9/2 from 3 < 2x ≤ 9).
  function genCompound(type, want, tut = isTutorial()) {
    const w = want || (type || tut ? null : anyCase('compound'));
    if (w === 'or') return genOrCompound();
    const [fk, ak] = w ? w.split('-') : [null, tut ? 'pos' : pick(['pos', 'neg'])];
    const pool = (fk === 'flip' ? FLIPS_C : fk === 'keep' ? KEEPS_C : [...FLIPS_C, ...KEEPS_C]).filter(t => ak !== 'frac' || ['mul', 'two', 'neg', 'negmul'].includes(t));
    const t = type || pick(pool);
    const a = rand(2, 5), b = nonZero(-9, 9), relP = pick(['<', '≤']), relQ = pick(['<', '≤']);
    let P;
    if (ak === 'frac') { let k; do k = nonZero(-2 * a, 3 * a); while (k % a === 0); P = F(k, a); }
    else P = F(ak === 'neg' ? rand(-8, -1) : rand(1, 4));
    let Q = fAdd(P, F(rand(2, tut ? 5 : 7)));
    if (t === 'div') { P = fMul(P, F(a)); Q = fMul(Q, F(a)); }
    const A = F(a), aP = fMul(A, P), aQ = fMul(A, Q), neg = v => fMul(v, F(-1));
    let e;
    if (t === 'one') e = CH(fAdd(P, F(b)), relP, 1, b, relQ, fAdd(Q, F(b)));
    else if (t === 'mul') e = CH(aP, relP, a, 0, relQ, aQ);
    else if (t === 'two') e = CH(fAdd(aP, F(b)), relP, a, b, relQ, fAdd(aQ, F(b)));
    else if (t === 'div') e = CH(fAdd(fMul(P, F(1, a)), F(b)), relP, F(1, a), b, relQ, fAdd(fMul(Q, F(1, a)), F(b)));
    else if (t === 'neg') { const bb = Math.abs(b); e = CH(fAdd(F(bb), neg(aQ)), relQ, -a, bb, relP, fAdd(F(bb), neg(aP)), true); }
    else if (t === 'negmul') e = CH(neg(aQ), relQ, -a, 0, relP, neg(aP));
    else { const bb = rand(3, 12); e = CH(fAdd(F(bb), neg(Q)), relQ, -1, bb, relP, fAdd(F(bb), neg(P)), true); }
    return { ineq: { ...e, skill: 'compound' }, enemy: 'clamp' };
  }
  // Difficulty: Normal and up multiply the numbers (and so the answer) by 2 or 3, and may turn the
  // whole chain negative; Expert nudges one end so the answer can end on a fraction.
  function chainDifficulty(g, regen) {
    const D = difficulty;
    for (let tries = 0; tries < 30; tries++, g = regen()) {
      if (!g.ineq || !g.ineq.chain) return prepare3(g, regen);    // a mixed generator (an elite) re-rolled something else
      let e = { ...g.ineq };
      let end0 = e; for (const p of chainPath(e, 'compound')) end0 = chainApply(end0, p.move);
      const fracOK = !isInt(end0.lo) || !isInt(end0.hi);     // the generator asked for a fraction case
      const f = D.level >= 2 ? rand(2, 3) : D.level === 1 ? rand(1, 2) : 1;
      e.lo = fMul(e.lo, F(f)); e.hi = fMul(e.hi, F(f)); e.b = fMul(e.b, F(f));
      if (D.neg && Math.random() < 0.5) e = { ...e, lo: fMul(e.hi, F(-1)), hi: fMul(e.lo, F(-1)), b: fMul(e.b, F(-1)), rel1: e.rel2, rel2: e.rel1, constFirst: e.constFirst && Math.random() < 0.5 };
      // Review fix: pick the end once. Picking twice set lo = hi ± k half the time, collapsing the chain to a sliver.
      if (D.fracAnswers) { const end = pick(['lo', 'hi']); e[end] = fAdd(e[end], F(nonZero(-2, 2))); }
      if (e.b.n === 0) e.constFirst = false;
      let end = e; for (const p of chainPath(e, 'compound')) end = chainApply(end, p.move);
      if (!fLess(end.lo, end.hi)) continue;                  // the ends must stay in order
      if ([e.lo, e.hi, e.b].some(k => Math.abs(k.n) > D.max * 2)) continue;
      if (!D.fracAnswers && !fracOK && (!isInt(end.lo) || !isInt(end.hi))) continue;
      return { ...g, ineq: e };
    }
    return g;

  }

  // ================================================================ the engine (index.html calls these)
  function apply(e, c, ref) {
    switch (kindOf(e)) {
      case 'board': return boardApply(e, c, ref);
      case 'abs': return absApply(e, c);
      case 'chain': return chainApply(e, c);
      default: return sApply(e, c, ref);
    }
  }
  function isSolved(e) {
    switch (kindOf(e)) {
      case 'board': return boardSolved(e);
      case 'abs': return !!e.result;
      case 'chain': return chainSteps(e) === 0;
      default: return sSolved(e);
    }
  }
  // The expected moves from a state to the answer, each tagged with the skill it practises.
  function pathOf(e, main) {
    switch (kindOf(e)) {
      case 'board': return e.branches.slice(e.active).flatMap(b => sPath(b, main));
      case 'chain': return chainPath(e, main);
      case 'abs': {
        if (e.result) return [];
        const path = []; let s = e;
        for (let i = 0; i < 4 && s.abs && !s.result; i++) { const m = absCanon(s); path.push({ state: s, move: m, skill: main }); s = absApply(s, m); }
        return path.concat(pathOf(s, main));
      }
      default: return sPath(e, main);
    }
  }
  function answerOf(e) {
    const k = kindOf(e);
    if (k === 'board') return boardAnswer(e);
    if (k === 'chain') return `${fracText(e.lo)} ${e.rel1} x ${e.rel2} ${fracText(e.hi)}`;
    if (k === 'abs') return absText(e);
    const sol = solution(e);
    return sol ? `x ${sol.rel} ${fracText(sol.v)}` : textOf(e);
  }
  // Which case of its stage a question is (see CASES), worked out from its path and its answer.
  function caseOf(main, start, path, end) {
    const flip = path.some(p => isFlip(p.move)) ? 'flip' : 'keep';
    const ends = e => (kindOf(e) === 'chain' ? [e.lo, e.hi] : kindOf(e) === 'board' ? e.branches.map(b => solution(b).v) : kindOf(e) === 'single' ? [solution(e).v] : []);
    const split = path.find(p => p.move.op === 'split');
    if (main === 'absval' || main === 'absineq') {
      if (end.result) return end.result;
      const k = ansKind(ends(end)) === 'frac' ? 'frac' : 'int';
      return main === 'absval' ? `two-${k}` : `${split && split.move.way === 'between' ? 'between' : 'outside'}-${k}`;
    }
    if (main === 'compound' && kindOf(start) === 'board') return 'or';
    return `${flip}-${ansKind(ends(end))}`;
  }
  function makeEquation3(eq, enemy) {
    const main = eq.skill || 'ineq', path = pathOf(eq, main);
    let end = eq; for (const p of path) end = apply(end, p.move, p.move.ref);
    return { start: eq, end, path, main, skills: [...new Set(path.map(p => p.skill))], enemy, act2: true, act3: true, answer: F(0), answerText: answerOf(end) };
  }
  function refreshPath(cur) { cur.path = cur.path.slice(0, cur.step).concat(pathOf(cur.state, cur.main)); }
  function isCorrect(cur, card, target) {
    const e = cur.state;
    switch (kindOf(e)) {
      case 'board': return sCorrect(boardActive(e), card, target);
      case 'abs': return absCorrect(e, card, target);
      case 'chain': return chainCorrect(e, card, target);
      default: return sCorrect(e, card, target);
    }
  }
  function makeHand3(e, correct, size) {
    switch (kindOf(e)) {
      case 'board': return sHand(boardActive(e), correct, size, true);
      case 'abs': return absHand(e, correct, size);
      case 'chain': return chainHand(e, correct, size);
      default: return sHand(e, correct, size);
    }
  }
  function whyWrong(cur, card, target) {
    const e = cur.state, want = cur.path[cur.step].move;
    if (isFlip(card) && !onSign(target) && isCorrect({ state: e }, card, 'rel')) return 'Right card, but Flip goes on the sign itself: drop it on the < or >.';
    if (card.op === 'split' && !(roleOf(target) === 'abs') && kindOf(e) === 'abs' && absCorrect(e, card, 'abs')) return 'Right card, but Split goes on the bars: drop it on the | |.';
    switch (kindOf(e)) {
      case 'board': return sWhyWrong(boardActive(e), card, want, target);
      case 'abs': return absWhyWrong(e, card, target);
      case 'chain': return chainWhyWrong(e, card);
      default: return sWhyWrong(e, card, want, target);
    }
  }
  // "Why?" for every Act 3 state. Trap cards carry their own text (card.why), which explainWhy shows first.
  function explain3({ state: e, card, correct, ref }) {
    if (!e || !card || !correct) return null;
    switch (kindOf(e)) {
      case 'board': return explainSingle(boardActive(e), card, correct, ref);
      case 'abs': return explainAbs(e, card, correct);
      case 'chain': return explainChain(e, card, correct);
      default: return e.rel ? explainSingle(e, card, correct, ref) : null;
    }
  }
  if (typeof registerWhy === 'function') registerWhy(explain3);
  function render(e) {
    switch (kindOf(e)) {
      case 'board': return renderBoard(e);
      case 'abs': return renderAbs(e);
      case 'chain': return renderChain(e);
      default: return renderSingle(e);
    }
  }
  function animFor() {
    return async (c, s, ns, ref) => {
      switch (kindOf(s)) {
        case 'board': return boardAnim(c, s, ns, ref);
        case 'abs': return c.op === 'split' ? splitAnim(c, s, ns) : isDeclare(c) ? verdictAnim(c, s, ns) : absStepAnim(c, s, ns);
        case 'chain': return chainAnim(c, s, ns);
        default: return singleAnim(c, s, ns, ref, false);
      }
    };
  }
  function textOf(e) {
    switch (kindOf(e)) {
      case 'board': return boardText(e);
      case 'abs': return absText(e);
      case 'chain': return chainText(e);
      default: return eqText(e);
    }
  }
  // The shared variety system (index.html freshEquation): writes a state, and mirrors a single inequality
  // (sides swap and the sign turns around, so it means the same thing). The other kinds aren't mirrored.
  if (typeof ENGINES === 'object') ENGINES.ineq = { text: textOf, mirror: e => (kindOf(e) === 'single' ? swapI(e) : e) };

  // Difficulty: single inequalities use Act 2's rules (bigger numbers, negatives, extra steps, fraction
  // answers on Expert); they only scale plain numbers, so a negative x-coefficient (the flip) stays.
  // Chains have their own; absolute value generators read the difficulty themselves.
  function caseOfG(g) {
    const main = g.ineq.skill || 'ineq', path = pathOf(g.ineq, main);
    let end = g.ineq; for (const p of path) end = apply(end, p.move, p.move.ref);
    return caseOf(main, g.ineq, path, end);
  }
  // A question from the case cycle keeps its case: re-roll until the harder numbers still give it.
  function applyDifficulty3(g, regen) {
    if (!g.case) return prepare3(g, regen);
    let out = g;
    for (let i = 0; i < 30; i++) { out = prepare3(i ? regen() : g, regen); if (caseOfG(out) === g.case) return out; }
    return out;
  }
  function prepare3(g, regen) {
    const k = kindOf(g.ineq);
    if (k === 'chain') return chainDifficulty(g, regen);
    if (k !== 'single') return g;
    const asEq = r => { const { ineq, ...rest } = r; return { ...rest, eq: ineq }; };
    const again = () => { for (let i = 0; i < 20; i++) { const r = regen(); if (kindOf(r.ineq) === 'single') return asEq(r); } return asEq(g); };
    // Act 2's extra x-term step hides the flip (Act 2 always removes the smaller x-term, which leaves a
    // positive x), so an inequality that needs a flip only gets the other extra steps, and keeps its flip.
    const flips = e => pathOf(e, 'ineq').some(p => isFlip(p.move));
    const want = flips(g.ineq);
    let out;
    for (let i = 0; i < 25; i++) {
      const { eq, ...rest } = A2.applyDifficulty(asEq(g), again, { noXadd: want, keepAnswer: true, messyOK: /frac/.test(g.case || '') });
      out = { ...rest, ineq: { ...eq, rel: eq.rel || g.ineq.rel } };
      if (!want || flips(out.ineq)) return out;
    }
    return out;
  }

  // Act 3 elite and boss fights. list = the unlocked skills this run can use, oldest first.
  function buildFight3(node, list) {
    const act3 = list.filter(id => (SKILL[id].act || 1) === 3);
    if (node.type === 'elite') return { phases: [genStacked3], handSize: difficulty.hand, enemy: 'boundwarden' };
    // Boss: an inequality that keeps its sign, one that needs a flip, one phase per later Act 3 stage, then a stacked one.
    const phases = [() => genIneq(null, anyCase('ineq', k => k.startsWith('keep'))), () => genIneq(null, anyCase('ineq', k => k.startsWith('flip')))];
    for (const id of act3.slice(1)) phases.push(SKILL[id].gen);
    phases.push(genStacked3);
    return { phases, handSize: difficulty.hand, enemy: 'leaningtower' };
  }
  // ---------------------------------------------------------------- skills, enemies, act
  SKILLS.push(
    { id: 'ineq', stage: 10, act: 3, name: 'Inequalities', cases: CASES.ineq, gen: cycled('ineq', c => genIneq(null, c)),
      title: 'Stage 10: Inequalities',
      intro: 'An inequality uses &lt;, &gt;, ≤ or ≥ instead of =, and its answer is a whole range of numbers. Solve it the same way as an equation, with one new rule: after multiplying or dividing both sides by a <b>negative</b> number, the sign has to flip. That is its own move: drop the new ◎ Flip card on the sign. Flipping at any other time is a wrong move. The answer is then shaded on a number line.',
      example: '2x + 1 &lt; 9<br>Subtract 1 from both sides → 2x &lt; 8<br>Divide both sides by 2 → x &lt; 4<br><br>−3x ≥ 12<br>Divide both sides by −3 → x ≥ −4 (not true yet!)<br>Flip the sign → x ≤ −4',
      tutorial: [() => genIneq('two', null, true), () => genIneq('negmul', null, true)] },
    { id: 'compound', stage: 11, act: 3, name: 'Compound inequalities', cases: CASES.compound, gen: cycled('compound', c => genCompound(null, c)),
      title: 'Stage 11: Compound inequalities',
      intro: 'A compound inequality squeezes x between two numbers: −3 &lt; 2x + 1 ≤ 7 means 2x + 1 is above −3 <b>and</b> at most 7. It has three parts, and every card now does the same thing to all three. After a negative × or ÷, Flip turns both signs around, and the chain is read from the other end so the smaller number comes first. Some are "or" compounds instead: two cases, solved one after the other.',
      example: '−3 &lt; 2x + 1 ≤ 7<br>Subtract 1 from all three parts → −4 &lt; 2x ≤ 6<br>Divide all three parts by 2 → −2 &lt; x ≤ 3<br><br>1 ≤ 7 − 2x &lt; 5<br>Subtract 7 → −6 ≤ −2x &lt; −2<br>Divide by −2 → 3 ≤ x &lt; 1 (can\'t be true)<br>Flip both signs → 3 ≥ x &gt; 1, which reads 1 &lt; x ≤ 3',
      tutorial: [() => genCompound('two', null, true), () => genCompound('neg', null, true)] },
    { id: 'absval', stage: 12, act: 3, name: 'Absolute value', cases: CASES.absval, gen: cycled('absval', c => genAbsEq(null, c)),
      title: 'Stage 12: Absolute value equations',
      intro: 'The bars | | mean distance from 0: |5| = 5 and |−5| = 5. So |x − 3| = 5 means x − 3 is 5 away from 0, which is 5 <b>or</b> −5. First get the bars alone, treating them as one block. Then drop the new ◎ Split card on the bars: it makes two cases, and you solve each one. One catch: a distance is never negative, so if the bars end up equal to a negative number, like |x − 3| = −5, nothing works. Declare No solution instead of splitting.',
      example: '|x − 3| = 5<br>Split → x − 3 = 5 or x − 3 = −5<br>Case 1: add 3 → x = 8<br>Case 2: add 3 → x = −2<br>Answer: x = 8 or x = −2<br><br>|x − 3| + 8 = 3<br>Subtract 8 → |x − 3| = −5<br>A distance can\'t be −5 → No solution',
      tutorial: [() => genAbsEq('plain', 'two-int', true), () => genAbsEq('front', 'two-int', true)] },
    { id: 'absineq', stage: 13, act: 3, name: 'Abs. inequalities', cases: CASES.absineq, gen: cycled('absineq', c => genAbsIneq(null, c)),
      title: 'Stage 13: Absolute value inequalities',
      intro: 'For inequalities there are two Split cards, and you choose. Less than 7 away from 0 means <b>between</b> −7 and 7, so drop ◎ Between on |u| &lt; 7 to get one chain, −7 &lt; u &lt; 7. More than 7 away means <b>outside</b>, so drop ◎ Outside on |u| &gt; 7 to get two cases, u &lt; −7 or u &gt; 7. If the number is negative, a distance is never below it (|u| &lt; −2: No solution) and always above it (|u| &gt; −2: All x).',
      example: '|2x − 1| &lt; 7<br>Between → −7 &lt; 2x − 1 &lt; 7<br>Add 1 → −6 &lt; 2x &lt; 8<br>Divide by 2 → −3 &lt; x &lt; 4<br><br>|x + 2| ≥ 4<br>Outside → x + 2 ≤ −4 or x + 2 ≥ 4<br>→ x ≤ −6 or x ≥ 2<br><br>|x − 1| ≥ −3 → All x',
      tutorial: [() => genAbsIneq('plain', 'between-int', true), () => genAbsIneq('plain', 'outside-int', true)] },
  );
  for (const s of SKILLS) SKILL[s.id] = s;
  progress = loadProgress();     // the save was first read before this skill existed

  Object.assign(ENEMIES, {
    tilter:       { name: 'Tilter',         rank: 'Normal', color: '#90be6d', size: 84 },
    flipjack:     { name: 'Flip-Jack',      rank: 'Normal', color: '#f9844a', size: 84 },
    clamp:        { name: 'Clamp',          rank: 'Normal', color: '#43aa8b', size: 84 },
    mirrorling:   { name: 'Mirrorling',     rank: 'Normal', color: '#b5838d', size: 84 },
    boundwarden:  { name: 'Bound Warden',   rank: 'Elite',  color: '#577590', size: 100, horns: true },
    leaningtower: { name: 'The Leaning Tower', rank: 'Boss', color: '#f94144', size: 120, crown: true },
  });
  ACTS[3] = { name: 'The Leaning Stacks', sub: 'Inequalities and absolute value', boss: 'The Leaning Tower', firstSkill: 'ineq',
    blurb: 'The shelves here lean one way or the other, and so do the equations: their answers are whole ranges of numbers. Watch out for negatives, which make you flip the sign. Defeat The Leaning Tower.' };

  const css = document.createElement('style');
  css.textContent = `
    .tok.eq.rel { color:var(--ink); transition: transform .26s ease-in, color .2s; }
    .tok.eq.relflip { transform: rotateY(90deg) scale(1.25); color:#7bdff2; }
    .tok.eq.relnew { color:var(--accent); transform: scale(1.15); }
    .tok.eq.rel.owed { color:var(--bad); animation: owed 1s ease-in-out infinite; }
    @keyframes owed { 50% { transform: scale(1.12); text-shadow: 0 0 12px #ef476f; } }
    /* Flip is dropped on the sign: the sign is a drop target while a ◎ card is held */
    #arena.targeting .tok.eq.rel { border-color: var(--muted); background:#ffffff0d; }
    .tok.absTok .bar { display:inline-block; color:#7bdff2; transition: opacity .35s, transform .35s, text-shadow .3s; }
    .tok.absTok .bar.glow { text-shadow: 0 0 14px #7bdff2, 0 0 4px #fff; }
    .tok.absTok .bar.fade { opacity:0; transform: scaleY(1.6); }
    #equation.absSplitOut .tok { animation: absOut .45s ease-in both; }
    @keyframes absOut { to { opacity:.35; transform: scale(.9); } }
    #cases { display:none; flex-direction:column; align-items:center; gap:2px; font-size:18px; font-weight:bold; }
    #cases.show { display:flex; }
    #cases .case { padding:2px 10px; border:2px solid transparent; border-radius:6px; color:var(--muted); white-space:nowrap; }
    #cases .case.on { color:var(--ink); border-color:var(--accent); }
    #cases .case.done { color:var(--good); }
    #cases .case.split { animation: caseIn .4s cubic-bezier(.2,1.4,.4,1) both; }
    @keyframes caseIn { from { transform: translateY(-24px) scale(.7); opacity:0; } }
    #cases .clabel { font-size:.7em; color:var(--muted); margin-right:6px; }
    #cases .cjoin { font-size:.75em; color:var(--accent); }
    .tok .xv { font-style:normal; color:var(--accent); }
    .tok.chainSwap { transition: transform .6s ease-in-out, color .2s; }
    .unote.split { animation: splitIn .3s cubic-bezier(.2,1.5,.4,1) both; }
    @keyframes splitIn { from { transform: translate(-50%, -40px) scale(.4); opacity:0; } }
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
      #cases { font-size:13px; }
      .card .ftag { margin-top:0; font-size:9px; }
      /* a flip tag is one more line on the card, so phone hands with one get a little taller */
      #hand.many:has(.ftag) .card { height:clamp(92px, 14.5vh, 120px); }
      #hand:not(.many):has(.ftag) .card { height:clamp(122px, 21vh, 156px); }
    }
    @media (orientation: landscape) and (max-height: 520px) { #numline { width:min(300px, 80%); } }
  `;
  document.head.appendChild(css);

  window.ACT3 = { apply, isSolved, solution, segmentsOf, drawLine, clearLine: () => { clearLine(); clearCases(); }, makeEquation: makeEquation3, refreshPath, render, prefit,
    eqText: textOf, makeHand: makeHand3, isCorrect, whyWrong, animFor, applyDifficulty: applyDifficulty3, label, text, kind, kindOf,
    buildFight: buildFight3, genStacked: genStacked3, caseOf: caseOfG, gens: { ineq: genIneq, compound: genCompound, absval: genAbsEq, absineq: genAbsIneq } };
})();
