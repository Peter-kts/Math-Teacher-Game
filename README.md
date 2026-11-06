# Math Teacher Game

A Slay the Spire-style card game where algebra equations are the enemies. This repo holds a playable prototype of Acts 1 and 2, and the start of Act 3.

## Running the prototype

No install or build is needed. Open `prototype/index.html` in any modern browser: double-click the file, or drag it into a browser window. It works offline, with a mouse or a touchscreen. The live copy is at https://peter-kts.github.io/Math-Teacher-Game/.

## How it plays

- Each enemy is an equation. You get a hand of cards, each a legal move like "Subtract 3 from both sides", built from the numbers in the equation. Only one gets x closer to alone.
- Cards marked ⇔ apply to both sides and can be dropped anywhere on the enemy. Cards marked ◎ change one part and must be dropped on that part of the equation. Act 1 only deals ⇔ cards; Act 2 adds the first ◎ cards (Combine, Distribute, and the two Declare cards).
- A wrong move costs 10 of your 100 HP. At 0 HP the run ends, but your mastery is kept.
- Every correct move plays its own animation: the operation is written under the term it acts on (division as a fraction bar under each side), the matching parts cancel, and the other side simplifies. Animation speed can be set to 0.5x, 1x or 2x.
- After a solve there is a short celebration, and the game waits until you tap (or press Space/Enter). The next question slides in.

## Act 1: The Ink Cellar

| Stage | Example | New cards |
|---|---|---|
| 1. One-step | x + 3 = 7, 4x = 20, x/3 = 6 | Add, Subtract, Multiply, Divide both sides |
| 2. Two-step | 3x + 4 = 19, x/2 − 1 = 5 | None: undo + and − before × and ÷ |
| 3. Negatives and fractions | −x = 5, 5 − x = 2, −3x = 12, (2/3)x = 8 | Multiply by −1, Multiply by the reciprocal |

A run is a map of 11 nodes: normal fights, two elites and The Scale Keeper boss.

- **Tutorial fight**: each stage is introduced alone once, with a short explanation and only 3 cards.
- **Normal fights**: about 60% the newest stage, 40% review of earlier stages (skills marked "needs review" come up 3 times as often).
- **Elites** stack the two newest stages in one equation (for example 18 − 4x = −10). Beating one heals 20 HP.
- **Boss**: one phase per unlocked stage (sides swap from phase 2), then a final phase that combines them.

## Act 2: The Bracket Halls

Act 2 opens on the title screen once Negatives & fractions reaches 80 mastery. Its code lives in `prototype/act2.js`, which has its own equation model (several terms per side, parentheses, x on both sides, fractions with x on top).

| Stage | Example | New cards |
|---|---|---|
| 4. Like terms | 3x + 2x − 4 = 11 | ◎ Combine: drop on one of two like terms; they slide together and their numbers add |
| 5. Distributing | 3(x + 2) = 15 | ◎ Distribute: drop on the parentheses; arrows run from the 3 to each term, the products are written underneath, the parentheses dissolve |
| 6. x on both sides | 5x + 3 = 2x + 12 | Subtract (or add) an x-term on both sides: written under the x-term on each side, it cancels on one side and combines on the other |
| 7. Clearing fractions | x/3 + x/4 = 7 | Multiply both sides by the common denominator: the multiplier is stamped under every term and the denominators pop away |
| 8. No solution or every number | 2x + 1 = 2x + 5, 3(x + 1) = 3x + 3 | ◎ No solution (the false statement cracks and shatters), ◎ All x (the true one glows) |

Stage 9 (formulas, d = rt) is not built yet.

- Normal fights mix in earlier ideas, for example 3(x + 2) + x = 18, and review fights can pull from Act 1.
- Elites (Bracket Knight) stack the two newest stages, for example 3(x + 2) = 2x + 9.
- The Archivist boss has one phase per unlocked Act 2 stage, then a combined phase.
- A ◎ card can be played on any part where it is legal and helps, not only the one the game would pick. Dropping Combine on a term with no like partner, or Distribute off the parentheses, counts as a wrong move.
- For testing, the title screen has an "Unlock all stages" button (only on the dev preview, a local file, or with `?debug=1`).
- Difficulty: on Normal and up, every number is multiplied by 2 to 4 (so answers stay whole), signs flip at random, and extra steps are added (a number split in two, or the same x-term added to both sides). Easy keeps answers positive; Expert also allows fraction answers. Tutorials always use Easy numbers.
- Wrong moves come with a "Why?" explanation of what the card did and which move works instead.

## Act 3: The Leaning Stacks

Act 3 opens once No solution / every x reaches 80 mastery. Its code lives in `prototype/act3.js`. It reuses Act 2's equation model with one more field, the relation (<, ≤, >, ≥), and lets Act 2's engine do the algebra.

| Stage | Example | New cards |
|---|---|---|
| 10. Inequalities | 2x + 1 < 9, −3x ≥ 12 | Multiply or divide both sides by a negative: the card says "flip ≥ to ≤". After the usual scale animation, the sign spins around and lands the other way |

Stages 11 to 13 (compound inequalities, absolute value equations, absolute value inequalities) are not built yet.

- **Number line**: when an inequality is solved, the answer is shaded on a number line under it (filled dot for ≤ and ≥, open dot for < and >). It draws any set of intervals, so the later stages can shade "between" and "outside" answers.
- About half of the normal inequality fights need a flip. The shared variety system writes about half the other way round (9 > 2x + 1); the answer is read with x first (4 > x is x < 4).
- Elites (Bound Warden) stack an inequality with an Act 2 move, for example −2(x − 3) < 10. The Leaning Tower boss has a no-flip phase, a flip phase and a stacked phase.
- Difficulty uses Act 2's rules. Expert adds a trap card: the same × or ÷ by a negative, marked "keep ≥". Its Why? checks a number that fits the wrong answer and shows the original inequality coming out false.
- Act 3 plugs into the shared variety system (`ENGINES.ineq`), so no inequality repeats within a run and shapes rotate.

## Mastery and stats

Each stage has a mastery meter from 0 to 100, saved in the browser (`localStorage`) across runs:

- +25 for solving an equation with no wrong moves (par is the fewest moves, so this is also "at par")
- −10 for each wrong move on that skill
- −5 for each week the skill goes unpracticed, down to 60 once mastered
- 80 = mastered, which unlocks the next stage's tutorial fight. Stages never lock again; a mastered skill that drops below 80 is marked "needs review".

The Skills & stats screen shows, per skill: mastery, fights attempted / solved, wrong moves by card, average moves vs par, average seconds per move, hints used and the date last practiced. It also has a reset button.

All art is stand-in.
