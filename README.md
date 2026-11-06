# Math Teacher Game

A Slay the Spire-style card game where algebra equations are the enemies. This repo holds a playable prototype of Act 1.

## Running the prototype

No install or build is needed. Open `prototype/index.html` in any modern browser: double-click the file, or drag it into a browser window. It works offline, with a mouse or a touchscreen. The live copy is at https://peter-kts.github.io/Math-Teacher-Game/.

## How it plays

- Each enemy is an equation. You get a hand of cards, each a legal move like "Subtract 3 from both sides", built from the numbers in the equation. Only one gets x closer to alone.
- Cards marked ⇔ apply to both sides and can be dropped anywhere on the enemy. Cards marked ◎ change one part and must be dropped on that part of the equation. Act 1 only deals ⇔ cards; ◎ is there for later acts (Distribute, Factor and so on).
- A wrong move costs 10 of your 100 HP. At 0 HP the run ends, but your mastery is kept.
- Every correct move plays its own animation on the equation. Animation speed can be set to 0.5x, 1x or 2x. After a solve the result holds for 3 seconds; click to skip.

## Act 1: The Ink Cellar

| Stage | Example | New cards |
|---|---|---|
| 1. One-step | x + 3 = 7, 4x = 20, x ÷ 3 = 6 | Add, Subtract, Multiply, Divide both sides |
| 2. Two-step | 3x + 4 = 19, x ÷ 2 − 1 = 5 | None: undo + and − before × and ÷ |
| 3. Negatives and fractions | −x = 5, 5 − x = 2, −3x = 12, (2/3)x = 8 | Multiply by −1, Multiply by the reciprocal |

A run is a map of 11 nodes: normal fights, two elites and The Scale Keeper boss.

- **Tutorial fight**: each stage is introduced alone once, with a short explanation and only 3 cards.
- **Normal fights**: about 60% the newest stage, 40% review of earlier stages (skills marked "needs review" come up 3 times as often).
- **Elites** stack the two newest stages in one equation (for example 18 − 4x = −10). Beating one heals 20 HP.
- **Boss**: one phase per unlocked stage (sides swap from phase 2), then a final phase that combines them.

## Mastery and stats

Each stage has a mastery meter from 0 to 100, saved in the browser (`localStorage`) across runs:

- +20 for solving an equation with no wrong moves, +5 for solving it at or under par (par = the fewest moves)
- −10 for each wrong move on that skill
- −5 for each week the skill goes unpracticed, down to 60 once mastered
- 80 = mastered, which unlocks the next stage's tutorial fight. Stages never lock again; a mastered skill that drops below 80 is marked "needs review".

The Skills & stats screen shows, per skill: mastery, fights attempted / solved, wrong moves by card, average moves vs par, average seconds per move, hints used and the date last practiced. It also has a reset button.

All art is stand-in.
