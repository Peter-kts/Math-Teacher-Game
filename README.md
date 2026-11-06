# Math Teacher Game

A Slay the Spire-style card game where algebra equations are the enemies. This repo currently holds a throwaway proof of concept.

## Running the prototype

No install or build is needed. Open `prototype/index.html` in any modern browser: double-click the file, or drag it into a browser window. It works offline, with a mouse or a touchscreen.

## How it plays

- Each enemy is a level 1 equation: a one-step linear equation such as `x + 3 = 7`, `x − 5 = 2`, `4x = 20` or `x ÷ 3 = 6`, sometimes with x on the right side.
- You get 4 cards, each a legal move like "Subtract 3 from both sides", built from the numbers in the equation. Only one gets x by itself.
- Cards marked ⇔ apply to both sides and can be dropped anywhere on the enemy. Cards marked ◎ change one part and must be dropped on that part of the equation. Level 1 only deals ⇔ cards; ◎ is there for later levels (Distribute, Factor and so on).
- A wrong move costs 10 of your 100 HP. At 0 HP the run ends and shows how many equations you beat.

The enemy art is a stand-in.
