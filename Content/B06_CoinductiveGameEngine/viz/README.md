# Snake — Coinductive BigBang Game

An interactive Snake game built on the BigBang coinductive framework.
The game exists in two forms: a terminal version (Lean) and a
graphical version (D3.js in the browser). Both implement the same
BigBang pattern: pure `toDraw / onTick / onKey / stopWhen` handlers
driven by a coinductive game loop.

## Quick Start (graphical)

From the repo root:

```
lake build snakeviz
.lake/build/bin/snakeviz > Content/B06_CoinductiveGameEngine/viz/demo.json
```

Then serve it locally and open in a browser:

```
cd Content/B06_CoinductiveGameEngine/viz
python3 -m http.server 8000
```

Visit [http://localhost:8000/snake.html](http://localhost:8000/snake.html).

- **Start Game** — play interactively with arrow keys
- **Watch Demo** — replay the Lean-computed AI simulation

(A local server is needed so the browser can load `demo.json`.
Opening the HTML file directly will work for interactive play
but the demo button will be disabled.)

## Quick Start (terminal)

Edit `Content/B06_CoinductiveGameEngine/Main.lean` to:

```lean
import Content.B06_CoinductiveGameEngine.games.Snake
open Content.B06_CoinductiveGameEngine.games.Snake
open Content.B06_CoinductiveGameEngine.chapters.CS6501_Coinduction

def main : IO Unit := do
  IO.println "Snake — BigBang coinductive game"
  IO.println "Type `help` for commands."
  runTerminal snakeBigBang initialSnake
```Select an answer and submit. For keyboard navigation, use the up/down arrow keys to select an answer.

a
Natural

b
Cursed

c
MaleficSelect an answer and submit. For keyboard navigation, use the up/down arrow keys to select an answer.

a
Natural

b
Cursed

c
Malefic

Then:

```
lake build bigbang
lake exe bigbang
```

At the `>` prompt, type `left`, `right`, `up`, `down` to steer
and `tick` to advance one step. Type `quit` to exit.

## How to Play

- **Arrow keys** (browser) or direction commands (terminal) steer the snake
- **Eat food** (`*` / red dot) to grow and score points
- **Don't hit walls or yourself** — that ends the game
- The game loop runs until `stopWhen` fires (snake dies)

## Architecture

The game demonstrates the coinductive BigBang pattern:

| Component | Lean (Snake.lean) | JavaScript (snake.html) |
|-----------|-------------------|------------------------|
| World state | `structure SnakeWorld` | JS object `{body, dir, food, ...}` |
| Observe | `toDraw := renderWorld` | `toDraw: render` |
| Step | `onTick := stepWorld` | `onTick: stepWorld` |
| Input | `onKey := handleKey` | `onKey: handleKey` |
| Guard | `stopWhen := fun w => !w.alive` | `stopWhen: w => !w.alive` |
| Loop | `partial def runTerminal` | `setTimeout(gameLoop, speed)` |

Both loops are coinductive: they have no predetermined length and
run until the termination guard fires. The Lean version marks this
honestly with `partial`; the JavaScript version uses `setTimeout`
for the same unbounded recursion.

## Files

| File | Purpose |
|------|---------|
| `../games/Snake.lean` | Game logic + BigBang instance (Lean) |
| `SnakeMain.lean` | AI demo simulation, JSON export |
| `snake.html` | D3.js interactive graphical game |
| `demo.json` | Pre-computed AI demo (generated) |

## Regenerating the Demo

```
lake build snakeviz
.lake/build/bin/snakeviz > Content/B06_CoinductiveGameEngine/viz/demo.json
```

The demo runs a greedy AI for 200 ticks. The AI steers toward
the food, avoiding direction reversals. All game logic is computed
in Lean using exact natural-number arithmetic.
