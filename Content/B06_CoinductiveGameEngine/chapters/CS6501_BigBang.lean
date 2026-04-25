import Std
import Content.B05_Geometry.chapters.CS6501_Rational2D

/- @@@
# A Coinductive Game Engine: HtDP Big-Bang in Lean 4

<!-- toc -->

This chapter builds a terminal-based *reactive game engine*
modeled on the *big-bang* framework from the textbook
*How to Design Programs* (HtDP). The key idea is simple:
a running program is a *world* that evolves over time in
response to external events — clock ticks, keystrokes,
and mouse actions.

## The Big Idea: World → Event → World

A big-bang program is defined by a handful of pure functions:

- **toDraw** renders the current world as a scene (here, a String)
- **onTick** advances the world by one clock tick
- **onKey** handles a keystroke
- **onMouse** handles a mouse event
- **stopWhen** decides whether the simulation is finished

The *runtime* is the only impure part: it reads input,
dispatches events, and prints scenes. The world logic
itself is entirely pure and could, in principle, be
verified.

## Induction vs. Coinduction

In the *Inductive Types* chapter we studied `Nat`, `List`,
and `Option`. All three are *inductive*: every value is
built by applying a finite number of constructors, and
every recursive function terminates because each recursive
call receives a structurally *smaller* argument. Lean
accepts such functions without the `partial` keyword
because it can verify, mechanically, that the recursion
bottoms out.

Reactive programs break this contract deliberately. A game
loop does not recurse on a smaller piece of data — it
recurses on the *next world state*, which is just as large
as the current one. There is no base case; the loop runs
until an external condition (user quit, stop predicate)
fires. That condition could, in principle, never fire.

This style of computation is called *coinductive* or
*corecursive*. Where an inductive process is characterized
by how it is *constructed* (bottom-up from a base case),
a coinductive process is characterized by what it *produces
next* (top-down, one observation at a time). The canonical
coinductive structure is an infinite stream: at any moment
you can ask for the *head* (the current value) and the
*tail* (the rest of the stream), but there is no final
element.

A big-bang world is exactly such a stream: at each step
the runtime *observes* the current scene (head), then
steps to the next world (tail). The stream has no
predetermined length; it is potentially infinite.

Because Lean's termination checker cannot prove that a
coinductive loop halts, we mark it `partial`. This is not
a limitation to work around — it is the *honest* signature.
We are telling Lean: "this function may run forever, and
that is by design."

## Mouse Events

We begin with a small enumeration of the mouse events
that the framework recognizes. These correspond to the
standard HtDP mouse event vocabulary.
@@@ -/

namespace Content.B06_CoinductiveGameEngine.chapters.CS6501_BigBang

universe u v

/-- HtDP-style mouse events. -/
inductive MouseEvent where
  | buttonDown
  | buttonUp
  | drag
  | move
  | enter
  | leave
deriving Repr, BEq, Inhabited

/- @@@
## Input Events

Every stimulus the world can receive is wrapped in a
single sum type. The runtime parses user input into one
of these three cases.

`InputEvent` is a perfectly ordinary *inductive* sum type —
the same kind of type as `Option`, `Bool`, or `Expr` from
earlier chapters. Nothing coinductive lives here. The
coinductive part is how the runtime *consumes* an unbounded
sequence of such events over time; the events themselves
are finite, discrete values.

Think of `InputEvent` as the element type of the infinite
stream that the outside world feeds to the game loop.
Each `tick`, `key`, or `mouse` value is one *head* drawn
from that stream.
@@@ -/

/-- External events that can update a world. -/
inductive InputEvent where
  | tick
  | key (k : String)
  | mouse (x y : Nat) (m : MouseEvent)
deriving Repr, BEq, Inhabited

/- @@@
## The BigBang Configuration

The `BigBang` structure bundles all the handlers together.
Only `toDraw` is mandatory — everything else defaults to
a no-op. This lets you start with a minimal world and
add behavior incrementally, exactly as HtDP recommends.

The structure is polymorphic in both the `World` type and
the `Scene` type. For our terminal runtime, `Scene` is
`String`, but one could instantiate it with an HTML or
SVG type for a graphical backend.

From the stream perspective, `BigBang` is the *specification*
of a coinductive process without committing to how it runs:

- `toDraw` is the *observation* function — it extracts the
  visible head of the stream (the current scene) from the
  hidden state (the world).
- `onTick` / `onKey` / `onMouse` are the *transition* functions —
  they produce the next hidden state given the current one
  and one element of the incoming event stream.
- `stopWhen` is the *termination guard* — it decides when
  the otherwise-infinite process is allowed to stop.

In a purely coinductive formulation (no `stopWhen`) the
process would be literally infinite. `stopWhen` is our
escape hatch: it converts the coinductive loop into a
`partial` function that *may* terminate. Every handler is
a pure function; no handler touches `IO`. The impurity is
isolated entirely in the runtime that *drives* the loop.
@@@ -/

/--
A terminal-friendly version of HtDP's big-bang configuration.

`toDraw` is mandatory.
All other handlers default to no-ops.
-/
structure BigBang (World : Type u) (Scene : Type v) where
  toDraw : World → Scene
  onTick : World → World := id
  onKey : World → String → World := fun w _ => w
  onMouse : World → Nat → Nat → MouseEvent → World := fun w _ _ _ => w
  stopWhen : World → Bool := fun _ => false

/- @@@
## Event Dispatch

`handleEvent` is a pure dispatcher: given a world and
one event, it selects the appropriate handler and returns
the new world. No IO here — the impurity lives entirely
in the runtime loop.

This function is exactly the *step* of the coinductive
transition system. If we were writing a formal stream
processor, `handleEvent bb` would be the *unfold* function:
given the current hidden state and one input observation,
produce the next hidden state. The runtime calls it once
per event, threading the resulting world into the next
iteration.

Notice that `handleEvent` is defined by pattern matching on
`InputEvent` — a finite inductive type. The pattern match
is total and obviously terminating: there are exactly three
cases. The coinductive complexity lives one level up, in
`runTerminal`, which calls `handleEvent` an unbounded number
of times. Separating the finite dispatch from the infinite
loop is a clean architectural boundary between inductive
and coinductive reasoning.
@@@ -/

namespace BigBang

variable {World : Type u} {Scene : Type v}

def handleEvent (bb : BigBang World Scene) (w : World) : InputEvent → World
  | .tick => bb.onTick w
  | .key k => bb.onKey w k
  | .mouse x y m => bb.onMouse w x y m

end BigBang

/- @@@
## Terminal Runtime

`runTerminal` is the coinductive heart of the system:

1. **Observe** — render the current world (extract the head)
2. **Guard** — check `stopWhen`; if true, halt
3. **Read** — obtain one event from the environment
4. **Step** — call `handleEvent` to produce the next world
5. **Recur** — loop with the new world as the hidden state

This is precisely the unfold pattern of a stream processor.
Contrast it with a recursive function on `List`:

```
-- Inductive: recurse on a structurally *smaller* list
def sum : List Nat → Nat
  | [] => 0
  | h :: t => h + sum t   -- t is smaller than h :: t ✓
```

```
-- Coinductive: recurse with the *next* world (same size)
partial def runTerminal (bb : BigBang W S) (w : W) : IO Unit := do
  ...
  runTerminal bb w'        -- w' is not smaller than w ✗ for termination
```

Lean's termination checker rejects the second pattern
because `w'` is not structurally smaller than `w`. The
`partial` keyword is our acknowledgement that we are
writing a coinductive process: we assert that the function
is *logically* well-defined (each step is deterministic
and productive) without claiming it terminates.

`Command` is the thin parse layer between raw terminal
input and the `InputEvent` algebra. `help` and `quit` are
meta-commands handled by the runtime itself; only `.step e`
passes through to `handleEvent`.
@@@ -/

inductive Command where
  | step (e : InputEvent)
  | help
  | quit
deriving Repr

def words (s : String) : List String :=
  (s.trimAscii.toString.splitOn " ").filter (fun t => t ≠ "")

def parseMouseEvent? : String → Option MouseEvent
  | "button-down" => some .buttonDown
  | "button-up"   => some .buttonUp
  | "drag"        => some .drag
  | "move"        => some .move
  | "enter"       => some .enter
  | "leave"       => some .leave
  | _             => none

def parseCommand (line : String) : Except String Command :=
  match words line with
  | [] => .error "Empty command. Type `help`."
  | "help" :: [] => .ok .help
  | "quit" :: [] => .ok .quit
  | "tick" :: [] => .ok <| .step .tick
  | "left" :: [] => .ok <| .step (.key "left")
  | "right" :: [] => .ok <| .step (.key "right")
  | "up" :: [] => .ok <| .step (.key "up")
  | "down" :: [] => .ok <| .step (.key "down")
  | "key" :: k :: [] => .ok <| .step (.key k)
  | "mouse" :: xs :: ys :: kind :: [] =>
      match xs.toNat?, ys.toNat?, parseMouseEvent? kind with
      | some x, some y, some m => .ok <| .step (.mouse x y m)
      | _, _, _ =>
          .error "Usage: mouse <x> <y> <button-down|button-up|drag|move|enter|leave>"
  | _ =>
      .error "Unknown command. Type `help`."

def helpText : String :=
  String.intercalate "\n"
    [ "Commands:"
    , "  tick"
    , "  left"
    , "  right"
    , "  up"
    , "  down"
    , "  key <text>"
    , "  mouse <x> <y> <button-down|button-up|drag|move|enter|leave>"
    , "  help"
    , "  quit"
    ]

partial def runTerminal
    {World : Type u}
    (bb : BigBang World String)
    (w : World) : IO Unit := do
  IO.println ""
  IO.println (bb.toDraw w)
  IO.println ""
  if bb.stopWhen w then
    IO.println "Stopped."
  else
    IO.print "> "
    let stdin ← IO.getStdin
    let line ← stdin.getLine
    let line := (line.dropEndWhile Char.isWhitespace).toString
    match parseCommand line with
    | .error msg =>
        IO.println msg
        runTerminal bb w
    | .ok .help =>
        IO.println helpText
        runTerminal bb w
    | .ok .quit =>
        IO.println "Goodbye."
    | .ok (.step e) =>
        let w' := bb.handleEvent w e
        runTerminal bb w'

/- @@@
## Example: Move a Ship to the Goal

To demonstrate the framework, we build a small game.
A ship (`@`) starts at the top-left corner of a grid.
The player must navigate it to the goal (`G`) at the
bottom-right corner before time runs out.

The world state is a `Ship` with an x-coordinate, a
y-coordinate, and a tick counter. The handlers are:

- **onTick**: increment the tick counter
- **onKey**: move the ship in the four cardinal directions
- **onMouse**: teleport the ship to the clicked cell
- **stopWhen**: stop if the ship reaches the goal or time expires

This is a pure, functional game. Every frame is a
deterministic function of the previous frame plus one event.
@@@ -/

def width : Nat := 20
def height : Nat := 8
def maxTicks : Nat := 30

def goalX : Nat := width - 1
def goalY : Nat := height - 1

structure Ship where
  x : Nat
  y : Nat
  ticks : Nat
deriving Repr, Inhabited

def decSat : Nat → Nat
  | 0 => 0
  | n' + 1 => n'

def incSat (limitExclusive n : Nat) : Nat :=
  if n + 1 < limitExclusive then n + 1 else n

def clampCoord (limitExclusive n : Nat) : Nat :=
  Nat.min n (limitExclusive - 1)

/- @@@
### Rendering

The `cell` function determines what character to display
at each grid position. The `boardString` function assembles
the full grid by mapping over rows and columns, then joins
them with newlines. The `statusString` adds context below
the board.
@@@ -/

def cell (w : Ship) (x y : Nat) : String :=
  if x = w.x ∧ y = w.y then
    "@"
  else if x = goalX ∧ y = goalY then
    "G"
  else
    "."

def rowString (w : Ship) (y : Nat) : String :=
  String.join ((List.range width).map (fun x => cell w x y))

def boardString (w : Ship) : String :=
  String.intercalate "\n" ((List.range height).map (rowString w))

def statusString (w : Ship) : String :=
  if w.x = goalX ∧ w.y = goalY then
    s!"You reached the goal in {w.ticks} ticks."
  else if w.ticks ≥ maxTicks then
    s!"Out of time at tick {w.ticks}."
  else
    s!"ticks: {w.ticks}/{maxTicks}    ship: ({w.x}, {w.y})    goal: ({goalX}, {goalY})"

def shipScene (w : Ship) : String :=
  boardString w ++ "\n" ++ statusString w

/- @@@
### The BigBang Instance

Here we wire everything together into a `BigBang` value.
Every handler is a pure function — no IO anywhere.

Reading through the fields as a coinductive specification:

- `toDraw` is the *observation*: it maps the hidden `Ship`
  state to a visible `String` scene. The runtime calls this
  once per step to produce the stream's next head value.
- `onTick` is the *autonomous step*: it advances the world
  when the clock fires, independent of player input.
- `onKey` is the *interactive step*: it moves the ship in
  response to arrow key events drawn from the input stream.
- `onMouse` is a second interactive step: it teleports the
  ship to the clicked grid cell.
- `stopWhen` is the *termination guard*: the coinductive
  loop is allowed to stop when either the player wins or
  time runs out. The `decide` tactic converts a decidable
  `Prop` into a `Bool`; this works because `=` and `≤` on
  `Nat` are decidable.

None of these functions is recursive. They are simple,
total, one-step transformations — the building blocks
that `runTerminal` assembles into the infinite (or
eventually-stopping) reactive loop.
@@@ -/

def shipBigBang : BigBang Ship String :=
  { toDraw := shipScene

    onTick := fun w =>
      { w with ticks := w.ticks + 1 }

    onKey := fun w k =>
      if k = "left" then
        { w with x := decSat w.x }
      else if k = "right" then
        { w with x := incSat width w.x }
      else if k = "up" then
        { w with y := decSat w.y }
      else if k = "down" then
        { w with y := incSat height w.y }
      else
        w

    onMouse := fun w x y _ =>
      { w with
          x := clampCoord width x
          y := clampCoord height y }

    stopWhen := fun w =>
      decide (w.ticks ≥ maxTicks ∨ (w.x = goalX ∧ w.y = goalY))
  }

def initialShip : Ship :=
  { x := 0, y := 0, ticks := 0 }

/- @@@
### Main

The `main` function prints a welcome message and launches
the terminal runtime. This is the only place IO appears
in the entire game — everything else is pure computation.
@@@ -/

def main : IO Unit := do
  IO.println "HtDP-style big-bang demo in Lean 4"
  IO.println "Move @ to G."
  IO.println "Type `help` for commands."
  runTerminal shipBigBang initialShip

/- @@@
## Example: Intercept — Affine Geometry in Motion

The ship game above uses natural-number coordinates on
a discrete grid. Now we build a second game that uses the
*rational affine algebra* developed in the Geometry unit.

### The Setup

A **target** point moves along a line segment from A to B
via affine interpolation: at tick k its position is
`affineInterp2d A B (k/maxTicks)`. The target slides
steadily and predictably — no randomness.

The **probe** is a point the player controls. Arrow keys
translate the probe by rational displacement vectors
applied with the torsor operation `v +ᵥ p`. Each keypress
adds a unit displacement: `re1` (right), `-re1` (left),
`re2` (down), `-re2` (up).

### Winning and Losing

The game computes the displacement `probe -ᵥ target` at
every frame. If its components are both small — within a
capture radius — the player wins. If time runs out first,
the player loses. The stop condition is a pure function
of the world state, and all coordinate arithmetic is
exact rational computation.

### Why This Matters

This game exercises every layer of the affine stack:

- `RPoint2` for positions (probe and target)
- `RVec2` for displacements (movements and the gap)
- `+ᵥ` (torsor action) to move the probe
- `-ᵥ` (torsor subtraction) to measure the gap
- `•` (scalar multiplication) inside `affineInterp2d`
- `affineInterp2d` for the target's parametric path

No coordinates are ever converted to floating point.
The terminal rendering quantizes to a character grid for
display, but the underlying world state lives in exact
rational affine space.
@@@ -/

section Intercept

open Content.B05_Geometry.chapters.rationalVectorSpace

/- @@@
### World State

The `Interceptor` structure tracks the probe position,
the current tick, and the two endpoints of the target's
path. The target's position is not stored — it is
*computed* from the tick count via `affineInterp2d`.
This is a key design choice: derived state is never
stored, only computed, so the world is always consistent.
@@@ -/

def iWidth : Nat := 30
def iHeight : Nat := 15
def iMaxTicks : Nat := 40
def captureRadius : Rat := 3/2

structure Interceptor where
  probe : RPoint2
  pathStart : RPoint2
  pathEnd : RPoint2
  ticks : Nat
deriving Repr

instance : Inhabited Interceptor where
  default := { probe := ⟨0, 0⟩, pathStart := ⟨0, 0⟩, pathEnd := ⟨0, 0⟩, ticks := 0 }

/- @@@
### Target Position

The target's position at tick k is the affine interpolation
`affineInterp2d pathStart pathEnd (k / maxTicks)`. At tick 0
the target is at `pathStart`; at the final tick it reaches
`pathEnd`. Every intermediate position is an exact rational
point on the segment.
@@@ -/

def targetPos (w : Interceptor) : RPoint2 :=
  affineInterp2d w.pathStart w.pathEnd ((w.ticks : Rat) / (iMaxTicks : Rat))

/- @@@
### Movement

Arrow keys translate the probe by a unit displacement
vector. This is the torsor operation `v +ᵥ p` — pure
affine geometry.
@@@ -/

def moveProbe (w : Interceptor) (dir : String) : Interceptor :=
  let step : RVec2 :=
    if dir = "right" then re1
    else if dir = "left" then -re1
    else if dir = "down" then re2
    else if dir = "up" then -re2
    else ⟨0, 0⟩
  { w with probe := step +ᵥ w.probe }

/- @@@
### Capture Test

The player captures the target when the displacement
between probe and target is small in both components.
We use the absolute value of each component of the
vector `probe -ᵥ target` and compare against the
capture radius. Everything is exact rational arithmetic.
@@@ -/

def absRat (r : Rat) : Rat :=
  if r < 0 then -r else r

def captured (w : Interceptor) : Bool :=
  let gap : RVec2 := w.probe -ᵥ targetPos w
  decide (absRat gap.x ≤ captureRadius ∧ absRat gap.y ≤ captureRadius)

def timeUp (w : Interceptor) : Bool :=
  decide (w.ticks ≥ iMaxTicks)

/- @@@
### Rendering

We quantize the rational positions to a character grid
for terminal display. The probe appears as `P`, the
target as `T`, and overlap as `*`. The status line shows
exact rational coordinates so the player can see the
true affine state beneath the coarse grid.
@@@ -/

def quantize (limitExclusive : Nat) (r : Rat) : Nat :=
  let n := r.floor.toNat
  if n < limitExclusive then n else limitExclusive - 1

def iCell (probeCol probeRow targetCol targetRow : Nat) (x y : Nat) : String :=
  let isProbe := x = probeCol ∧ y = probeRow
  let isTarget := x = targetCol ∧ y = targetRow
  if isProbe ∧ isTarget then "*"
  else if isProbe then "P"
  else if isTarget then "T"
  else "·"

def iRowString (probeCol probeRow targetCol targetRow : Nat) (y : Nat) : String :=
  String.join ((List.range iWidth).map (fun x =>
    iCell probeCol probeRow targetCol targetRow x y))

def iBoardString (w : Interceptor) : String :=
  let target := targetPos w
  let pc := quantize iWidth w.probe.x
  let pr := quantize iHeight w.probe.y
  let tc := quantize iWidth target.x
  let tr := quantize iHeight target.y
  String.intercalate "\n" ((List.range iHeight).map
    (iRowString pc pr tc tr))

def ratStr (r : Rat) : String :=
  if r.den = 1 then toString r.num
  else toString r.num ++ "/" ++ toString r.den

def iStatusString (w : Interceptor) : String :=
  let target := targetPos w
  let gap : RVec2 := w.probe -ᵥ target
  if captured w then
    s!"CAPTURED at tick {w.ticks}! Gap: ({ratStr gap.x}, {ratStr gap.y})"
  else if timeUp w then
    s!"TIME UP at tick {w.ticks}. Gap: ({ratStr gap.x}, {ratStr gap.y})"
  else
    s!"tick {w.ticks}/{iMaxTicks}  " ++
    s!"probe: ({ratStr w.probe.x}, {ratStr w.probe.y})  " ++
    s!"target: ({ratStr target.x}, {ratStr target.y})  " ++
    s!"gap: ({ratStr gap.x}, {ratStr gap.y})"

def iScene (w : Interceptor) : String :=
  iBoardString w ++ "\n" ++ iStatusString w

/- @@@
### The BigBang Instance

The `onTick` handler simply increments the tick counter —
a minimal state update. But because `targetPos` *derives*
the target's location from the tick count via
`affineInterp2d`, the target moves automatically every
time `runTerminal` calls `onTick`. The target is never
stored; it is *computed on demand from the hidden state*.

This is the coinductive design principle in action:
**store the minimal hidden state; derive all observations**.
The stream of target positions is an infinite sequence
`(targetPos w₀), (targetPos w₁), ...` produced by the
`toDraw` observation function applied to successive worlds.
We never explicitly build that sequence — the runtime
materializes one term at a time by calling `iScene`.

Contrast this with an inductive approach where you might
precompute the full list of target positions:

```
-- Inductive: finite list, built all at once
def targetPath : List RPoint2 :=
  (List.range iMaxTicks).map (fun k =>
    affineInterp2d pathStart pathEnd ((k : Rat) / iMaxTicks))
```

That list has a fixed, finite length. The coinductive
version has no predetermined length — the target just
keeps moving until `stopWhen` fires.
@@@ -/

def interceptBigBang : BigBang Interceptor String :=
  { toDraw := iScene

    onTick := fun w =>
      { w with ticks := w.ticks + 1 }

    onKey := fun w k => moveProbe w k

    stopWhen := fun w => captured w || timeUp w
  }

/- @@@
### Initial State

The target travels diagonally from the top-left area
to the bottom-right area. The probe starts near the
center of the grid. The player must intercept the
target as it slides along its affine path.
@@@ -/

def initialInterceptor : Interceptor :=
  { probe := ⟨15, 7⟩
    pathStart := ⟨2, 2⟩
    pathEnd := ⟨27, 13⟩
    ticks := 0 }

end Intercept

end Content.B06_CoinductiveGameEngine.chapters.CS6501_BigBang
