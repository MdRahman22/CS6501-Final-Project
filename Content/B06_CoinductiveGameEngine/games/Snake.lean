import Content.B06_CoinductiveGameEngine.chapters.CS6501_Coinduction

/-
  Snake — a coinductive game built on the BigBang framework.

  The game loop is genuinely coinductive: each tick produces the
  next world state, and the process runs until the snake dies.
  All game logic is pure; IO is isolated in the BigBang runtime.
-/

open Content.B06_CoinductiveGameEngine.chapters.CS6501_Coinduction

namespace Content.B06_CoinductiveGameEngine.games.Snake

-- Grid dimensions
def gridW : Nat := 20
def gridH : Nat := 15

-- Direction the snake is traveling
inductive Dir where
  | up | down | left | right
deriving Repr, BEq, Inhabited

instance : ToString Dir where
  toString
    | .up => "up" | .down => "down" | .left => "left" | .right => "right"

def Dir.opposite : Dir → Dir
  | .up => .down | .down => .up | .left => .right | .right => .left

-- A cell on the grid
structure Cell where
  x : Nat
  y : Nat
deriving Repr, BEq, Inhabited

-- Linear congruential PRNG (same constants as glibc)
def nextSeed (s : Nat) : Nat :=
  (s * 1103515245 + 12345) % (2 ^ 31)

-- Place food at a position not occupied by the snake.
-- Uses bounded retries to guarantee termination.
def spawnFood (snake : List Cell) (seed : Nat) (fuel : Nat := 100) : Cell × Nat :=
  match fuel with
  | 0 => (⟨0, 0⟩, seed)
  | n + 1 =>
    let s1 := nextSeed seed
    let s2 := nextSeed s1
    let candidate : Cell := ⟨s1 % gridW, s2 % gridH⟩
    if snake.any (· == candidate) then spawnFood snake s2 n
    else (candidate, s2)

-- World state: everything the game loop needs
structure SnakeWorld where
  body : List Cell     -- head is first element
  dir : Dir
  food : Cell
  score : Nat
  ticks : Nat
  alive : Bool
  seed : Nat           -- PRNG state
deriving Repr, Inhabited

-- Advance the head one cell; none = wall collision
def moveHead (head : Cell) (d : Dir) : Option Cell :=
  match d with
  | .up    => if head.y > 0 then some ⟨head.x, head.y - 1⟩ else none
  | .down  => if head.y + 1 < gridH then some ⟨head.x, head.y + 1⟩ else none
  | .left  => if head.x > 0 then some ⟨head.x - 1, head.y⟩ else none
  | .right => if head.x + 1 < gridW then some ⟨head.x + 1, head.y⟩ else none

-- One tick of the game: move snake, check collisions, maybe eat food
def stepWorld (w : SnakeWorld) : SnakeWorld :=
  if !w.alive then w
  else match w.body with
  | [] => { w with alive := false }
  | head :: _ =>
    match moveHead head w.dir with
    | none =>
        -- Wall collision
        { w with alive := false, ticks := w.ticks + 1 }
    | some h =>
      if w.body.any (· == h) then
        -- Self collision
        { w with alive := false, ticks := w.ticks + 1 }
      else if h == w.food then
        -- Eat food: grow (keep tail), spawn new food
        let newBody := h :: w.body
        let (newFood, newSeed) := spawnFood newBody w.seed
        { w with body := newBody, food := newFood,
                 score := w.score + 1, ticks := w.ticks + 1, seed := newSeed }
      else
        -- Normal move: advance head, drop tail
        { w with body := h :: w.body.dropLast, ticks := w.ticks + 1 }

-- Handle arrow key input (no reversals allowed)
def handleKey (w : SnakeWorld) (k : String) : SnakeWorld :=
  let newDir := match k with
    | "up" => some Dir.up
    | "down" => some Dir.down
    | "left" => some Dir.left
    | "right" => some Dir.right
    | _ => none
  match newDir with
  | none => w
  | some d => if d == w.dir.opposite then w else { w with dir := d }

-- Terminal rendering
def renderWorld (w : SnakeWorld) : String :=
  let border := String.join ((List.range gridW).map fun _ => "-")
  let rows := (List.range gridH).map fun y =>
    let cells := (List.range gridW).map fun x =>
      let pos : Cell := ⟨x, y⟩
      let isHead := match w.body with
        | hd :: _ => hd == pos
        | [] => false
      if isHead then "#"
      else if w.body.any (· == pos) then "o"
      else if pos == w.food then "*"
      else "."
    "|" ++ String.join cells ++ "|"
  let board := String.intercalate "\n"
    (["+" ++ border ++ "+"] ++ rows ++ ["+" ++ border ++ "+"])
  let status := if w.alive then
    s!"Score: {w.score}  Ticks: {w.ticks}  Dir: {toString w.dir}"
  else
    s!"GAME OVER! Score: {w.score} in {w.ticks} ticks"
  board ++ "\n" ++ status

-- BigBang instance: wires pure handlers into the coinductive framework
def snakeBigBang : BigBang SnakeWorld String :=
  { toDraw := renderWorld
    onTick := stepWorld
    onKey := handleKey
    stopWhen := fun w => !w.alive
  }

-- Initial world state
def initialSnake : SnakeWorld :=
  let body := [⟨12, 7⟩, ⟨11, 7⟩, ⟨10, 7⟩]
  let (food, seed) := spawnFood body 42
  { body, dir := .right, food, score := 0, ticks := 0, alive := true, seed }

end Content.B06_CoinductiveGameEngine.games.Snake
