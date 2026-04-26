import Content.B06_CoinductiveGameEngine.chapters.CS6501_Coinduction

open Content.B06_CoinductiveGameEngine.chapters.CS6501_Coinduction

namespace Content.B06_CoinductiveGameEngine.games.MissileChase

/-
  Missile Chase v1

  This is a BigBang world model:
  - the target moves automatically on each tick
  - the missile moves one cell toward the target on each tick
  - arrow keys can manually nudge the missile
  - the world stops when the missile catches the target
-/

def gridW : Nat := 24
def gridH : Nat := 15
def maxTicks : Nat := 60

structure Cell where
  x : Nat
  y : Nat
deriving Repr, BEq

structure ChaseWorld where
  target : Cell
  missile : Cell
  ticks : Nat
deriving Repr

def incWrap (limit n : Nat) : Nat :=
  if n + 1 < limit then n + 1 else 0

def decSat (n : Nat) : Nat :=
  if n = 0 then 0 else n - 1

def incSat (limit n : Nat) : Nat :=
  if n + 1 < limit then n + 1 else n

def moveTarget (w : ChaseWorld) : Cell :=
  let newX := incWrap gridW w.target.x
  let newY :=
    if w.ticks % 4 == 0 then
      incWrap gridH w.target.y
    else
      w.target.y
  { x := newX, y := newY }

def towardCoord (a b : Nat) : Nat :=
  if a < b then
    a + 1
  else if b < a then
    a - 1
  else
    a

def moveMissileToward (m t : Cell) : Cell :=
  { x := towardCoord m.x t.x,
    y := towardCoord m.y t.y }

def stepWorld (w : ChaseWorld) : ChaseWorld :=
  let newTarget := moveTarget w
  let newMissile := moveMissileToward w.missile newTarget
  { target := newTarget,
    missile := newMissile,
    ticks := w.ticks + 1 }

def moveByKey (c : Cell) (k : String) : Cell :=
  if k = "left" then
    { c with x := decSat c.x }
  else if k = "right" then
    { c with x := incSat gridW c.x }
  else if k = "up" then
    { c with y := decSat c.y }
  else if k = "down" then
    { c with y := incSat gridH c.y }
  else
    c

def handleKey (w : ChaseWorld) (k : String) : ChaseWorld :=
  { w with missile := moveByKey w.missile k }

def caught (w : ChaseWorld) : Bool :=
  w.missile == w.target

def stopWorld (w : ChaseWorld) : Bool :=
  caught w || decide (w.ticks >= maxTicks)

def charAt (w : ChaseWorld) (x y : Nat) : String :=
  let c : Cell := { x := x, y := y }
  if (c == w.missile) && (c == w.target) then
    "X"
  else if c == w.missile then
    "M"
  else if c == w.target then
    "T"
  else
    "."

def row (w : ChaseWorld) (y : Nat) : String :=
  String.join ((List.range gridW).map (fun x => charAt w x y))

def renderWorld (w : ChaseWorld) : String :=
  let rows := String.join ((List.range gridH).map (fun y => row w y ++ "\n"))
  rows ++
  "tick: " ++ toString w.ticks ++ "\n" ++
  "target:  (" ++ toString w.target.x ++ ", " ++ toString w.target.y ++ ")\n" ++
  "missile: (" ++ toString w.missile.x ++ ", " ++ toString w.missile.y ++ ")\n"

def missileBigBang : BigBang ChaseWorld String :=
  { toDraw := renderWorld,
    onTick := stepWorld,
    onKey := handleKey,
    stopWhen := stopWorld }

def initialChase : ChaseWorld :=
  { target := { x := 18, y := 9 },
    missile := { x := 0, y := 0 },
    ticks := 0 }

def simulate : Nat -> ChaseWorld -> List ChaseWorld
  | 0, w => [w]
  | Nat.succ n, w =>
      if stopWorld w then
        [w]
      else
        w :: simulate n (stepWorld w)

def absDiff (a b : Nat) : Nat :=
  if a < b then b - a else a - b

def gap (w : ChaseWorld) : Nat :=
  absDiff w.missile.x w.target.x + absDiff w.missile.y w.target.y

def jsonCell (name : String) (c : Cell) : String :=
  "\"" ++ name ++ "\":{\"x\":" ++ toString c.x ++ ",\"y\":" ++ toString c.y ++ "}"

def jsonWorld (w : ChaseWorld) : String :=
  "{" ++
  "\"tick\":" ++ toString w.ticks ++ "," ++
  jsonCell "target" w.target ++ "," ++
  jsonCell "missile" w.missile ++ "," ++
  "\"gap\":" ++ toString (gap w) ++ "," ++
  "\"caught\":" ++ (if caught w then "true" else "false") ++
  "}"

def joinWith (sep : String) : List String -> String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ joinWith sep xs

def demoJson : String :=
  "[" ++ joinWith "," ((simulate 40 initialChase).map jsonWorld) ++ "]"

end Content.B06_CoinductiveGameEngine.games.MissileChase