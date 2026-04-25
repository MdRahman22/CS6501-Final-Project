import Content.B06_CoinductiveGameEngine.games.Snake

/-
  Demo driver: simulates a Snake game with a simple greedy AI,
  then outputs every frame as JSON for playback in the D3 viewer.
-/

open Content.B06_CoinductiveGameEngine.games.Snake
open Content.B06_CoinductiveGameEngine.chapters.CS6501_Coinduction

-- Simple greedy AI: steer toward food, avoid reversing
def aiDirection (w : SnakeWorld) : String :=
  match w.body with
  | [] => "right"
  | head :: _ =>
    let hDir := if head.x < w.food.x then "right"
                else if head.x > w.food.x then "left" else ""
    let vDir := if head.y < w.food.y then "down"
                else if head.y > w.food.y then "up" else ""
    let isReverse (s : String) (d : Dir) : Bool :=
      (s == "left" && d == .right) || (s == "right" && d == .left) ||
      (s == "up" && d == .down) || (s == "down" && d == .up)
    if hDir != "" && !isReverse hDir w.dir then hDir
    else if vDir != "" && !isReverse vDir w.dir then vDir
    else if vDir != "" then vDir
    else if hDir != "" then hDir
    else toString w.dir

-- One simulation step: AI chooses direction, then tick
def simStep (w : SnakeWorld) : SnakeWorld :=
  let dir := aiDirection w
  let w' := snakeBigBang.onKey w dir
  snakeBigBang.onTick w'

-- Collect frames for N steps (or until the game ends)
def simulate (w : SnakeWorld) : Nat → List SnakeWorld
  | 0 => [w]
  | n + 1 =>
    if snakeBigBang.stopWhen w then [w]
    else w :: simulate (simStep w) n

-- JSON serialization
def cellJson (c : Cell) : String :=
  "{\"x\":" ++ toString c.x ++ ",\"y\":" ++ toString c.y ++ "}"

def frameJson (w : SnakeWorld) : String :=
  let snakeArr := "[" ++ String.intercalate "," (w.body.map cellJson) ++ "]"
  let aliveStr := if w.alive then "true" else "false"
  "{\"snake\":" ++ snakeArr ++
  ",\"food\":" ++ cellJson w.food ++
  ",\"dir\":\"" ++ toString w.dir ++ "\"" ++
  ",\"score\":" ++ toString w.score ++
  ",\"ticks\":" ++ toString w.ticks ++
  ",\"alive\":" ++ aliveStr ++ "}"

def demoJson (frames : List SnakeWorld) : String :=
  let strs := frames.map frameJson
  "{\"meta\":{" ++
  "\"title\":\"Snake Demo\"," ++
  "\"gridW\":" ++ toString gridW ++ "," ++
  "\"gridH\":" ++ toString gridH ++ "," ++
  "\"frameCount\":" ++ toString frames.length ++
  "},\"frames\":[\n" ++
  String.intercalate ",\n" strs ++
  "\n]}"

def main : IO Unit := do
  let frames := simulate initialSnake 200
  IO.println (demoJson frames)
