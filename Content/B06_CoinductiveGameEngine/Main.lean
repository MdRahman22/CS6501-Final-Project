import Content.B06_CoinductiveGameEngine.chapters.CS6501_BigBang

open Content.B06_CoinductiveGameEngine.chapters.CS6501_BigBang

def main : IO Unit := do
  IO.println "HtDP-style big-bang demo in Lean 4"
  IO.println "Move @ to G."
  IO.println "Type help for commands."
  runTerminal shipBigBang initialShip
