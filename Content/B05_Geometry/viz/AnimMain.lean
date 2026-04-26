import Content.B05_Geometry.chapters.CS6501_Rational2D

open Content.B05_Geometry.chapters.rationalVectorSpace

/-- Simple physics-style state: positions and velocities. -/
structure SimState where
  targetPos  : RPoint2
  targetVel  : RVec2
  missilePos : RPoint2
  missileVel : RVec2

/-- Add two rational 2D vectors. -/
def vecAdd : RVec2 → RVec2 → RVec2
  | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩

/-- Scale a rational 2D vector by a rational number. -/
def vecScale (k : Rat) : RVec2 → RVec2
  | ⟨x, y⟩ => ⟨k * x, k * y⟩

/-- Connect consecutive points with segments. -/
def pathSegments (lbl : String) : List RPoint2 → List String
  | p1 :: p2 :: ps =>
      segmentToJson lbl p1 p2 :: pathSegments lbl (p2 :: ps)
  | _ => []

/-- One physics-style update step.
    The target keeps constant velocity.
    The missile keeps some of its old velocity and also steers toward the target. -/
def nextState (steer : Rat) (s : SimState) : SimState :=
  let targetPos' : RPoint2 := s.targetVel +ᵥ s.targetPos

  let toTarget : RVec2 := s.targetPos -ᵥ s.missilePos

  let keepFactor : Rat := 3 / 4
  let keepPart : RVec2 := vecScale keepFactor s.missileVel
  let steerPart : RVec2 := vecScale steer toTarget

  let missileVel' : RVec2 := vecAdd keepPart steerPart
  let missilePos' : RPoint2 := missileVel' +ᵥ s.missilePos

  {
    targetPos := targetPos'
    targetVel := s.targetVel
    missilePos := missilePos'
    missileVel := missileVel'
  }

/-- Finite simulation: returns the first n+1 states, including the initial one. -/
def simulate : Nat → Rat → SimState → List SimState
  | 0, _, s => [s]
  | Nat.succ n, steer, s =>
      s :: simulate n steer (nextState steer s)

/-- Infinite-time viewpoint:
    the state at time n. -/
def stateAt (steer : Rat) (initState : SimState) : Nat → SimState
  | 0 => initState
  | Nat.succ n => stateAt steer (nextState steer initState) n

/-- First n+1 states taken from the infinite-time model. -/
def prefixStates : Nat → Rat → SimState → List SimState
  | 0, steer, initState =>
      [stateAt steer initState 0]
  | Nat.succ n, steer, initState =>
      stateAt steer initState 0 :: prefixStates n steer (nextState steer initState)

/-- First real correctness theorem:
    the finite simulator and the finite prefix of the infinite-time model agree. -/
theorem prefixStates_eq_simulate
    (n : Nat) (steer : Rat) (initState : SimState) :
    prefixStates n steer initState = simulate n steer initState := by
  induction n generalizing initState with
  | zero =>
      rfl
  | succ n ih =>
      simp [prefixStates, simulate, stateAt, ih]

/-- Build one frame from the current state and the paths so far. -/
def frameScene
  (startState currentState : SimState)
  (targetSoFar missileSoFar : List RPoint2) : String :=

  let items : List String := [
    pointToJson "TargetStart" startState.targetPos,
    pointToJson "MissileStart" startState.missilePos,
    pointToJson "Target" currentState.targetPos,
    pointToJson "Missile" currentState.missilePos,
    vectorToJson "target velocity" currentState.targetPos currentState.targetVel,
    vectorToJson "missile velocity" currentState.missilePos currentState.missileVel,
    segmentToJson "gap" currentState.missilePos currentState.targetPos
  ]
  ++ pathSegments "target path" targetSoFar
  ++ pathSegments "missile path" missileSoFar

  toJsonArray items

/-- Turn simulation states into animation frames. -/
def makeFrames (states : List SimState) : List String :=
  match states with
  | [] => []
  | startState :: _ =>
      let targetPts : List RPoint2 := states.map SimState.targetPos
      let missilePts : List RPoint2 := states.map SimState.missilePos

      let rec go (i : Nat) (ss : List SimState) : List String :=
        match ss with
        | [] => []
        | s :: ss' =>
            let targetSoFar := targetPts.take (i + 1)
            let missileSoFar := missilePts.take (i + 1)
            frameScene startState s targetSoFar missileSoFar :: go (i + 1) ss'

      go 0 states


/-
  Time-indexed motion functions

  These definitions make the professor's suggestion explicit:
  instead of only storing a finite list of frames, we can treat
  position and velocity as functions of time.

  Since this simulation uses discrete time steps, the derivative-like
  idea is a finite difference:
    velocity at time t = position at time t+1 - position at time t
-/

/-- Target position as a function of time. -/
def targetPositionAt (steer : Rat) (initState : SimState) (t : Nat) : RPoint2 :=
  (stateAt steer initState t).targetPos

/-- Missile position as a function of time. -/
def missilePositionAt (steer : Rat) (initState : SimState) (t : Nat) : RPoint2 :=
  (stateAt steer initState t).missilePos

/-- Target stored velocity as a function of time. -/
def targetVelocityAt (steer : Rat) (initState : SimState) (t : Nat) : RVec2 :=
  (stateAt steer initState t).targetVel

/-- Missile stored velocity as a function of time. -/
def missileVelocityAt (steer : Rat) (initState : SimState) (t : Nat) : RVec2 :=
  (stateAt steer initState t).missileVel

/-- Discrete derivative of a point-valued function. -/
def discreteVelocity (pos : Nat -> RPoint2) (t : Nat) : RVec2 :=
  pos (t + 1) -ᵥ pos t

/-- Target velocity computed from consecutive target positions. -/
def targetDiscreteVelocityAt (steer : Rat) (initState : SimState) (t : Nat) : RVec2 :=
  discreteVelocity (targetPositionAt steer initState) t

/-- Missile velocity computed from consecutive missile positions. -/
def missileDiscreteVelocityAt (steer : Rat) (initState : SimState) (t : Nat) : RVec2 :=
  discreteVelocity (missilePositionAt steer initState) t


/-
  Discrete acceleration functions

  Acceleration is the finite difference of velocity:
    acceleration at time t = velocity at time t+1 - velocity at time t

  This is the discrete-time version of the professor's derivative idea.
-/

/-- Discrete derivative of a vector-valued function. -/
def discreteAcceleration (vel : Nat -> RVec2) (t : Nat) : RVec2 :=
  vecAdd (vel (t + 1)) (vecScale (-1) (vel t))

/-- Target acceleration computed from target velocity over time. -/
def targetAccelerationAt (steer : Rat) (initState : SimState) (t : Nat) : RVec2 :=
  discreteAcceleration (targetVelocityAt steer initState) t

/-- Missile acceleration computed from missile velocity over time. -/
def missileAccelerationAt (steer : Rat) (initState : SimState) (t : Nat) : RVec2 :=
  discreteAcceleration (missileVelocityAt steer initState) t


/-
  Small checkable example values.

  These are not theorems. They are quick Lean evaluations I can use
  while presenting to show that the time-indexed functions actually compute.
-/

def demoInitState : SimState := {
  targetPos  := ?12, 8?
  targetVel  := ?1, 1 / 2?
  missilePos := ?0, 0?
  missileVel := ?1, 3 / 4?
}

def demoSteer : Rat := 1 / 25

#eval targetPositionAt demoSteer demoInitState 0
#eval targetPositionAt demoSteer demoInitState 3
#eval missilePositionAt demoSteer demoInitState 3
#eval targetVelocityAt demoSteer demoInitState 3
#eval missileVelocityAt demoSteer demoInitState 3
#eval targetAccelerationAt demoSteer demoInitState 3
#eval missileAccelerationAt demoSteer demoInitState 3
#eval (simulate 10 demoSteer demoInitState).length
#eval (prefixStates 10 demoSteer demoInitState).length


/-
  Small proof facts about the motion model.

  These are useful presentation theorems:
  they show that the target's velocity is constant in the model.
-/

/-- One update step preserves the target velocity. -/
theorem nextState_preserves_targetVel
    (steer : Rat) (s : SimState) :
    (nextState steer s).targetVel = s.targetVel := by
  simp [nextState]

/-- The target velocity as a function of time is constant. -/
theorem targetVelocityAt_constant
    (steer : Rat) (initState : SimState) (t : Nat) :
    targetVelocityAt steer initState t = initState.targetVel := by
  induction t generalizing initState with
  | zero =>
      rfl
  | succ n ih =>
      unfold targetVelocityAt stateAt
      change (stateAt steer (nextState steer initState) n).targetVel = initState.targetVel
      have h := ih (nextState steer initState)
      unfold targetVelocityAt at h
      rw [h]
      exact nextState_preserves_targetVel steer initState

/-- Full animated missile/target pursuit with velocity in the state,
    rendered from the first part of an infinite-time model. -/
def anim : String :=
  let initState : SimState := {
    targetPos  := ⟨12, 8⟩
    targetVel  := ⟨1, 1 / 2⟩
    missilePos := ⟨0, 0⟩
    missileVel := ⟨1, 3 / 4⟩
  }

  let steps : Nat := 10
  let steer : Rat := 1 / 25

  let states : List SimState := prefixStates steps steer initState
  let frames : List String := makeFrames states

  toJsonArray frames

theorem simulate_length
    (n : Nat) (steer : Rat) (initState : SimState) :
    (simulate n steer initState).length = n + 1 := by
  induction n generalizing initState with
  | zero =>
      rfl
  | succ n ih =>
      simp [simulate, ih]

theorem prefixStates_length
    (n : Nat) (steer : Rat) (initState : SimState) :
    (prefixStates n steer initState).length = n + 1 := by
  rw [prefixStates_eq_simulate]
  exact simulate_length n steer initState

def main : IO Unit := do
  IO.println anim
