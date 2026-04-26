# CS6501 Final Project Explanation Notes

Project name:
Missile and Target Trajectories as Affine Motion

## Core idea

This project models a moving target and a pursuing missile in 2D affine space using Lean 4.

The important distinction is:

- positions are points
- velocities and displacements are vectors

This matches affine geometry because it makes sense to add a vector to a point, but it does not make sense to add two positions as if they were ordinary numbers.

## Main state type

`SimState` stores one moment of the simulation:

- `targetPos : RPoint2`
- `targetVel : RVec2`
- `missilePos : RPoint2`
- `missileVel : RVec2`

What to say:

"SimState is one snapshot of the world. It stores where the target and missile are, and how they are moving."

## Main transition function

`nextState` computes the next simulation state.

What it does:

- moves the target by its velocity
- computes the vector from the missile to the target
- keeps part of the missile's old velocity
- adds a steering vector toward the target
- moves the missile by the new missile velocity

What to say:

"`nextState` is the pure update rule. Given the current state, it returns the next state. No IO happens here."

## Finite simulation

`simulate n steer initState`

What it does:

Builds a finite list of states, including the initial state.

What to say:

"`simulate` gives the list of states I can render as animation frames."

## Infinite-time model

`stateAt steer initState t`

What it does:

Gives the state at time step `t`.

What to say:

"This is the time-indexed view. Instead of only storing a finite list, I model the simulation as a function from natural-number time steps to states."

## Finite prefix of infinite model

`prefixStates n steer initState`

What it does:

Takes the first `n + 1` states from the infinite-time model.

What to say:

"The browser cannot render an infinite process, so I render a finite prefix."

## Main correctness theorem

`prefixStates_eq_simulate`

Proposition:

`prefixStates n steer initState = simulate n steer initState`

What it proves:

The finite prefix taken from the infinite-time model agrees with the direct finite simulator.

What to say:

"This proves that my animation frames are not ad hoc. They are a finite view of the same underlying time-indexed process."

## Length theorem 1

`simulate_length`

Proposition:

`(simulate n steer initState).length = n + 1`

What it proves:

The finite simulator produces exactly the initial state plus `n` transitions.

What to say:

"If I simulate `n` steps, I get `n + 1` states because the initial state is included."

## Length theorem 2

`prefixStates_length`

Proposition:

`(prefixStates n steer initState).length = n + 1`

What it proves:

The finite prefix of the infinite-time model also has the expected size.

What to say:

"This follows by rewriting the prefix model into the finite simulator, then using `simulate_length`."

## Position as a function of time

Added definitions:

- `targetPositionAt`
- `missilePositionAt`

What to say:

"These make position explicitly a function of time, which is what the professor suggested."

## Velocity as a function of time

Added definitions:

- `targetVelocityAt`
- `missileVelocityAt`
- `discreteVelocity`
- `targetDiscreteVelocityAt`
- `missileDiscreteVelocityAt`

What to say:

"Because the simulation is discrete, I use finite differences. Velocity is computed as position at time `t + 1` minus position at time `t`."

## Acceleration as a function of time

Added definitions:

- `discreteAcceleration`
- `targetAccelerationAt`
- `missileAccelerationAt`

What to say:

"Acceleration is the finite difference of velocity. This is the discrete-time version of a derivative."

## BigBang extension

Files:

- `Content/B06_CoinductiveGameEngine/games/MissileChase.lean`
- `Content/B06_CoinductiveGameEngine/viz/MissileChaseMain.lean`
- `Content/B06_CoinductiveGameEngine/viz/missile.html`
- `Content/B06_CoinductiveGameEngine/viz/missile-demo.json`

What to say:

"I also built a BigBang-style version where the world evolves through tick events. This connects the missile chase to the coinductive game framework."

## Demo order

1. Show `AnimMain.lean`.
2. Show `SimState`.
3. Show `nextState`.
4. Show `stateAt` and `prefixStates`.
5. Show the three theorems.
6. Show the time-indexed position, velocity, and acceleration definitions.
7. Run the missile animation.
8. Show the BigBang MissileChase extension.

## Commands

From project root:

`lake env lean Content/B05_Geometry/viz/AnimMain.lean`

`lake env lean --run Content/B05_Geometry/viz/AnimMain.lean | Set-Content -Encoding utf8 Content/B05_Geometry/viz/anim.json`

`cd Content/B05_Geometry/viz`

`python -m http.server 8000`

Open:

`http://localhost:8000/animated.html`

For BigBang MissileChase:

`cd "C:\Software Logic\CS6501-Final-Project"`

`lake build Content.B06_CoinductiveGameEngine.games.MissileChase`

`lake env lean --run Content/B06_CoinductiveGameEngine/viz/MissileChaseMain.lean | Set-Content -Encoding utf8 Content/B06_CoinductiveGameEngine/viz/missile-demo.json`

`cd Content/B06_CoinductiveGameEngine/viz`

`python -m http.server 8002`

Open:

`http://localhost:8002/missile.html`
