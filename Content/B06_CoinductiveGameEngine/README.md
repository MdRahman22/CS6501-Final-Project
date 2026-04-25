# B06 — Coinductive Game Engine

Two terminal games built on an HtDP-style big-bang framework.

## Build and run

From the repo root:

```
lake build bigbang
lake exe bigbang
```

This launches the **Ship** game. Navigate `@` to `G` before tick 30.

## Commands

At the `>` prompt:

| Command | Effect |
|---------|--------|
| `left` / `right` / `up` / `down` | Move the ship one cell |
| `tick` | Advance one clock tick |
| `key <text>` | Send an arbitrary key string |
| `mouse <x> <y> <event>` | Send a mouse event (`button-down`, `button-up`, `drag`, `move`, `enter`, `leave`) |
| `help` | Print this list |
| `quit` | Exit |

## Switching to the Intercept game

Edit `Main.lean` and replace:

```lean
runTerminal shipBigBang initialShip
```

with:

```lean
runTerminal interceptBigBang initialInterceptor
```

Then rebuild and run. In Intercept, move `P` (probe) to intercept `T`
(target) within a capture radius before tick 40. The target slides along
a straight affine path; all coordinates are exact rationals.
