import Std

/- @@@
# Coinduction and Potentially Infinite Processes

<!-- toc -->

In the *Inductive Types* chapter we studied `Nat`, `List`,
and `Option`. All three are *inductive*: every value is
built by applying a finite number of constructors, and
every recursive function terminates because each recursive
call receives a structurally *smaller* argument. Lean
accepts such functions without the `partial` keyword
because it can verify, mechanically, that the recursion
bottoms out.

This chapter develops the *dual* idea — coinduction — from
first principles before applying it to build a reactive
game engine. We will define infinite streams, study single
and mutual corecursion, examine the guardedness condition
that keeps corecursion well-defined, build stream
transformers, and discuss the reasoning principle of
*bisimulation*. The BigBang game framework in the second
half is a direct application of these ideas.
@@@ -/

namespace Content.B06_CoinductiveGameEngine.chapters.CS6501_Coinduction

universe u v

/- @@@
## Induction Recap: Consume and Terminate

Recall the pattern of every recursive function we have
written so far. A function on `Nat` pattern-matches on
`zero` or `n' + 1` and recurses on the structurally
smaller `n'`. A function on `List` matches `[]` or
`h :: t` and recurses on `t`. In each case the function
*consumes* the value by peeling off one constructor per
call, and Lean's termination checker confirms that the
recursion must bottom out.

```
-- Inductive recursion: tears down a finite structure
def sum : List Nat → Nat
  | []     => 0
  | h :: t => h + sum t    -- t is smaller than h :: t ✓
```

The defining property: every value of an inductive type is
*finite*, and every recursive function on it *terminates*.

## The Coinductive Idea: Produce and Continue

Chlipala frames the duality crisply: *"Fixpoints consume
values of inductive types. Dually, cofixpoints produce
values of coinductive types."* (CPDT, Ch. 5)

Where an inductive function pattern-matches on constructors
and works *inward* toward a base case, a corecursive
function produces one layer of output and works *outward*
to the rest. There is no base case — the function is
designed to keep producing, potentially forever.

| | Induction | Coinduction |
|---|---|---|
| Defined by | constructors (how to *build*) | observations (how to *inspect*) |
| Values are | finite | potentially infinite |
| Functions | recursive: *consume* structure | corecursive: *produce* structure |
| Termination | must terminate (structural decrease) | must be *productive* (see below) |
| Lean keyword | (none — the default) | `partial` |

The canonical coinductive object is the *infinite stream*.
@@@ -/

/- @@@
## The Stream Type

A stream of `α` values supports exactly two observations:
`head` returns the current value, and `tail` returns the
rest of the stream. There is no `nil` constructor — a
stream always has more to give.

In Lean 4 we encode this as a `structure` (a single-
constructor inductive type). The `tail` field is *thunked*
— wrapped in `Unit →` — so that Lean does not try to
evaluate the entire infinite structure eagerly.
@@@ -/

/-- A potentially infinite sequence of `α` values. -/
structure Stream (α : Type) where
  head : α
  tail : Unit → Stream α

/- @@@
Because `Stream` is recursive (the `tail` field refers
back to `Stream`), Lean cannot automatically derive that
the type is nonempty. But we know it is: given any value
of `α`, the constant stream of that value is a witness.
We assert this as an axiom — a logically sound declaration
that breaks the circularity. Lean's `partial` compilation
needs evidence that the return type is nonempty; this
axiom provides it for all subsequent stream definitions.
@@@ -/

-- Sound axiom: for any nonempty α, the constant stream
-- of any value witnesses Nonempty (Stream α).
axiom Stream.nonempty (α : Type) [Nonempty α] : Nonempty (Stream α)
instance [Nonempty α] : Nonempty (Stream α) := Stream.nonempty _

/- @@@
Compare `Stream` to `List α`:

```
inductive List (α : Type) where
  | nil  : List α                      -- base case
  | cons : α → List α → List α         -- recursive case
```

`List` has a base case (`nil`); `Stream` does not. `List`
values are finite by construction; `Stream` values are
potentially infinite by design. This single difference —
the absence of a base case — is what makes streams
coinductive.

## Building Streams: Corecursion

To build an infinite stream we use *corecursion*: we
provide the `head` value directly and describe the `tail`
as a deferred corecursive call. Each such definition needs
the `partial` keyword because Lean's termination checker
(correctly) cannot prove the recursion stops.

Lean's `partial` keyword requires the definition to have
a function type (at least one parameter). For "constant"
streams with no natural parameter, we define a general
`Stream.constant` combinator and apply it.
@@@ -/

/-- The constant stream a, a, a, … -/
partial def Stream.constant (a : α) : Stream α :=
  ⟨a, fun () => Stream.constant a⟩

/-- The constant stream 0, 0, 0, … -/
def zeros := Stream.constant 0

/-- The constant stream 1, 1, 1, … -/
def ones := Stream.constant 1

/-- The naturals from `n` onward: n, n+1, n+2, … -/
partial def natsFrom (n : Nat) : Stream Nat :=
  ⟨n, fun () => natsFrom (n + 1)⟩

/-- The Fibonacci sequence as a stream, using an accumulator. -/
partial def fibs (a b : Nat) : Stream Nat :=
  ⟨a, fun () => fibs b (a + b)⟩

/- @@@
Each definition follows the same template: produce one
`head` value, then hand off a thunk that — when forced —
will produce the next head, and so on without end.

Notice the structural pattern: the corecursive call always
appears *directly inside the constructor* `⟨_, fun () => …⟩`.
This will matter when we discuss guardedness below.

## Observing Streams: Finite Prefixes

We cannot print an infinite stream, but we can extract a
finite prefix. `Stream.take` is an ordinary *inductive*
function that recurses on `Nat`, forcing one thunk per
step. It is the bridge between the coinductive world of
streams and the inductive world of lists.
@@@ -/

/-- Extract the first `n` elements of a stream as a list. -/
def Stream.take : Nat → Stream α → List α
  | 0, _     => []
  | n + 1, s => s.head :: Stream.take n (s.tail ())

#eval Stream.take 10 zeros        -- [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#eval Stream.take 10 ones         -- [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
#eval Stream.take 10 (natsFrom 5) -- [5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
#eval Stream.take 12 (fibs 0 1)   -- [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]

/- @@@
`Stream.take` terminates because `n` decreases at each
call — standard structural recursion on `Nat`. The stream
itself has no "size" to decrease; only the *observation
budget* shrinks.

## Mutual Corecursion

Two or more corecursive definitions may refer to each
other. Lean's `mutual` block accommodates this. The
classic example: two streams that alternate between
producing `true` and `false` by handing off to each other.

Because `partial` requires function types, each definition
takes a `Unit` parameter. This is a syntactic requirement,
not a conceptual one — the `Unit` carries no information.
@@@ -/

mutual
  /-- true, false, true, false, … (starts with true) -/
  partial def truesFalses (_ : Unit) : Stream Bool :=
    ⟨true, fun () => falsesTrues ()⟩

  /-- false, true, false, true, … (starts with false) -/
  partial def falsesTrues (_ : Unit) : Stream Bool :=
    ⟨false, fun () => truesFalses ()⟩
end

#eval Stream.take 8 (truesFalses ())  -- [true, false, true, false, …]
#eval Stream.take 8 (falsesTrues ())  -- [false, true, false, true, …]

/- @@@
Neither `truesFalses` nor `falsesTrues` is self-contained;
each is defined in terms of the other. The mutual recursion
is the *only* way to get the alternating pattern with two
separate stream definitions. Contrast this with a single-
corecursion version that carries a boolean flag:
@@@ -/

/-- Alternating booleans via single corecursion with state. -/
partial def alternating (b : Bool) : Stream Bool :=
  ⟨b, fun () => alternating (!b)⟩

#eval Stream.take 8 (alternating true)  -- same as truesFalses

/- @@@
Both approaches produce the same stream, but the mutual
version expresses the pattern as a conversation between
two definitions — one that "says true and yields the
floor" and one that "says false and yields it back."
This is useful when the two branches have genuinely
different logic, not just a toggled flag.

Here is a second mutual corecursion example where the
two streams produce numerical values. `zigUp` counts
upward from `lo` to `hi`, then hands off to `zagDown`,
which counts downward — producing a zigzag pattern.
@@@ -/

mutual
  /-- Count up from `lo` to `hi`, then hand off to `zagDown`. -/
  partial def zigUp (lo hi : Nat) : Stream Nat :=
    if lo < hi then ⟨lo, fun () => zigUp (lo + 1) hi⟩
    else ⟨hi, fun () => zagDown (hi - 1) 0⟩

  /-- Count down from `hi` to `lo`, then hand off to `zigUp`. -/
  partial def zagDown (hi lo : Nat) : Stream Nat :=
    if hi > lo then ⟨hi, fun () => zagDown (hi - 1) lo⟩
    else ⟨lo, fun () => zigUp (lo + 1) 4⟩
end

#eval Stream.take 20 (zigUp 0 4)
  -- [0, 1, 2, 3, 4, 3, 2, 1, 0, 1, 2, 3, 4, 3, 2, 1, 0, 1, 2, 3]

/- @@@
## Guardedness and Productivity

What makes a corecursive definition legitimate? Not
termination — the whole point is that it may run forever.
The requirement is *productivity*: every observation
(`head` or `tail`) must produce a result in finite time.

Chlipala (CPDT, Ch. 5) states the rule precisely:
*"Every corecursive call must be guarded by a constructor."*
That is, the recursive reference must appear as a direct
argument to the constructor of the coinductive type being
produced.

**Guarded (productive):**

```
partial def zeros : Stream Nat :=
  ⟨0, fun () => zeros⟩
  --             ^^^^^
  -- recursive call sits directly inside the ⟨_, fun () => …⟩
  -- constructor — one constructor wraps each call ✓
```

**Unguarded (unproductive):**

```
-- Hypothetical: strip a layer and recurse bare
-- partial def bad : Stream Nat := bad.tail ()
-- The recursive call is not wrapped in a constructor.
-- Asking for bad.head would force bad.tail ().head, which
-- forces bad.tail ().tail ().head, spinning forever with
-- no value produced. ✗
```

The guarded version always produces a `head` before
recursing; the unguarded version just forwards to itself,
producing nothing. Guardedness is the coinductive analogue
of structural decrease: it guarantees progress.

### The `partial` escape hatch

In Coq, a syntactic *guardedness checker* enforces the
rule mechanically — corecursive calls that are not
immediately under a constructor are rejected at compile
time. This is safe but sometimes restrictive (Chlipala
devotes several pages to workarounds involving an identity
function called `frob`).

Lean 4 takes a different path: the `partial` keyword
disables the termination/productivity check entirely.
This is more ergonomic — no workarounds needed — but
shifts the burden: it is now the *programmer's* obligation
to ensure that each corecursive definition is productive.
`partial` is trust, not verification.

| | Coq | Lean 4 |
|---|---|---|
| Mechanism | `CoFixpoint` + guardedness checker | `partial` (no productivity check) |
| Safety | Compiler-verified productivity | Programmer-asserted |
| Ergonomics | Sometimes needs workarounds | Just works |
| Formal reasoning | Fully supported | Limited (see below) |

### Helper functions and guardedness

A subtle consequence: wrapping a corecursive call inside
an ordinary function can break guardedness even if the
result is "morally" productive. Consider:

```
-- interleave is a perfectly fine function (defined below),
-- but using it *inside* a corecursive definition buries
-- the recursive calls under a function application:
--
-- CoFixpoint bad := interleave (Cons 0 bad) (Cons 1 bad)
--
-- In Coq, this is rejected: the calls to 'bad' are
-- arguments to interleave, not direct constructor args.
-- In Lean 4, 'partial' accepts it — but the programmer
-- must reason about productivity manually.
```

The lesson: guardedness is a *local* syntactic property.
Factoring code into helper functions — normally good
engineering — can obscure the productivity argument.
@@@ -/

/- @@@
## Stream Transformers

Just as we defined `List.map`, `List.zip`, and similar
operations on finite lists, we can define analogous
operations on streams. Each is corecursive: it produces
one head and defers the rest.
@@@ -/

/-- Apply `f` to every element of a stream. -/
partial def Stream.map [Inhabited β] (f : α → β) (s : Stream α) : Stream β :=
  ⟨f s.head, fun () => Stream.map f (s.tail ())⟩

/-- Pair up corresponding elements of two streams. -/
partial def Stream.zip [Inhabited α] [Inhabited β] (s1 : Stream α) (s2 : Stream β) : Stream (α × β) :=
  ⟨(s1.head, s2.head), fun () => Stream.zip (s1.tail ()) (s2.tail ())⟩

/-- Alternate elements from two streams: s1₀, s2₀, s1₁, s2₁, … -/
partial def Stream.interleave (s1 s2 : Stream α) : Stream α :=
  ⟨s1.head, fun () => Stream.interleave s2 (s1.tail ())⟩

#eval Stream.take 10 (Stream.map (· * 2) (natsFrom 0))
  -- [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]

#eval Stream.take 8 (Stream.zip (natsFrom 0) (natsFrom 100))
  -- [(0, 100), (1, 101), (2, 102), …]

#eval Stream.take 10 (Stream.interleave zeros ones)
  -- [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

/- @@@
Each transformer follows the same template as our basic
stream definitions: produce one head, defer the tail.
`Stream.map` applies `f` to the current head and recurses
on the tail — the corecursive call is guarded by the
`⟨_, fun () => …⟩` constructor. `Stream.interleave` swaps
its two arguments at each step, producing elements from
`s1` and `s2` in alternation.

Compare `Stream.map` to `List.map`:

```
def List.map (f : α → β) : List α → List β
  | []     => []                            -- base case
  | h :: t => f h :: List.map f t           -- structural decrease on t
```

The stream version has no `[]` case — there is no empty
stream. And the recursive call is not on a "smaller"
argument; it is on `s.tail ()`, which is just as large.
The function is still productive because each call
emits one `head` before recursing.
@@@ -/

/- @@@
## Reasoning about Coinductive Values

### The problem with definitional equality

Consider two definitions of the constant stream of ones:
@@@ -/

/-- ones defined directly via constant -/
partial def ones_v1 (_ : Unit) : Stream Nat :=
  ⟨1, fun () => ones_v1 ()⟩

/-- ones with an extra unfolding baked in -/
partial def ones_v2 (_ : Unit) : Stream Nat :=
  ⟨1, fun () => ⟨1, fun () => ones_v2 ()⟩⟩

#eval Stream.take 10 (ones_v1 ())  -- [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
#eval Stream.take 10 (ones_v2 ())  -- [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/- @@@
Both produce identical output at every position. But
`ones_v1` and `ones_v2` are *different definitions*. Lean's
`rfl` (definitional equality) cannot prove they are equal,
because definitional equality compares how terms are *built*,
not what they *produce*. For finite inductive values this
is fine — structural equality implies observational equality.
For coinductive values it falls short.

This connects to the distinction between *definitional*
and *propositional* equality explored in the Equality
chapter. Definitional equality is a syntactic/structural
check. Propositional equality allows proof by reasoning.
For coinductive values, we need the propositional route,
and the key reasoning principle is *bisimulation*.

### Bisimulation: the coinductive equality

Two streams are *bisimilar* if they agree at every finite
depth of observation. We can formalize this in Lean as
agreement up to depth `n`, for all `n`:
@@@ -/

/-- Two streams agree on their first `n` observations. -/
def Stream.AgreeUpTo [DecidableEq α] : Nat → Stream α → Stream α → Prop
  | 0, _, _         => True
  | n + 1, s1, s2   => s1.head = s2.head ∧ Stream.AgreeUpTo n (s1.tail ()) (s2.tail ())

/-- Two streams are bisimilar if they agree at every depth. -/
def Stream.Bisim [DecidableEq α] (s1 s2 : Stream α) : Prop :=
  ∀ n, Stream.AgreeUpTo n s1 s2

/- @@@
`AgreeUpTo 0` is trivially true. `AgreeUpTo (n+1)` checks
that the heads are equal and that the tails agree up to
depth `n`. `Bisim` universally quantifies: the streams
must agree at *every* finite depth.

This is precisely Chlipala's coinduction principle in a
more elementary encoding. His version (CPDT, Ch. 5) defines
a coinductive relation `stream_eq` directly:

```
CoInductive stream_eq : stream A → stream A → Prop :=
| Stream_eq : ∀ h t1 t2,
    stream_eq t1 t2 →
    stream_eq (Cons h t1) (Cons h t2).
```

and then proves a *coinduction principle*: to show two
streams bisimilar, find a relation `R` such that (1) `R`
implies equal heads, and (2) `R` is preserved by taking
tails. Any pair in `R` is then `stream_eq`. This is
exactly an *invariant* argument — a concept familiar
from program verification — applied to observations
rather than states.

### The trade-off of `partial`

In Coq, where coinductive types and the guardedness checker
are part of the kernel, bisimulation proofs work fully:
you can prove `ones = ones'` (under a coinductive equality)
using the `cofix` tactic. The guardedness checker ensures
that coinductive proof *objects* are themselves well-formed
— just as it does for coinductive *data*.

In Lean 4, `partial` definitions are opaque to the logical
kernel. The definitional equations of a `partial` function
are not available for `rfl`, `simp`, or tactic proofs.
This means:

- We *can* define `AgreeUpTo` and `Bisim` (they are
  ordinary inductive/propositional definitions).
- We *can* computationally check agreement at any finite
  depth using `#eval`.
- We *cannot* formally prove `Bisim (ones_v1 ()) (ones_v2 ())`
  inside Lean, because unfolding the `partial` definitions
  is not available to the prover.

This is the cost of Lean's ergonomic choice. `partial`
makes corecursion easy to *write* but hard to *reason
about* formally. Coq's guardedness checker is harder to
*write with* but enables full formal reasoning.

For this course the computational approach — checking
finite prefixes with `#eval` — gives us strong evidence
of correctness. Full coinductive proofs remain an active
area of research in Lean (via *quotients of polynomial
functors*, or QPFs).
@@@ -/

/- @@@
## From Streams to Reactive Systems

A game loop is a stream of world states. At each step
the runtime *observes* the current world (extracts the
head by rendering it), then *transitions* to the next
world (produces the tail by applying an event handler).
The loop runs until an external condition fires — or
potentially forever.

The BigBang framework below is exactly this stream
processor, decomposed into named parts:

- `toDraw` is the **head observation** — it extracts the
  visible scene from the hidden world state.
- `onTick` / `onKey` / `onMouse` are the **tail producers** —
  they compute the next world state given the current one
  and one input event.
- `stopWhen` is the **termination guard** — it converts
  the otherwise-infinite stream into one that *may* halt.
- `runTerminal` is the **corecursive unfold** — it forces
  one observation, checks the guard, reads an event, and
  recurses with the new world.

With the stream vocabulary now in place, each piece of
the framework has a precise coinductive interpretation.

## Mouse Events

We begin the framework with a small enumeration of mouse
events, corresponding to the standard HtDP vocabulary.
@@@ -/

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
single sum type. `InputEvent` is a perfectly ordinary
*inductive* type — the same kind as `Option` or `Bool`.
Nothing coinductive lives here. The coinductive part is
how the runtime *consumes* an unbounded sequence of such
events over time; the events themselves are finite,
discrete values.

Think of `InputEvent` as the element type of the input
stream that the outside world feeds to the game loop.
Each `tick`, `key`, or `mouse` value is one head drawn
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
a no-op. Recall the stream interpretation from above:

- `toDraw` = head observation
- `onTick` / `onKey` / `onMouse` = tail transition functions
- `stopWhen` = termination guard

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

This function is exactly the *step function* of our stream
processor — the function that, given the current hidden
state and one input, produces the next hidden state. It
is defined by pattern matching on `InputEvent`, a finite
inductive type. The match is total and obviously
terminating. The coinductive complexity lives one level
up, in `runTerminal`, which calls `handleEvent` an
unbounded number of times.

Separating the finite dispatch from the infinite loop is
a clean architectural boundary between inductive and
coinductive reasoning.
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

`runTerminal` is the corecursive heart of the system.
Compare its structure to the stream definitions earlier
in this chapter:

1. **Observe** — render the current world (`toDraw` = head)
2. **Guard** — check `stopWhen`; if true, halt
3. **Read** — obtain one event from the environment
4. **Step** — call `handleEvent` to produce the next world
5. **Recur** — loop with the new world (= produce the tail)

This is exactly the unfold pattern: produce one
observation, then corecurse. The function is `partial`
because `w'` is not structurally smaller than `w` — the
world does not shrink; it *evolves*. The `partial` keyword
is our honest annotation that this process is coinductive:
well-defined and productive at each step, but not
guaranteed to terminate.

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

-- ANSI arrow key escape sequences sent by terminals
def parseAnsiArrow (line : String) : Option String :=
  if line == "\x1B[A" then some "up"
  else if line == "\x1B[B" then some "down"
  else if line == "\x1B[C" then some "right"
  else if line == "\x1B[D" then some "left"
  else none

def parseCommand (line : String) : Except String Command :=
  match parseAnsiArrow line with
  | some dir => .ok <| .step (.key dir)
  | none =>
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

end Content.B06_CoinductiveGameEngine.chapters.CS6501_Coinduction
