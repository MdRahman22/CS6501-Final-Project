/- @@@
# Certified!

Our formalized algebraic structures define classes of
objects that monoids, semigroups, groups, and so forth.
We can be assured that any isntance of any such class
satisfies all of the requirements for an object to be
in that class. To be a monoid, for exampl, one must have
a carrier set (type), a binary operator, an identity, and
proofs that these things all work together *in the way you
would expect* no matter what type of objects are in the
underlying carrier set (integers, fields, matrices, etc.)

The key that makes much of this work is the dependent type.
A dependently typed object is one that associates a value
with a proof of some proposition, most critically here one
that is *about* that value. For example, the proposition,
∃ x, P x, asserts that there exists some x, such that there
is a proof of the proposition, P x. That proposition, in
turn, is the result of applying the predicate (function),
P, to x. Finally, if there's a proof of P x for a specific
x, then we could rightly say that there exists an x with
that property.

The payoff is that we can be sure
beyond nearly any doubt that any instance of one of classes
(such as monoid or group) will provide all the structure, of
types and functions and theorems and notations and the like,
promised by the class, but for particular variables, such as
the type of objects in the carrier set. Mathematics already
gives you that. What Lean gives you is that *on automation*.


<!-- toc -->


Now we'll look at a fundamental concept in type theory and
 practical mechanism in type-theoretical programming: that
 of *dependent types*, of two fundamental kinds: dependent
 pair types, and function types whose output types depend
 on input values.

A dependent pair types is a type of pairs, ⟨ val, pf ⟩,
where *val* is a value of some type and *pf* is a proof
that that particular value, *val*, has some property in
the sense that there's a proof of a proposition *(P val)*
asserting that *val* satisfies the predicate, i.e., has the
property, *P*.

That's important because if someone hands you a value on
the street and says, trust me, that's gold, ... well, ok,
where's the hidden camera? But if someone hands you a box
and inside there's a value and right next to it is a Lean
checked proof that it really is gold, well, now you know.
You have a proof-certified value.

If we overload our Duration and Time types as the carrier
sets for a Torsor (points in Time) over a group of actions
(rotations of the clock arm), in Lean, the we can be sure
we've implemented the algebra as a flawless construction.
It's the pairing of the ordinary data and functions with
*machine checked proofs involving them* that creates an
ironclad guarantee: you cannot construct a group unless
you can provide proofs that the operations you've defined
satisfy all of the rules that must be followed if one is
to have a mathematical group. The group objects we've now
created is a first *certified* mathematical program*.

Again the recurring trick is to bundle data together with
*proofs about that data*. A monoid does not merely carry an
operation and an identity element — it carries proofs that
the identity element behaves correctly and that the operation
is associative. A group adds further proof obligations. The
typeclass instances encoding these structures are not just
records of data; they are *dependently typed* records in the
sense that they contain proofs that the data satisfy the key
invariants that characterize these various abstract algebraic
structures.

That trick has a name and a deeper story. We diverge briefly from
the algebraic thread here to examine its foundations. The key concept
is the *dependent type* — a type whose form depends on a *value*. We
will see how dependent types give rise to proof-carrying values and to
functions whose return types vary with their inputs. And then, almost
as a corollary, we arrive at something fundamental: dependent types
*are* the quantifiers of predicate logic. Welcome to that.
@@@ -/

namespace Content.B04_AlgebraicStructures.chapters.dependentTypesPredicateLogic

/- @@@
## Dependent Pairs

The simplest dependent type is the *dependent pair*, also called the
*Sigma type*. An ordinary pair `α × β` carries a value of type `α`
and a value of type `β`, with no relationship between them. A dependent
pair goes further: the *type* of the second component can depend on
the *value* of the first component.

In Lean, the canonical notation for a dependent pair type is the
*subtype*: `{ x : α // P x }`. A value of this type is an anonymous
pair `⟨v, h⟩` where:
- `v : α` is the value
- `h : P v` is a proof that *this specific value* satisfies property `P`

The type of `h` depends on `v`. That dependence is what makes the
pair *dependent*.
@@@ -/

-- A dependent pair: a natural number together with a proof that it is zero
def ZeroNat : Type := { n : Nat // n = 0 }

def theZero : ZeroNat := ⟨0, rfl⟩     -- value 0; proof: 0 = 0
-- #check (⟨ 1, rfl ⟩ : ZeroNat)


def isEv (n : Nat) : Prop := n % 2 = 0
def EvenNat : Type := { n : Nat // isEv n }

-- details about how check actually works: it does NOT infer a proof here
#check (⟨3, _⟩ : EvenNat)

def fourIsEvenNat : EvenNat := ⟨ 4, rfl ⟩
def fromEvenToOdd (n : EvenNat) : Nat := 0
#eval (fromEvenToOdd (fourIsEvenNat :EvenNat))



-- The subtype has two projections
#eval theZero.val         -- 0
#check theZero.property   -- theZero.property : theZero.val = 0

/- @@@
Notice what we cannot do: we cannot build a `ZeroNat` from any value
other than `0`. The pair `⟨5, ???⟩` would require a proof of `5 = 0`,
which no one can supply. The type system enforces this at construction
time, before any program runs.

This is the fundamental payoff. We can define a *type* that contains
exactly those values satisfying a given property — not by filtering at
runtime, but by requiring a proof at construction time. That is the
algebra-chapter trick, seen in its simplest form.

## Predicates

The property `P` in `{ x : α // P x }` is a *predicate*. A predicate
over type `α` is a function `P : α → Prop`. Apply it to a specific
value `v : α` and you get a proposition `P v` — a type that either has
a proof (the property holds for `v`) or does not (it fails for `v`).
The predicate itself is neither true nor false; it becomes a proposition
only when applied to a specific input.

In Lean, a predicate is simply a function into `Prop`. There is no
encoding, no separate mechanism. `Prop` is the universe of propositions,
and a function into it is a predicate.
@@@ -/

-- "n is even": there exists a k such that n = 2 * k
def isEven : Nat → Prop := fun n => ∃ k, n = 2 * k

-- "m divides n": there exists a k such that n = m * k
def divides : Nat → Nat → Prop := fun m n => ∃ k, n = m * k

-- "s is long": the string has more than five characters
def isLong : String → Prop := fun s => s.length > 5

example : isLong "Hello!" := by
  unfold isLong
  decide

/- @@@
Applying a predicate to a specific value yields a specific proposition.
@@@ -/

#check isEven 4       -- isEven 4 : Prop   (true — has a proof)
#check isEven 7       -- isEven 7 : Prop   (false — no proof exists)
#check divides 3 12   -- divides 3 12 : Prop
#check isLong "hi"    -- isLong "hi" : Prop

-- Proofs that specific predicate applications hold
def fourIsEven : isEven 4 := ⟨2, rfl⟩              -- 4 = 2 * 2
def threeDividesTwelve : divides 3 12 := ⟨4, rfl⟩  -- 12 = 3 * 4

/- @@@
## Dependent Pairs

With predicates in hand, we can revisit the dependent pair more
carefully. The subtype `{ n : Nat // isEven n }` is a *dependent sum
type* — a Sigma type. It pairs a natural number `n` with a proof of
`isEven n`. The "sum" in the name reflects that the type is a disjoint
union indexed over values of `α`: one variant for each `v`, carrying a
proof that `v` satisfies `P`.
@@@ -/

-- -- The type of even natural numbers: value plus proof of evenness
-- def EvenNat : Type := { n : Nat // isEven n }

-- def fourEven : EvenNat := ⟨4, ⟨2, rfl⟩⟩     -- 4 = 2 * 2
-- def zeroEven : EvenNat := ⟨0, ⟨0, rfl⟩⟩     -- 0 = 2 * 0

-- #eval fourEven.val     -- 4
-- #eval zeroEven.val     -- 0

/- @@@
Odd values simply cannot be inserted. The pair `⟨3, ???⟩` would need a
proof of `isEven 3` — a witness `k` and a proof that `3 = 2 * k`. No
such `k` exists in the naturals, so no proof can be given, so the pair
cannot be built.

This is precisely what happens in the algebra chapters: a Monoid instance
for some type cannot be constructed without proofs of the identity and
associativity laws. An illegal Monoid is exactly as impossible to construct
as an odd `EvenNat`.

The existential quantifier `∃` is the same idea at the `Prop` level.
The proposition `∃ (x : α), P x` asserts that *some* value of type `α`
satisfies `P`. A proof of it is a pair: a witness `w : α` and a proof
of `P w`. This is a dependent pair — a Sigma type — restricted to the
universe of propositions.
@@@ -/

-- There exists an even natural number (witness: 0, since 0 = 2 * 0)
theorem exists_even : ∃ n : Nat, isEven n := ⟨0, ⟨0, rfl⟩⟩

-- There exists a number divisible by both 3 and 5 (witness: 15)
theorem exists_divisible : ∃ n : Nat, divides 3 n ∧ divides 5 n :=
  ⟨15, ⟨⟨5, rfl⟩, ⟨3, rfl⟩⟩⟩    -- 15 = 3 * 5 and 15 = 5 * 3

-- To use an existential, destructure the dependent pair
example (h : ∃ n : Nat, isEven n) : True := by
  obtain ⟨n, k, _⟩ := h    -- n is the witness; k is the halving factor
  trivial

/- @@@
## Dependent Product Types: Dependent-Returning Functions

The other half of the picture is the *dependent product type* (Pi type,
written Π). Where a Sigma type pairs a value with a proof, a Pi type is
a *function* whose return *type* depends on its input *value*.

An ordinary function `f : α → β` always returns a `β`, regardless of
which `α` is passed. A dependent function `f : (x : α) → P x` returns
a value whose type is `P x` — different for different inputs. The return
type genuinely varies with the value.

The universal quantifier `∀` is the Pi type at the `Prop` level. The
proposition `∀ (x : α), P x` asserts that `P x` holds for every `x : α`.
A proof of it is a function that, given any `x`, returns a proof of
`P x`. That function is a Pi type: its return type `P x` depends on
the input `x`.

In Lean, `∀ (x : α), P x` and `(x : α) → P x` are the same notation.
The universal quantifier just is the dependent function type.
@@@ -/

-- Every natural number is either zero or positive
theorem zero_or_pos : ∀ n : Nat, n = 0 ∨ n > 0 := by
  intro n
  cases n with
  | zero   => exact Or.inl rfl
  | succ n' => exact Or.inr (Nat.succ_pos n')

-- Every natural number doubled is even.
-- Proof: a function returning the witness k = n and rfl.
theorem double_even : ∀ n : Nat, isEven (2 * n) :=
  fun n => ⟨n, rfl⟩       -- 2 * n = 2 * n

-- 2 divides every doubled number
theorem two_divides_doubles : ∀ n : Nat, divides 2 (2 * n) :=
  fun n => ⟨n, rfl⟩

-- The same two theorems written with explicit Pi type notation.
-- ∀ n : Nat, P n   and   (n : Nat) → P n   mean exactly the same thing.
def double_even' : (n : Nat) → isEven (2 * n) :=
  fun n => ⟨n, rfl⟩

def two_divides_doubles' : (n : Nat) → divides 2 (2 * n) :=
  fun n => ⟨n, rfl⟩

/- @@@
`double_even` is proved by a plain function. Given any `n`, we return
a proof that `isEven (2 * n)` holds. That proof is itself an existential
pair — the witness `n` and `rfl`. The Pi type is the function; the Sigma
type is its return value. They fit together naturally.

At the `Prop` level, Pi and Sigma types are exactly ∀ and ∃. At the
`Type` level, the same idea gives us *programs that return proofs of
their own correctness* as part of their output type.

Consider a function that checks whether a string has exactly `n`
characters. If yes, return the string paired with a proof of its
length. If no, return the empty string paired with a proof that its
length is zero. The caller receives not just a string, but a string
whose length has been machine-checked.
@@@ -/

def checkedLength (s : String) (n : Nat) :
    { t : String // t.length = n } ⊕ { t : String // t.length = 0 } :=
  if h : s.length = n then
    Sum.inl ⟨s, h⟩
  else
    Sum.inr ⟨"", by native_decide⟩

-- A helper to extract the string from either branch
def getResult {n : Nat} :
    { t : String // t.length = n } ⊕ { t : String // t.length = 0 } → String
  | Sum.inl ⟨s, _⟩ => s
  | Sum.inr ⟨s, _⟩ => s

#eval getResult (checkedLength "hello" 5)   -- "hello"
#eval getResult (checkedLength "hello" 3)   -- ""

/- @@@
The proofs in the return type are not comments or assertions — they are
machine-checked guarantees, part of the value. The `if h : s.length = n`
pattern binds `h` to the proof in the true branch, handing it directly
to the constructor. No proof is fabricated; none can be.

## The Curry-Howard Correspondence, Complete

We now have the full table for constructive predicate logic. Compare
with the propositional table from the earlier chapters:

```
Proposition            Type (Curry-Howard)

P ∧ Q                  Prod P Q             (non-dependent pair)
P ∨ Q                  Sum P Q
P → Q                  P → Q                (non-dependent function)
¬P                     P → Empty

∀ (x : α), P x        (x : α) → P x        Pi type   (dependent function)
∃ (x : α), P x        Σ (x : α), P x       Sigma type (dependent pair)
```

The top rows are propositional logic: types whose structure does not
depend on values. The bottom rows are predicate logic: types whose
structure *does* depend on values. The move from propositional to
predicate logic is the move from fixed propositions to propositions
*about specific values*.

Dependent types — Pi and Sigma — make that move possible. And we have
been using them all along: every typeclass instance in the algebra
chapters is a dependent record. Every proof of an algebraic law is a
term in a Pi type. The machinery was always there; now we have the
name and the picture.

Welcome to constructive predicate logic. It's good for math anyway!
@@@ -/

end Content.B04_AlgebraicStructures.chapters.dependentTypesPredicateLogic
