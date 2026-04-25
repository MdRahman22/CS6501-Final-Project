```lean
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
```

# Overloaded Structures: I. Monoid

<!-- toc -->

We ended the last chapter with the observation that we
had not properly tied together the binary operator and
the identity value *for that operator* in the arguments
to our higher-order *map* and *foldr* functions.

What we really want to pass to these functions is a
structure that bundles these things together along with
proofs that they are correctly related: an operator, a
value, and a proof that that value really behaves as a
(left and right) zero should, always leaving an argument
unchanged when zero is added on either the left or right.

What we want is an absrtact algebraic object called a
*monoid*. Let make the idea concrete with a new example,
and develop the notion from there.

## A Three-Hour Clock

Consider a clock that counts only hours, and only
up to three. There are exactly three durations: zero
hours, one hour, and two hours. After two, the clock
wraps back to zero.

```lean
namespace Content.B02_ClassicalPropositionalLogic.chapters.monoid

inductive Duration where
| zero
| one
| two
deriving Repr, BEq, DecidableEq

open Duration
```

### Adding Durations

We can add durations. The result wraps around modulo
three: one + two = zero, two + two = one, and so on.
There are nine cases, one for each pair of values.

```lean
def durAdd : Duration → Duration → Duration
| zero, d => d
| d, zero => d
| one, one => two
| one, two => zero
| two, one => zero
| two, two => one

#eval durAdd one two    -- zero
#eval durAdd two two    -- one
```

### What Laws Does This Operation Satisfy?

Our clock arithmetic is well behaved. If we check,
we find that durAdd satisfies three important laws.

**Zero is an identity element.** Adding zero to any
duration leaves it unchanged: durAdd zero d = d and
durAdd d zero = d for all d.

**The operation is associative.** The order of grouping
doesn't matter: durAdd (durAdd a b) c = durAdd a (durAdd b c)
for all a, b, c.

A type equipped with a binary operation, an identity
element, and proofs of these laws is called a *monoid*.
Our three-hour clock is a monoid.

## What is a Monoid?

A monoid is a triple: a carrier type, a binary operation,
and a distinguished identity element, satisfying:

- **Associativity**: (a * b) * c = a * (b * c) for all a, b, c
- **Left identity**: e * a = a for all a
- **Right identity**: a * e = a for all a

Familiar examples: (Nat, +, 0), (Nat, *, 1), (String, ++, ""),
(List, ++, []). Our (Duration, durAdd, zero) is another.

## Mathlib's AddMonoid Hierarchy

Lean's Mathlib library represents monoids as typeclasses,
organized in a hierarchy. We build an AddMonoid for
Duration by providing instances for each layer, starting
from the bottom.

### Add: A Type with a + Operation

At the bottom of the hierarchy, Add simply declares that
a type has a binary operation called *add*, written `+`.

```
class Add (α : Type u) where
  add : α → α → α
```

```lean
#check Add

instance : Add Duration where
  add := durAdd

#eval one + two
```

### Zero: A Type with a Distinguished Element

Zero provides the constant `0`. Together with Add,
these are the raw materials from which richer structures
are built.

```
class Zero (α : Type u) where
  zero : α
```

```lean
#check Zero

instance : Zero Duration where
  zero := Duration.zero
```

With these two instances in place, Lean now resolves
the `+` notation and the `0` literal for Duration.
When we write `one + two`, Lean searches for an
`Add Duration` instance and finds the one above. When
we write `0`, Lean finds our `Zero Duration` instance.

```lean
#eval (one + two : Duration)    -- zero
#eval (0 + one : Duration)   -- one
```

### AddSemigroup: Associative Addition

An AddSemigroup requires a proof that `+` is associative.

```
class AddSemigroup (G : Type u) extends Add G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
```

Note the `extends Add G`: an AddSemigroup *inherits* an
Add instance. Since we already defined `Add Duration`,
Lean picks it up automatically — we only need to supply
the new field, the associativity proof.

Because Duration has only three values, we prove this by
exhausting all 3³ = 27 cases. The *cases* tactic splits on
each constructor; *rfl* closes each goal by computation.

```lean
#check AddSemigroup

instance : AddSemigroup Duration where
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
```

### AddZeroClass: Zero as Identity

AddZeroClass requires proofs that zero is both a left
and a right identity for addition.

```
class AddZeroClass (M : Type u) extends Zero M, Add M where
  zero_add : ∀ a : M, 0 + a = a
  add_zero : ∀ a : M, a + 0 = a
```

This class extends both `Zero M` and `Add M`. Lean finds
our existing `Zero Duration` and `Add Duration` instances
automatically, so we only need to supply the two identity
proofs.

```lean
#check AddZeroClass

instance : AddZeroClass Duration where
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
```

### AddMonoid: Putting It Together

AddMonoid extends AddSemigroup and AddZeroClass and adds
*nsmul* (natural-number scalar multiplication: adding a
value to itself n times). The nsmul fields have default
implementations, so we supply the standard recursive
definition and its proofs.

```
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  nsmul : ℕ → M → M
  nsmul_zero : ∀ x, nsmul 0 x = 0
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = nsmul n x + x
```

This is the top of the hierarchy. It extends both
`AddSemigroup M` and `AddZeroClass M`. Lean finds our
instances for both — including, transitively, the `Add`
and `Zero` instances they depend on. All that remains
is to supply the nsmul fields. We use `nsmulRec`, a
standard recursive implementation that defines repeated
addition in terms of `+` and `0`, and its proofs hold
by definitional equality (`rfl`).

```lean
#check AddMonoid

instance : AddMonoid Duration where
  nsmul := nsmulRec
  nsmul_zero := by intro x; rfl
  nsmul_succ := by intro n x; rfl
```

## Duration is Now a Monoid

Duration is a registered AddMonoid. Any theorem or function
in Mathlib that works for an arbitrary AddMonoid now works
for Duration automatically. Let's verify a few properties.

```lean
#eval (one + zero : Duration)     -- one (right identity)
#eval (zero + two : Duration)     -- two (left identity)
#eval (one + one + one : Duration) -- zero (wraps around)

-- Associativity in action
#eval ((one + two) + two : Duration)   -- two
#eval (one + (two + two) : Duration)   -- two
```

## A Familiar Monoid: Nat under Addition

The natural numbers under addition with identity zero
form a monoid. Lean and Mathlib already know this, so
Nat already has an AddMonoid instance.

```lean
#check (inferInstance : AddMonoid Nat)
```

## Polymorphic Functions over Monoids

The real payoff of typeclasses is polymorphism. We can
write a function that works for *any* type that has an
AddMonoid instance. The instance argument in curly braces
acts as a type guard: calling the function on a type that
lacks the required instance is a compile-time error.

```lean
def addThree [AddMonoid α] (a b c : α) : α :=
  a + b + c

-- Works for Duration (our instance)
#eval addThree one two two          -- two

-- Works for Nat (Mathlib's instance)
#eval addThree 3 4 5                -- 12

-- Would NOT compile for a type without an AddMonoid instance:
-- #eval addThree "a" "b" "c"       -- error: no AddMonoid String
```

The `[AddMonoid α]` parameter is an *instance argument*.
Lean resolves it automatically by searching for a matching
typeclass instance. When we call `addThree one two two`,
Lean finds `AddMonoid Duration`. When we call `addThree 3 4 5`,
Lean finds `AddMonoid Nat`. One function definition, many
types — but only types whose algebraic structure has been
verified.

## Why Algebraic Structures Matter

Without algebraic structures, we'd have types, and we'd
have functions on those types, and nothing to connect the
two. We could define *myAdd* on Nat and have no assurance
that it's associative or that zero is its identity. A
bug in our implementation would go undetected.

An AddMonoid instance is not just a claim that a type has
addition and a zero — it is a *proof* that those operations
satisfy the monoid laws. Once we have such a proof, any
downstream code that relies on associativity or identity
can trust these properties unconditionally.

This is the shift from *testing* to *proving*. Tests check
finitely many cases. Proofs cover them all.

```lean
end Content.B02_ClassicalPropositionalLogic.chapters.monoid
```
