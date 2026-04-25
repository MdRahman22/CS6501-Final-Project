/- @@@
# Equivalence: Pairs of Functions

<!-- toc -->

The biconditional P ↔ Q asserts that P implies Q *and*
Q implies P. In our type-theoretic encoding, this is a
pair of functions: one from P to Q and one from Q to P.
That is, P ↔ Q is represented as (P → Q) × (Q → P).

## Introduction: Proving an Equivalence

To prove P ↔ Q, provide two functions: one that converts
any proof of P into a proof of Q, and one that converts
any proof of Q into a proof of P.
@@@ -/

import Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C00_introduction

namespace Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C05_equivalence

open Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C00_introduction

/- @@@
### A Type for Equivalence

We define Equiv as a product of two implications.
@@@ -/

abbrev Equiv (α β : Type) := (α → β) × (β → α)

/- @@@
SkyBlue and EarthGreen are equivalent in the sense
that each has a proof, so we can convert between them.
@@@ -/

def skyEarthEquiv : Equiv SkyBlue EarthGreen :=
  ⟨ fun _ => EarthGreen.intro, fun _ => SkyBlue.intro ⟩

/- @@@
## Elimination: Extracting Implications

Given a proof of P ↔ Q, we can extract either direction.
The first projection gives us P → Q (the "forward" direction),
and the second gives us Q → P (the "backward" direction).
@@@ -/

def equivForward : Equiv SkyBlue EarthGreen → (SkyBlue → EarthGreen)
| pf => pf.1

def equivBackward : Equiv SkyBlue EarthGreen → (EarthGreen → SkyBlue)
| pf => pf.2

/- @@@
## Symmetry of Equivalence

If P ↔ Q then Q ↔ P. We just swap the two components
of the pair.
@@@ -/

def equivSymm {α β : Type} : Equiv α β → Equiv β α
| ⟨ forward, backward ⟩ => ⟨ backward, forward ⟩

/- @@@
## Reflexivity and Transitivity

Every proposition is equivalent to itself (reflexivity).
And if P ↔ Q and Q ↔ R, then P ↔ R (transitivity) —
by composing the forward and backward functions.
@@@ -/

def equivRefl (α : Type) : Equiv α α :=
  ⟨ id, id ⟩

def equivTrans {α β γ : Type} : Equiv α β → Equiv β γ → Equiv α γ
| ⟨ ab, ba ⟩, ⟨ bc, cb ⟩ => ⟨ fun a => bc (ab a), fun c => ba (cb c) ⟩

end Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C05_equivalence
