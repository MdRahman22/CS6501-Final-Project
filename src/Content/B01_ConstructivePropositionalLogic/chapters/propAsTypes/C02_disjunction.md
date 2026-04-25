# Disjunction: Sum Types

<!-- toc -->

A proof of P ∨ Q requires a proof of *either* P or Q
(not necessarily both). The Sum type (notation ⊕) has
two constructors, *inl* and *inr*, corresponding to
the two ways of proving a disjunction.

## Introduction: Two Ways to Prove a Disjunction

To prove P ∨ Q, provide a proof of P (using *inl*)
or a proof of Q (using *inr*). Each constructor is
an introduction rule.

```lean
import Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C00_introduction

namespace Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C02_disjunction

open Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C00_introduction

-- Two different proofs of EarthGreen ∨ SkyBlue
def orProof1 : EarthGreen ⊕ SkyBlue := Sum.inl pfEarthGreen
def orProof2 : EarthGreen ⊕ SkyBlue := Sum.inr pfSkyBlue
```

## Elimination: Case Analysis

To use a proof of P ∨ Q, you must handle both cases:
show the conclusion follows from P, and show it follows
from Q. This is case analysis — pattern matching on
which constructor was used.

## Commutativity of Disjunction

A proof of P ∨ Q can be converted to a proof of Q ∨ P
by swapping the injection side.

```lean
def orComm : EarthGreen ⊕ SkyBlue → SkyBlue ⊕ EarthGreen
| Sum.inl eg => Sum.inr eg
| Sum.inr sb => Sum.inl sb

end Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C02_disjunction
```
