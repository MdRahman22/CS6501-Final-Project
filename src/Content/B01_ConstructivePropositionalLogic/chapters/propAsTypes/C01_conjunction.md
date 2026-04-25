# Conjunction: Product Types

<!-- toc -->

To express "the sky is blue *and* the earth is green"
we need a type whose values require proofs of *both*
conjuncts. A product type does exactly this: its single
constructor takes two arguments.

## Introduction: Constructing a Conjunction

To prove a conjunction, provide proofs of both parts.

```lean
import Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C00_introduction

namespace Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C01_conjunction

open Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C00_introduction
```

### A Hand-Crafted Conjunction Type

We can define our own conjunction type with a single
constructor that demands both proofs.

```lean
-- A hand-crafted conjunction type
inductive SkyBlueAndEarthGreen : Type where
| intro : SkyBlue → EarthGreen → SkyBlueAndEarthGreen

inductive EarthGreenAndSkyBlue where
| intro : EarthGreen → SkyBlue → EarthGreenAndSkyBlue

-- Constructing a proof of the conjunction
def pfBoth := SkyBlueAndEarthGreen.intro SkyBlue.intro EarthGreen.intro
```

## Elimination: Extracting Conjuncts

If P ∧ Q is true, then P is true and Q is true. In
type-theoretic terms: from a value of the conjunction
type we can extract a value of either conjunct type.
These extractions are *implications* — function types —
and their proofs are functions.

```lean
def conjToSkyBlue : EarthGreenAndSkyBlue → SkyBlue
| ⟨ _, pfsb ⟩ => pfsb

def conjToEarthGreen : EarthGreenAndSkyBlue → EarthGreen
| ⟨ pfeg, _ ⟩ => pfeg
```

## Commutativity of Conjunction

A proof of P ∧ Q can always be converted to a proof
of Q ∧ P, and vice versa. As a programming matter,
it's just swapping the elements of a pair.

```lean
def andForward : EarthGreenAndSkyBlue → SkyBlueAndEarthGreen
| EarthGreenAndSkyBlue.intro eg sb => ⟨ sb, eg ⟩

def andReverse : SkyBlueAndEarthGreen → EarthGreenAndSkyBlue
| pf => ⟨ pf.2, pf.1 ⟩
```

## Using Lean's Prod Type

Our hand-crafted conjunction types are just specialized
product types. Lean provides *Prod* (with notation ×)
as a general-purpose polymorphic product. We can use it
directly: *SkyBlue × EarthGreen* is the conjunction.

```lean
def pfProd : SkyBlue × EarthGreen := ⟨ SkyBlue.intro, EarthGreen.intro ⟩
```

### Elimination via Projection

The first and second projections extract the left and
right conjuncts from a product value.

```lean
def prodLeft : SkyBlue × EarthGreen → SkyBlue
| pr => pr.1

def prodRight : SkyBlue × EarthGreen → EarthGreen
| pr => pr.2
```

### Commutativity via Prod

```lean
def prodComm : SkyBlue × EarthGreen → EarthGreen × SkyBlue
| ⟨ sb, eg ⟩ => ⟨ eg, sb ⟩

end Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C01_conjunction
```
