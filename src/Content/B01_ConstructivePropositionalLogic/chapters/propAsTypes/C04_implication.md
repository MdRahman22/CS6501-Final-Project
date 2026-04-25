# Implication: Function Types

<!-- toc -->

The implication P → Q is represented by the function
type from P to Q. A proof of P → Q is a function that
transforms any proof of P into a proof of Q.

## Introduction: Defining a Function

To prove P → Q, define a function from P to Q. The
function body explains how to turn any proof of P
into a proof of Q.

## Elimination: Applying a Function (Modus Ponens)

Given a proof of P → Q and a proof of P, applying the
function yields a proof of Q. This is modus ponens —
the most fundamental rule of deduction — realized as
function application.

## The Four Cases

We can verify the classical truth table for implies
using our propositions. We have true propositions
(SkyBlue, EarthGreen) and a false one (WaterDry).

- false → false is true
- false → true is true
- true → false is false
- true → true is true

```lean
import Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C00_introduction
import Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C03_falsity_negation

namespace Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C04_implication

open Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C00_introduction
open Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C03_falsity_negation

-- false → false: from WaterDry we can derive anything
def falseToFalse : WaterDry → Empty
| wd => nomatch wd

-- false → true: from WaterDry we can certainly get EarthGreen
def falseToTrue : WaterDry → EarthGreen
| _ => EarthGreen.intro

-- true → false: IMPOSSIBLE — we cannot define this function
-- def trueToFalse : EarthGreen → WaterDry
-- | eg => ???   -- no constructor for WaterDry exists

-- true → true: trivial
def trueToTrue : EarthGreen → SkyBlue
| _ => SkyBlue.intro

end Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C04_implication
```
