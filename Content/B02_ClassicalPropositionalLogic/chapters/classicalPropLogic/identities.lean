import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.syntax
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.properties

namespace Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.identities

open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.properties

def P := {⟨0⟩}
def Q := {⟨1⟩}
def R := {⟨2⟩}

def andIdempotent   := P ↔ (P ∧ P)
def orIdempotent    := P ↔ (P ∨ P)

def andCommutative  := (P ∧ Q) ↔ (Q ∧ P)
def orCommutative   := (P ∨ Q) ↔ (Q ∨ P)

def identityAnd     := (P ∧ ⊤) ↔ P
def identityOr      := (P ∨ ⊥) ↔ P

def annihilateAnd    := (P ∧ ⊥) ↔ ⊥
def annihilateOr     := (P ∨ ⊤) ↔ ⊤

def orAssociative   := ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R))
def andAssociative  := ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R))

def equivalence     := (P ↔ Q) ↔ ((P ⇒ Q) ∧ (Q ⇒ P))
def implication     := (P ⇒ Q) ↔ (¬P ∨ Q)
def exportation     := ((P ∧ Q) ⇒ R) ↔ (P ⇒ Q ⇒ R)
def absurdity       := (P ⇒ Q) ∧ (P ⇒ ¬Q) ⇒ ¬P

-- Distributive laws
def distribAndOr    := (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R))
def distribOrAnd    := (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R))

-- DeMorgan's laws
def deMorganAnd     := ¬(P ∧ Q) ↔ (¬P ∨ ¬ Q)
def deMorganOr      := ¬(P ∨ Q) ↔ (¬P ∧ ¬ Q)

-- Validate all identities
#eval is_valid andIdempotent    -- true
#eval is_valid orIdempotent     -- true
#eval is_valid andCommutative   -- true
#eval is_valid orCommutative    -- true
#eval is_valid identityAnd      -- true
#eval is_valid identityOr       -- true
#eval is_valid annihilateAnd    -- true
#eval is_valid annihilateOr     -- true
#eval is_valid orAssociative    -- true
#eval is_valid andAssociative   -- true
#eval is_valid equivalence      -- true
#eval is_valid implication      -- true
#eval is_valid exportation      -- true
#eval is_valid absurdity        -- true
#eval is_valid distribAndOr     -- true
#eval is_valid distribOrAnd     -- true
#eval is_valid deMorganAnd      -- true
#eval is_valid deMorganOr       -- true

end Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.identities
