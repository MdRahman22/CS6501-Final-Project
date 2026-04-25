#### Low-level bit vector routines

```lean
namespace Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.utilities
```

Converting natural number indices to corresponding rows of
truth tables for any given v, a number of variables.

```lean
--
abbrev Bit := Bool
abbrev Binary := List Bit

-- rightmost bit in binary representation of given natural number, n
def rightBit (n : Nat) := n%2

-- dividing n by 2 discards rightmost bit in binary representation of n
def shiftRight (n : Nat) := n/2

-- Given nat n return its binary expansion as a list Bool
def BitFromNat (n : Nat) := if n= 0 then false else true

-- convert natural number to corresponding list of bits (nat, 0 or 1)
def binaryFromNat : Nat → Binary
| 0     => [false]
| 1     => [true]
| n' + 2 =>
  have : (shiftRight (n' + 2)) < (n' + 2) := by unfold shiftRight; omega
  (binaryFromNat (shiftRight (n' + 2))) ++ [(BitFromNat (rightBit (n' + 2)))]
```

Left pad list of nats with zeros
Todo: Clarify bits vs nats
```lean
def zeroPadListLeft : Binary → Nat → Binary
  | l, n => zero_pad_recursive (n - (l.length)) l
where zero_pad_recursive : Nat → Binary → Binary
  | 0, l => l
  | n'+1, l => zero_pad_recursive n' (false::l)
```

Make bit list at index "row" zero padded "cols" wide
```lean
def binaryFromRowCols : (row : Nat) → (cols: Nat) → Binary
| r, c => zeroPadListLeft (binaryFromNat r) c
```

Make row'th row of truth table with vars variable columns
```lean
def listBoolFromRowIndexForNumVars : (row : Nat) → (vars : Nat) → List Bool
| index, cols => (binaryFromRowCols index cols)


-- functions to check if bool list has any, resp. all, values true
def reduce_or : List Bool → Bool
| [] => false
| h::t => or h (reduce_or t)

def reduce_and : List Bool → Bool
| [] => true
| h::t => and h (reduce_and t)
```

The indexFirstTrue function returns an option:
either (some "index of the first true value in
the list"), or "none" if there is no such value.

```lean
def indexFirstTrue : List Bool → Option Nat
    | bs => foo bs bs.length
where foo : List Bool → Nat → Option Nat
    | [], _ => none
    | b::bs, len =>
        if b then
          /-current index-/
          some (len-(b::bs).length)
        else
          /-search rest-/
          foo bs len

end Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.utilities
```
