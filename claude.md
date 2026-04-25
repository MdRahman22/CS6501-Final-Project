# Lean 4 Formal Verification Workspace

## Project Purpose
Pedagogical materials for basic Lean 4: constructive propositional logic, constructive predicate logic, set theory, theory of relations

## Build Commands
- `lake build` — build all; this is your primary verification tool
- `lake build <Module>` — build one module for fast feedback
- `lake clean && lake build` — nuclear option for stale oleans
- `lake env printPaths` — debug import resolution issues

## The Core Loop
This is how you work on proofs in this codebase:
1. Read the file and understand the proof goal
2. Make a focused edit (one tactic step or one definition change)
3. Run `lake build <Module>` immediately
4. Read Lean's error output carefully — it tells you exactly what's wrong
5. Fix and repeat

Do NOT batch multiple proof changes before building. Lean's error messages
are your best tool — use them after every edit.

## Proof Strategy
- Start with the type signature; get it right before attempting the proof
- For complex proofs: stub with `sorry`, get the file compiling, then fill
- When filling `sorry`: work one at a time, innermost first
- If a proof resists 3 attempts: show me the goal state and I'll redirect
- Use `#check`, `#print`, and `#eval` liberally to explore

## Codebase Conventions
- ⟨id,id⟩ not Iff.rfl for membership lemmas
- Parenthesize ∈ᵣ in all positions
- `unfold` not `simp` for definitional unfolding
- `List.flatten` not `bind`/`join`
- `.symm` for equation direction
- No `sorry` in committed code, ever
- All documentation comment blocks use `/- @@@ ... @@@ -/` delimiters
- Prefer `n' + 1` over `Nat.succ n'` in pattern matches and expressions

## Common Pitfalls in This Codebase
- Universe level mismatches: check `universe` declarations first
- Instance diamonds: if typeclass resolution hangs, check for overlapping instances
- Module visibility: if a definition isn't found, check export/open statements
- Definitional equality: `rfl` failures often mean you need `unfold` first

## Safety Guardrails
- Never edit `lakefile.lean` or `lean-toolchain` without asking
- Always branch: `git checkout -b claude/<task-description>`
- Never `sorry` and commit — I will catch it in review
- When context compacts: preserve file paths, proof states, and error text