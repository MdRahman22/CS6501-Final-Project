# Alpha: Discrete Mathematics in Type Theory
## A Lean 4 Course in Constructive Logic

### Overview

Alpha is a series of interactive textbooks teaching logic and discrete 
mathematics through the Curry-Howard correspondence in Lean 4. Students 
learn mathematical reasoning by writing programs that are mechanically 
verified proofs.

### Book Sequence

| Book | Title | Content |
|------|-------|---------|
| **Book 1** | Constructive Propositional Logic | ∧, ∨, →, ↔, ¬, True, False |
| **Book 2** | Constructive Predicate Logic | ∀, ∃, =, induction |
| **Optional** | Propositional Logic: A Deep Embedding | Syntax, semantics, SAT |

### The Curry-Howard Correspondence

The central insight of this course is the **Curry-Howard correspondence**:

| Logic | Programming |
|-------|-------------|
| Propositions | Types |
| Proofs | Programs |
| Proving P | Constructing a value of type P |
| P → Q | Function type P → Q |
| P ∧ Q | Product type P × Q |
| P ∨ Q | Sum type P ⊕ Q |

When you write a proof in this course, you're writing a program. When 
Lean type-checks your code, it's verifying your proof is correct.

### Directory Structure

```
Alpha/
├── book.lean                 -- Main entry point
├── book1.lean                -- Book 1 entry
├── book1lib/
│   ├── chapters/             -- 12 chapters
│   ├── homework/             -- 5 assignments
│   ├── diagrams/             -- Inference rule PDFs
│   └── README.md
│
├── book2.lean                -- Book 2 entry
├── book2lib/
│   ├── chapters/             -- (under development)
│   └── README.md
│
├── book3lib.lean   -- Optional module entry
└── book3lib/
    ├── library/              -- Implementation files
    └── README.md
```

### Getting Started

1. Install Lean 4 and set up your editor (VS Code recommended)
2. Clone this repository
3. Open `book1lib/chapters/C00_introduction.lean`
4. Work through the chapters in order

### Prerequisites

- Basic programming experience (functions, types, variables)
- No prior logic or proof experience required

### Constructive vs Classical Logic

This course teaches **constructive** (intuitionistic) logic:

- To prove P ∨ Q, you must prove P or prove Q (and say which)
- To prove ∃x, P(x), you must exhibit a specific witness
- The law of excluded middle (P ∨ ¬P) is not assumed

This is more restrictive than classical logic but produces more 
informative proofs—existence proofs always give witnesses.

### Course Sequence Recommendation

**Full Semester:**
1. Book 1: Constructive Propositional Logic (5-6 weeks)
2. Book 2: Constructive Predicate Logic (5-6 weeks)
3. Optional: Deep Embedding project (2-3 weeks)

**Half Semester:**
- Book 1 only

**Programming-Focused Variant:**
- Book 1 + Deep Embedding module

### License

[Your license here]

### Acknowledgments

- Inspired by the Curry-Howard correspondence
- Built on Lean 4 and Mathlib
