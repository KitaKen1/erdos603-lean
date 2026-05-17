# Lean Formalization of Erdős Problem 603

This repository contains a Lean formalization project for Erdős Problem 603.

## Overview

Erdős Problem 603 admits at least two natural readings.

- Interpretation 1: the countable-sequence reading.
- Interpretation 2: the arbitrary-size-family reading.

At present, this GitHub-facing repository contains only Interpretation 1.

For Interpretation 1, the repository includes both:

- a standard Lean/Lake version; and
- a standalone Lean4Web version.

The Lean4Web version is intended for copy-paste checking in Lean4Web with
Mathlib enabled.

## Sources

This formalization is based on:

- Przemek Chojecki's PDF solution/discussion of Erdős Problem 603:
  <https://www.ulam.ai/research/erdos603.pdf>
- the discussion of Problem 603 on the Erdős Problems forum:
  <https://www.erdosproblems.com/forum/thread/603>.

## Mathematical Content

The formalized statement for Interpretation 1 is:

If `A : ℕ → Set α` is a countable sequence of infinite sets, then there exists
a two-coloring `c : α → Bool` such that every `A n` contains points of both
colors.

In Lean, the main theorem is:

```lean
theorem Erdos603.CountableSequence.countable_family_two_colorable
    (A : ℕ → Set α) (hA : ∀ n, (A n).Infinite) :
    ∃ c : α → Bool, ∀ n, ContainsBothColors c (A n)
```

## Repository Layout

- `Erdos603CountableSequence/CountableSequence.lean`: the main Lean formalization for
  Interpretation 1.
- `Erdos603CountableSequence.lean`: the project entry point importing the main file.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: Lake project files
  for local checking.
- `Erdos603CountableSequenceLean4Web.lean`: a standalone Lean4Web-compatible
  version of the formalization.

## How to Check Locally

```bash
lake update
lake env lean Erdos603CountableSequence/CountableSequence.lean
lake env lean Erdos603CountableSequenceLean4Web.lean
lake build
```



## AI Assistance Disclosure

This formalization was developed with AI assistance.

The AI system used was **OpenAI Codex 5.5**, with reasoning effort
**`xhigh`**.


## References

- Erdős Problems, Problem 603 forum thread:
  <https://www.erdosproblems.com/forum/thread/603>
- Przemek Chojecki, PDF solution/discussion of Erdős Problem 603:
  <https://www.ulam.ai/research/erdos603.pdf>
- The Lean theorem prover:
  <https://lean-lang.org/>
- Mathlib, the Lean mathematical library:
  <https://github.com/leanprover-community/mathlib4>
- Lean4Web:
  <https://live.lean-lang.org/>
