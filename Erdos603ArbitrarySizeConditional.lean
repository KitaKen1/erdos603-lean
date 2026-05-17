import Erdos603ArbitrarySizeConditional.ConditionalConstruction

/-!
# Erdős Problem 603: arbitrary-size-family reading, conditional version

This Lean module is the entry point for the GitHub-facing conditional
formalization of the arbitrary-size-family interpretation of Erdős Problem 603.

It proves the PDF construction assuming the relevant Erdős--Rado/partition
input `ArrowOmegaTwo κ μ`, i.e. the input corresponding to `κ → (ω)^2_μ`.

References:

* Przemek Chojecki's PDF solution/discussion of Erdős Problem 603:
  https://www.ulam.ai/research/erdos603.pdf
* Erdős Problems forum thread 603:
  https://www.erdosproblems.com/forum/thread/603

AI assistance disclosure:

* This formalization was developed with assistance from OpenAI Codex 5.5,
  using reasoning effort `xhigh`.
-/
