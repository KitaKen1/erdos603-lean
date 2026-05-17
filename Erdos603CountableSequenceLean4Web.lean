import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic

/-!
# Erdős Problem 603: countable-sequence reading, Lean4Web version

Paste this whole file into Lean4Web with Mathlib enabled.

This is a standalone copy of the countable-sequence formalization.  It proves
the following PDF Proposition 6 reading:

References for the mathematical source:

* Przemek Chojecki's PDF solution/discussion of Erdős Problem 603:
  https://www.ulam.ai/research/erdos603.pdf
* Erdős Problems forum thread 603:
  https://www.erdosproblems.com/forum/thread/603

AI assistance disclosure:

* This formalization was developed with AI assistance.
* The AI system used was OpenAI Codex 5.5 with reasoning effort `xhigh`.

If `A : ℕ → Set α` is a countable sequence of infinite sets, then there is a
two-coloring `c : α → Bool` such that every `A n` contains both colors.
-/

open Classical
open Set

namespace Erdos603
namespace CountableSequence

variable {α : Type*}

/-- A set contains points of both Boolean colors. -/
def ContainsBothColors (c : α → Bool) (s : Set α) : Prop :=
  (∃ x ∈ s, c x = true) ∧ (∃ y ∈ s, c y = false)

/-- A finite set of all points used by a finite prefix of chosen pairs. -/
def usedPrefix [DecidableEq α] {n : ℕ} (p : Fin n → α × α) : Finset α :=
  ((Finset.univ : Finset (Fin n)).image fun i => (p i).1) ∪
    ((Finset.univ : Finset (Fin n)).image fun i => (p i).2)

lemma fst_mem_usedPrefix [DecidableEq α] {n : ℕ} (p : Fin n → α × α)
    (i : Fin n) :
    (p i).1 ∈ usedPrefix p := by
  classical
  simp [usedPrefix]

lemma snd_mem_usedPrefix [DecidableEq α] {n : ℕ} (p : Fin n → α × α)
    (i : Fin n) :
    (p i).2 ∈ usedPrefix p := by
  classical
  simp [usedPrefix]

/-- Choose two distinct points of an infinite set outside a prescribed finite set. -/
noncomputable def freshPair [DecidableEq α] (s : Set α) (hs : s.Infinite)
    (F : Finset α) : α × α :=
  let hx : ∃ x ∈ s, x ∉ F := hs.exists_notMem_finset F
  let x : α := Classical.choose hx
  let hy : ∃ y ∈ s, y ∉ insert x F := hs.exists_notMem_finset (insert x F)
  let y : α := Classical.choose hy
  (x, y)

lemma freshPair_fst_mem [DecidableEq α] (s : Set α) (hs : s.Infinite)
    (F : Finset α) :
    (freshPair s hs F).1 ∈ s := by
  classical
  unfold freshPair
  exact (Classical.choose_spec (hs.exists_notMem_finset F)).1

lemma freshPair_snd_mem [DecidableEq α] (s : Set α) (hs : s.Infinite)
    (F : Finset α) :
    (freshPair s hs F).2 ∈ s := by
  classical
  unfold freshPair
  let hx : ∃ x ∈ s, x ∉ F := hs.exists_notMem_finset F
  let x : α := Classical.choose hx
  let hy : ∃ y ∈ s, y ∉ insert x F := hs.exists_notMem_finset (insert x F)
  exact (Classical.choose_spec hy).1

lemma freshPair_ne [DecidableEq α] (s : Set α) (hs : s.Infinite)
    (F : Finset α) :
    (freshPair s hs F).1 ≠ (freshPair s hs F).2 := by
  classical
  unfold freshPair
  let hx : ∃ x ∈ s, x ∉ F := hs.exists_notMem_finset F
  let x : α := Classical.choose hx
  let hy : ∃ y ∈ s, y ∉ insert x F := hs.exists_notMem_finset (insert x F)
  have hy_not : Classical.choose hy ∉ insert x F := (Classical.choose_spec hy).2
  intro h
  dsimp at h
  exact hy_not (by
    simp only [Finset.mem_insert]
    exact Or.inl (by simpa [x, hx, hy] using h.symm))

lemma freshPair_fst_not_mem [DecidableEq α] (s : Set α) (hs : s.Infinite)
    (F : Finset α) :
    (freshPair s hs F).1 ∉ F := by
  classical
  unfold freshPair
  exact (Classical.choose_spec (hs.exists_notMem_finset F)).2

lemma freshPair_snd_not_mem [DecidableEq α] (s : Set α) (hs : s.Infinite)
    (F : Finset α) :
    (freshPair s hs F).2 ∉ F := by
  classical
  unfold freshPair
  let hx : ∃ x ∈ s, x ∉ F := hs.exists_notMem_finset F
  let x : α := Classical.choose hx
  let hy : ∃ y ∈ s, y ∉ insert x F := hs.exists_notMem_finset (insert x F)
  have hy_not : Classical.choose hy ∉ insert x F := (Classical.choose_spec hy).2
  intro hF
  exact hy_not (by
    simp only [Finset.mem_insert]
    exact Or.inr (by simpa [x, hx, hy] using hF))

/--
Finite-prefix version of the greedy construction.

For each `n`, it chooses pairs for the first `n` sets.  The successor step adds
a fresh pair for `A n`, avoiding all previously used points.
-/
noncomputable def greedyPrefix [DecidableEq α] (A : ℕ → Set α)
    (hA : ∀ n, (A n).Infinite) : (n : ℕ) → Fin n → α × α
  | 0 => Fin.elim0
  | n + 1 =>
      let prev := greedyPrefix A hA n
      let q := freshPair (A n) (hA n) (usedPrefix prev)
      fun i =>
        if h : (i : ℕ) < n then
          prev ⟨i, h⟩
        else
          q

/-- The pair chosen at its own stage. -/
noncomputable def chosenPair [DecidableEq α] (A : ℕ → Set α)
    (hA : ∀ n, (A n).Infinite) (n : ℕ) : α × α :=
  greedyPrefix A hA (n + 1) ⟨n, Nat.lt_succ_self n⟩

lemma chosenPair_fst_mem [DecidableEq α] (A : ℕ → Set α)
    (hA : ∀ n, (A n).Infinite) (n : ℕ) :
    (chosenPair A hA n).1 ∈ A n := by
  classical
  simp [chosenPair, greedyPrefix, freshPair_fst_mem]

lemma chosenPair_snd_mem [DecidableEq α] (A : ℕ → Set α)
    (hA : ∀ n, (A n).Infinite) (n : ℕ) :
    (chosenPair A hA n).2 ∈ A n := by
  classical
  simp [chosenPair, greedyPrefix, freshPair_snd_mem]

lemma chosenPair_ne [DecidableEq α] (A : ℕ → Set α)
    (hA : ∀ n, (A n).Infinite) (n : ℕ) :
    (chosenPair A hA n).1 ≠ (chosenPair A hA n).2 := by
  classical
  simp [chosenPair, greedyPrefix, freshPair_ne]

lemma greedyPrefix_eq_chosenPair_of_lt [DecidableEq α] (A : ℕ → Set α)
    (hA : ∀ n, (A n).Infinite) {m n : ℕ} (hmn : m < n) :
    greedyPrefix A hA n ⟨m, hmn⟩ = chosenPair A hA m := by
  classical
  induction n generalizing m with
  | zero =>
      exact (Nat.not_lt_zero m hmn).elim
  | succ n ih =>
      by_cases hm : m < n
      · have ih' := ih hm
        simp [greedyPrefix, chosenPair, hm] at ih' ⊢
        exact ih'
      · have hmn' : m = n := by
          exact Nat.le_antisymm (Nat.le_of_lt_succ hmn) (Nat.le_of_not_gt hm)
        subst m
        simp [chosenPair, greedyPrefix]

lemma chosenPair_fst_not_mem_previous [DecidableEq α] (A : ℕ → Set α)
    (hA : ∀ n, (A n).Infinite) (n : ℕ) :
    (chosenPair A hA n).1 ∉ usedPrefix (greedyPrefix A hA n) := by
  classical
  simp [chosenPair, greedyPrefix, freshPair_fst_not_mem]

lemma chosenPair_snd_not_mem_previous [DecidableEq α] (A : ℕ → Set α)
    (hA : ∀ n, (A n).Infinite) (n : ℕ) :
    (chosenPair A hA n).2 ∉ usedPrefix (greedyPrefix A hA n) := by
  classical
  simp [chosenPair, greedyPrefix, freshPair_snd_not_mem]

lemma chosenPair_cross_ne [DecidableEq α] (A : ℕ → Set α)
    (hA : ∀ n, (A n).Infinite) (m n : ℕ) :
    (chosenPair A hA m).1 ≠ (chosenPair A hA n).2 := by
  classical
  by_cases hmn : m < n
  · intro h
    have hmem : (chosenPair A hA m).1 ∈ usedPrefix (greedyPrefix A hA n) := by
      rw [← greedyPrefix_eq_chosenPair_of_lt A hA hmn]
      exact fst_mem_usedPrefix (greedyPrefix A hA n) ⟨m, hmn⟩
    have hnot := chosenPair_snd_not_mem_previous A hA n
    exact hnot (by simpa [h] using hmem)
  · by_cases hnm : n < m
    · intro h
      have hmem : (chosenPair A hA n).2 ∈ usedPrefix (greedyPrefix A hA m) := by
        rw [← greedyPrefix_eq_chosenPair_of_lt A hA hnm]
        exact snd_mem_usedPrefix (greedyPrefix A hA m) ⟨n, hnm⟩
      have hnot := chosenPair_fst_not_mem_previous A hA m
      exact hnot (by simpa [← h] using hmem)
    · have h_eq : m = n := by
        exact Nat.le_antisymm (Nat.le_of_not_gt hnm) (Nat.le_of_not_gt hmn)
      subst m
      exact chosenPair_ne A hA n

/--
If red witnesses and blue witnesses are globally disjoint, the final
two-coloring is immediate.
-/
theorem two_colorable_of_cross_ne [DecidableEq α]
    (A : ℕ → Set α) (hA : ∀ n, (A n).Infinite)
    (hcross : ∀ m n,
      (chosenPair A hA m).1 ≠ (chosenPair A hA n).2) :
    ∃ c : α → Bool, ∀ n, ContainsBothColors c (A n) := by
  classical
  let c : α → Bool := fun z =>
    if ∃ n, z = (chosenPair A hA n).1 then true else false
  refine ⟨c, fun n => ?_⟩
  constructor
  · refine ⟨(chosenPair A hA n).1, chosenPair_fst_mem A hA n, ?_⟩
    have hx : ∃ m, (chosenPair A hA n).1 = (chosenPair A hA m).1 := ⟨n, rfl⟩
    simp [c, hx]
  · refine ⟨(chosenPair A hA n).2, chosenPair_snd_mem A hA n, ?_⟩
    have hnot : ¬ ∃ m, (chosenPair A hA n).2 = (chosenPair A hA m).1 := by
      rintro ⟨m, hm⟩
      exact hcross m n hm.symm
    simp [c, hnot]

/--
Main theorem for the countable-sequence reading of Problem #603.

No intersection hypothesis is needed: every countable sequence of infinite sets
can be two-colored so that no member is monochromatic.
-/
theorem countable_family_two_colorable
    (A : ℕ → Set α) (hA : ∀ n, (A n).Infinite) :
    ∃ c : α → Bool, ∀ n, ContainsBothColors c (A n) := by
  classical
  exact two_colorable_of_cross_ne A hA (chosenPair_cross_ne A hA)

end CountableSequence
end Erdos603
