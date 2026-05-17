import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Sym.Card
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Erdős Problem 603: arbitrary-size-family reading, Lean4Web conditional version

Paste this whole file into Lean4Web with Mathlib enabled.

This is a standalone copy of the arbitrary-size-family construction from
Przemek Chojecki's PDF discussion of Erdős Problem 603, conditional on the
relevant partition-relation input.

Mathematical sources:

* Przemek Chojecki's PDF solution/discussion of Erdős Problem 603:
  https://www.ulam.ai/research/erdos603.pdf
* Erdős Problems forum thread 603:
  https://www.erdosproblems.com/forum/thread/603

AI assistance disclosure:

* This formalization was developed with assistance from OpenAI Codex 5.5,
  using reasoning effort `xhigh`.

The partition-relation input is represented by `ArrowOmegaTwo κ μ`: every
`μ`-coloring of unordered non-diagonal pairs from `κ` has a countably infinite
monochromatic complete subgraph.  This is the role played by the
Erdős--Rado/partition relation `κ → (ω)^2_μ` in the PDF argument.

Under that hypothesis, the construction takes the ground set to be unordered
pairs of vertices and takes the family members to be the complete edge sets
`[X]^2` for countably infinite `X`.
-/

open Classical
open Set
open scoped Sym2

namespace Erdos603
namespace ArbitrarySizeConditional

universe u

variable {κ μ : Type u}

/-- A set is countably infinite. -/
def CountablyInfinite (s : Set κ) : Prop :=
  s.Countable ∧ s.Infinite

/-- A subset is monochromatic for a point-coloring. -/
def SetMonochromatic {α χ : Type u} (c : α → χ) (E : Set α) : Prop :=
  ∃ color : χ, ∀ x ∈ E, c x = color

/--
The unordered non-diagonal pairs from a vertex set `X`.

This is the Lean version of `[X]^2`.
-/
def completeEdges (X : Set κ) : Set (Sym2 κ) :=
  X.sym2 ∩ Sym2.diagSetᶜ

/-- A set of edges is monochromatic for a coloring `c`. -/
def Monochromatic (c : Sym2 κ → μ) (E : Set (Sym2 κ)) : Prop :=
  SetMonochromatic c E

/--
Partition-relation input: every `μ`-coloring of unordered pairs from `κ` has a
countably infinite monochromatic complete subgraph.

This packages the role played by the Erdős--Rado/partition input
`κ → (ω)^2_μ` in the PDF argument.
-/
def ArrowOmegaTwo (κ μ : Type u) : Prop :=
  ∀ c : Sym2 κ → μ,
    ∃ H : Set κ, CountablyInfinite H ∧ Monochromatic c (completeEdges H)

/-- The family `{[X]^2 : X ⊆ κ, X countably infinite}`. -/
def erdosFamily (κ : Type u) : Set (Set (Sym2 κ)) :=
  {E | ∃ X : Set κ, CountablyInfinite X ∧ E = completeEdges X}

/--
The counterexample package promised by the arbitrary-size-family reading of
Problem 603, for a fixed vertex type `κ` and color type `μ`.

The ground set is `Sym2 κ`, i.e. unordered pairs of vertices.  The package asks
for a family of countably infinite subsets whose pairwise intersections never
have size `2`, while every `μ`-coloring has a monochromatic member.
-/
def Erdos603Counterexample (κ μ : Type u) : Prop :=
  ∃ A : Set (Set (Sym2 κ)),
    (∀ E ∈ A, E.Countable ∧ E.Infinite) ∧
    (∀ E ∈ A, ∀ F ∈ A, (E ∩ F).encard ≠ 2) ∧
    (∀ c : Sym2 κ → μ, ∃ E ∈ A, Monochromatic c E)

/--
A color type `χ` is universal for the arbitrary-size-family reading if every
valid family admits a `χ`-coloring with no monochromatic member.

The PDF's negative conclusion is that no such universal color type exists.
-/
def UniversalColorCardinal (χ : Type u) : Prop :=
  ∀ (α : Type u) (A : Set (Set α)),
    (∀ E ∈ A, E.Countable ∧ E.Infinite) →
    (∀ E ∈ A, ∀ F ∈ A, (E ∩ F).encard ≠ 2) →
    ∃ c : α → χ, ∀ E ∈ A, ¬ SetMonochromatic c E

lemma completeEdges_subset_sym2 (X : Set κ) :
    completeEdges X ⊆ X.sym2 := by
  intro e he
  exact he.1

lemma countable_sym2 {X : Set κ} (hX : X.Countable) :
    X.sym2.Countable := by
  simpa [Set.sym2_eq_mk_image] using
    ((hX.prod hX).image (fun p : κ × κ => Sym2.mk p.1 p.2))

lemma completeEdges_countable {X : Set κ} (hX : X.Countable) :
    (completeEdges X).Countable :=
  Set.Countable.mono (completeEdges_subset_sym2 X) (countable_sym2 hX)

lemma completeEdges_infinite {X : Set κ} (hX : X.Infinite) :
    (completeEdges X).Infinite := by
  classical
  obtain ⟨a, ha⟩ := hX.nonempty
  let f : κ → Sym2 κ := fun b => Sym2.mk a b
  have hdomain : (X \ {a}).Infinite := hX.diff (finite_singleton a)
  refine infinite_of_injOn_mapsTo
    (s := X \ {a}) (t := completeEdges X) (f := f) ?hinj ?hmaps hdomain
  · intro b hb c hc hbc
    exact (Sym2.mkEmbedding a).injective hbc
  · intro b hb
    have hbX : b ∈ X := hb.1
    have hbne : b ≠ a := by
      intro h
      exact hb.2 (by simp [h])
    constructor
    · simp [f, ha, hbX]
    · simp [f, Sym2.mk_isDiag_iff, hbne.symm]

lemma completeEdges_countablyInfinite {X : Set κ}
    (hX : CountablyInfinite X) :
    (completeEdges X).Countable ∧ (completeEdges X).Infinite :=
  ⟨completeEdges_countable hX.1, completeEdges_infinite hX.2⟩

lemma completeEdges_inter (X Y : Set κ) :
    completeEdges X ∩ completeEdges Y = completeEdges (X ∩ Y) := by
  ext e
  simp [completeEdges, Set.sym2_inter, and_left_comm, and_assoc]

lemma completeEdges_eq_finset_offDiag_image {S : Set κ} (hS : S.Finite) :
    completeEdges S =
      (↑(hS.toFinset.offDiag.image Sym2.mk.uncurry) : Set (Sym2 κ)) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
      simp only [completeEdges, Set.mem_inter_iff, Set.mk_mem_sym2_iff,
        Set.mem_compl_iff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff,
        Finset.mem_coe, Finset.mem_image, Finset.mem_offDiag]
      constructor
      · rintro ⟨⟨ha, hb⟩, hne⟩
        exact ⟨(a, b), ⟨by simpa using ha, by simpa using hb, hne⟩, rfl⟩
      · rintro ⟨⟨a', b'⟩, ⟨ha', hb', hne'⟩, heq⟩
        change Sym2.mk a' b' = Sym2.mk a b at heq
        simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
        rcases heq with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨by simpa using ha', by simpa using hb'⟩, hne'⟩
        · exact ⟨⟨by simpa using hb', by simpa using ha'⟩, fun h => hne' h.symm⟩

lemma nat_choose_two_ne_two (n : ℕ) :
    n.choose 2 ≠ 2 := by
  rcases n with _ | n
  · norm_num
  rcases n with _ | n
  · norm_num
  rcases n with _ | n
  · norm_num
  rcases n with _ | n
  · norm_num
  have hle : 6 ≤ (Nat.choose (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))) 2) := by
    calc
      6 = Nat.choose 4 2 := by norm_num [Nat.choose]
      _ ≤ Nat.choose (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))) 2 :=
        Nat.choose_le_choose 2 (by omega)
  exact ne_of_gt ((by norm_num : 2 < 6).trans_le hle)

lemma completeEdges_encard_ne_two (S : Set κ) :
    (completeEdges S).encard ≠ 2 := by
  classical
  by_cases hSinf : S.Infinite
  · rw [(completeEdges_infinite hSinf).encard_eq]
    norm_num
  · have hSfin : S.Finite := Set.not_infinite.mp hSinf
    rw [completeEdges_eq_finset_offDiag_image hSfin]
    rw [Set.encard_coe_eq_coe_finsetCard]
    rw [Sym2.card_image_offDiag]
    exact_mod_cast nat_choose_two_ne_two hSfin.toFinset.card

lemma erdosFamily_members_countablyInfinite
    {E : Set (Sym2 κ)} (hE : E ∈ erdosFamily κ) :
    E.Countable ∧ E.Infinite := by
  rcases hE with ⟨X, hX, rfl⟩
  exact completeEdges_countablyInfinite hX

lemma erdosFamily_intersection_ne_two
    {E F : Set (Sym2 κ)} (hE : E ∈ erdosFamily κ)
    (hF : F ∈ erdosFamily κ) :
    (E ∩ F).encard ≠ 2 := by
  rcases hE with ⟨X, _hX, rfl⟩
  rcases hF with ⟨Y, _hY, rfl⟩
  rw [completeEdges_inter]
  exact completeEdges_encard_ne_two (X ∩ Y)

lemma arrow_gives_monochromatic_member
    (hpart : ArrowOmegaTwo κ μ) (c : Sym2 κ → μ) :
    ∃ E ∈ erdosFamily κ, Monochromatic c E := by
  rcases hpart c with ⟨H, hH, hmono⟩
  exact ⟨completeEdges H, ⟨H, hH, rfl⟩, hmono⟩

/--
Conditional counterexample package.

If `κ` has the partition property `ArrowOmegaTwo κ μ`, then the PDF family
`{[X]^2 : X countably infinite}` has countably infinite members, pairwise
intersections never of size `2`, and every `μ`-coloring has a monochromatic
member.
-/
theorem arbitrary_size_counterexample_conditional
    (hpart : ArrowOmegaTwo κ μ) :
    Erdos603Counterexample κ μ := by
  refine ⟨erdosFamily κ, ?_, ?_, ?_⟩
  · intro E hE
    exact erdosFamily_members_countablyInfinite hE
  · intro E hE F hF
    exact erdosFamily_intersection_ne_two hE hF
  · intro c
    exact arrow_gives_monochromatic_member hpart c

/--
Same theorem with a name emphasizing the mathematical role of the hypothesis:
assuming the Erdős--Rado/partition input `κ → (ω)^2_μ`, the arbitrary-size
family counterexample follows.

Lean note: this theorem has the explicit hypothesis `hER : ArrowOmegaTwo κ μ`.
`#print axioms` checks undeclared axiom dependencies, but it does not list
ordinary theorem hypotheses.
-/
theorem arbitrary_size_counterexample_from_erdos_rado
    (hER : ArrowOmegaTwo κ μ) :
    Erdos603Counterexample κ μ :=
  arbitrary_size_counterexample_conditional hER

/--
Any fixed counterexample package refutes the claim that `μ` is a universal
color type for the arbitrary-size-family reading.
-/
theorem Erdos603Counterexample.not_universalColorCardinal
    (hcounter : Erdos603Counterexample κ μ) :
    ¬ UniversalColorCardinal μ := by
  rintro huniversal
  rcases hcounter with ⟨A, hmembers, hintersections, hmono_all⟩
  rcases huniversal (Sym2 κ) A hmembers hintersections with ⟨c, havoid⟩
  rcases hmono_all c with ⟨E, hEA, hmono⟩
  exact havoid E hEA hmono

/--
Final conditional negative conclusion.

If the Erdős--Rado/partition input `κ → (ω)^2_μ` is available for every color
type `μ`, then there is no universal color cardinal for the arbitrary-size
family reading.  This is stronger than saying that no smallest such cardinal
exists.

This theorem is still conditional: the hypothesis `hER_all` is the
Erdős--Rado/partition input for all color types.
-/
theorem no_universal_color_cardinal_of_erdos_rado
    (hER_all : ∀ χ : Type u, ∃ κ : Type u, ArrowOmegaTwo κ χ) :
    ¬ ∃ χ : Type u, UniversalColorCardinal χ := by
  rintro ⟨χ, huniversal⟩
  rcases hER_all χ with ⟨κ, hER⟩
  exact
    (arbitrary_size_counterexample_from_erdos_rado
      (κ := κ) (μ := χ) hER).not_universalColorCardinal huniversal

/-!
## How to read the Lean check

In Lean4Web, the following commands are useful for distinguishing an
unconditional proof from a conditional theorem.

`#check` prints the theorem statement.  Here it shows that the theorem still
has the explicit hypothesis `ArrowOmegaTwo κ μ`, so this is a conditional
formalization of the PDF construction, not a complete proof of Erdős--Rado.

`#print axioms` prints undeclared axiom dependencies.  It does not print
ordinary theorem hypotheses, so it must be read together with `#check`.
-/

#check Erdos603.ArbitrarySizeConditional.arbitrary_size_counterexample_from_erdos_rado

#print axioms Erdos603.ArbitrarySizeConditional.arbitrary_size_counterexample_from_erdos_rado

#check Erdos603.ArbitrarySizeConditional.no_universal_color_cardinal_of_erdos_rado

#print axioms Erdos603.ArbitrarySizeConditional.no_universal_color_cardinal_of_erdos_rado

end ArbitrarySizeConditional
end Erdos603
