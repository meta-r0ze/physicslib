import PMAction.Machine.EdgeLocality
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Controls for a whole finite configuration

`RootWordControls` realizes one edge's root word; `EdgeLocality` shows an edge's link depends only
on the controls along it. This module puts them together: a finite configuration of edges, each
with its own rates, is realized by one set of C² controls.

An `Edge` is a segment `y + [0, 1] v` with a functional `f` (`f v = 1`) and root rates `a`. Its
staggered controls (`RootWordControls.stagger`, offset `f y`) run only on the middle half
`mid e = y + [1/4, 3/4] v` (`RootWordControls.rate_outside`).

* `bump_exists`: if each edge's middle misses every other edge's segment, smooth Urysohn
  (`exists_contMDiffMap_zero_one_of_isClosed`) gives `χₑ`, C², equal to `1` on `mid e` and `0` on
  every other segment.
* `controls`: `Σₑ χₑ • staggerₑ`.
* `agree`: on edge `e`'s segment the sum equals `e`'s own staggered controls: other edges' terms
  vanish by their bumps, and `e`'s own term is either multiplied by `1` (middle half) or zero
  (outside it).
* `configuration_realized`: **every edge carries its own root word**
  `exp R₀ · (exp R₁ · (exp R₂ · exp R₃))` with its own rates, under one set of C² controls.

The hypothesis is geometric: an edge's middle half meets no other edge's segment. For distinct
lattice edges of `D₄` it holds (`D4EdgeSeparation.d4_disjoint`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.ConfigurationControls
open Matrix NativeCoherentLinks NativePacketUpdate RootWordControls Set
open scoped Matrix.Norms.L2Operator Manifold ContDiff

/-- An edge with its own root rates. -/
structure Edge where
  y : V
  v : V
  f : V →L[ℝ] ℝ
  hv : f v = 1
  a : Fin 4 → ℝ

/-- The edge's segment. -/
def seg (e : Edge) : Set V := (fun t : ℝ => e.y + t • e.v) '' Icc 0 1

/-- The middle half, where its roots run. -/
def mid (e : Edge) : Set V := (fun t : ℝ => e.y + t • e.v) '' Icc (1 / 4) (3 / 4)

lemma seg_compact (e : Edge) : IsCompact (seg e) := isCompact_Icc.image (by fun_prop)
lemma mid_compact (e : Edge) : IsCompact (mid e) := isCompact_Icc.image (by fun_prop)

/-- The root word an edge carries. -/
def word (c : Fin 3) (a : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  NormedSpace.exp (R c a 0) * (NormedSpace.exp (R c a 1) *
    (NormedSpace.exp (R c a 2) * NormedSpace.exp (R c a 3)))

/-- **A smooth bump separating an edge's middle from the other segments.** -/
lemma bump_exists {ι : Type*} [Fintype ι] (E : ι → Edge)
    (hdisj : ∀ e e', e ≠ e' → Disjoint (mid (E e)) (seg (E e'))) (e : ι) :
    ∃ χ : V → ℝ, ContDiff ℝ 2 χ ∧ EqOn χ 1 (mid (E e)) ∧
      ∀ e', e ≠ e' → EqOn χ 0 (seg (E e')) := by
  let F := ⋃ e' ∈ {e' : ι | e' ≠ e}, seg (E e')
  have hF : IsClosed F := (Set.toFinite _).isClosed_biUnion fun e' _ => (seg_compact _).isClosed
  have hd : Disjoint F (mid (E e)) := by
    rw [Set.disjoint_iUnion₂_left]
    exact fun e' he' => (hdisj e e' (Ne.symm he')).symm
  obtain ⟨χ, h0, h1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, V)) (n := ⊤)
    hF (mid_compact _).isClosed hd
  refine ⟨χ, ?_, h1, fun e' he' x hx => h0 (Set.mem_iUnion₂.2 ⟨e', Ne.symm he', hx⟩)⟩
  have h := contMDiff_iff_contDiff.1 χ.contMDiff
  simpa using contDiff_infty.1 h 2

/-- The configuration's controls. -/
def controls {ι : Type*} [Fintype ι] (E : ι → Edge) (χ : ι → V → ℝ) : Controls :=
  fun j x => ∑ e, χ e x • stagger (E e).f ((E e).f (E e).y) (E e).a j x

/-- **On an edge's segment, the configuration's controls are that edge's own.** -/
lemma agree {ι : Type*} [Fintype ι] (E : ι → Edge) (χ : ι → V → ℝ)
    (hone : ∀ e, EqOn (χ e) 1 (mid (E e))) (hzero : ∀ e e', e ≠ e' → EqOn (χ e) 0 (seg (E e')))
    (e : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : Fin 4) :
    controls E χ j ((E e).y + t • (E e).v) =
      stagger (E e).f ((E e).f (E e).y) (E e).a j ((E e).y + t • (E e).v) := by
  have hx : (E e).y + t • (E e).v ∈ seg (E e) := ⟨t, ht, rfl⟩
  unfold controls
  rw [Finset.sum_eq_single e]
  · by_cases hm : t ∈ Icc (1 / 4 : ℝ) (3 / 4)
    · rw [(hone e ⟨t, hm, rfl⟩ : χ e ((E e).y + t • (E e).v) = 1), Pi.one_apply, one_smul]
    · have ht' : (E e).f ((E e).y + t • (E e).v) - (E e).f (E e).y = t := by
        rw [map_add, map_smul, (E e).hv, smul_eq_mul]; ring
      have hg : g j t = 0 := by
        apply rate_outside
        simp only [mem_Icc, not_and_or, not_le] at hm
        rcases hm with h | h
        · left; linarith
        · right; linarith
      simp only [stagger]
      rw [ht', hg, mul_zero, zero_smul, smul_zero]
  · intro e' _ he'
    rw [(hzero e' e he' hx : χ e' ((E e).y + t • (E e).v) = 0), Pi.zero_apply, zero_smul]
  · intro h; exact absurd (Finset.mem_univ e) h

lemma packetA_congr (c : Fin 3) {w w' : Controls} (x v : V) (h : ∀ j, w j x = w' j x) :
    packetA c w x v = packetA c w' x v := by
  simp [packetA, form, h]

/-- **A finite configuration of root words is realized by C² controls.** -/
theorem configuration_realized {ι : Type*} [Fintype ι] (c : Fin 3) (E : ι → Edge)
    (hdisj : ∀ e e', e ≠ e' → Disjoint (mid (E e)) (seg (E e'))) :
    ∃ w : Controls, (∀ j, ContDiff ℝ 2 (w j)) ∧
      ∀ (r : Realization c w) (e : ι), r.packet (E e).y (E e).v 1 = word c (E e).a := by
  choose χ hχ hone hzero using bump_exists E hdisj
  refine ⟨controls E χ, fun j => by
    unfold controls
    exact ContDiff.sum fun e _ => (hχ e).smul (stagger_c2 _ _ _ j), fun r e => ?_⟩
  rw [EdgeLocality.edge_local c r (realized c _ (stagger_c2 (E e).f ((E e).f (E e).y) (E e).a))
    (E e).y (E e).v fun t ht => packetA_congr c _ _ fun j => agree E χ hone hzero e t ht j]
  exact root_word_link c _ _ _ _ _ _ (E e).hv rfl

end PMAction.ConfigurationControls
