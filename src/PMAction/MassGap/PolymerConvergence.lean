import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Convergence of the polymer expansion (Dobrushin's criterion)

`ContourCount` proves the volume-independent counting and the Kotecký–Preiss smallness condition.
This file proves the convergence statement that the condition feeds. It is stated for a polymer
gas with **real activities of either sign**, which is what a Duhamel/Dyson expansion of an
off-diagonal (quantum) term produces.

Setting: a finite set `P` of polymers (contours), a symmetric incompatibility relation `inc`
(two contours that overlap or touch), and activities `w : P → ℝ`. The partition function of a
set `S` of allowed polymers is the sum over pairwise-compatible subfamilies:
`Z S = Σ_{I ⊆ S independent} Π_{γ∈I} w γ`.

* `Z_empty`, `Z_recursion`: `Z ∅ = 1` and, for `γ ∈ S`,
  `Z S = Z (S − γ) + w γ · Z (polymers of S − γ compatible with γ)` (deletion recursion).
* `dobrushin`: **Dobrushin's criterion.** If there are `x γ ∈ [0,1)` with
  `|w γ| ≤ x γ · Π_{γ' incompatible with γ, γ' ≠ γ} (1 − x γ')`, then for **every** `S`:
  `Z S > 0`, and for every `γ ∈ S`,
  `(1 − x γ) · Z (S − γ) ≤ Z S ≤ (1 + x γ) · Z (S − γ)`.
* `Z_lower`, `Z_upper`: consequently `Π_{γ∈S} (1 − x γ) ≤ Z S ≤ Π_{γ∈S} (1 + x γ)`. The free
  energy `log Z` is a sum of local terms, each bounded by a constant set by its own polymer.
* `prod_one_sub_ge`: the Weierstrass product inequality `Π (1 − x_i) ≥ 1 − Σ x_i`, the tool for
  checking the criterion from a summed (Kotecký–Preiss-type) bound such as
  `ContourCount.kotecky_preiss_condition`.

None of these constants depends on the number of polymers, so all bounds are uniform in the
volume.

## What is not here

The criterion gives a positive partition function and local ratio bounds. A mass gap also needs
the ratio `Z S / Z (S − γ)` to depend only exponentially weakly on polymers far from `γ`
(decay of correlations). That is the next step: the deletion recursion is a contraction under
the same criterion. Also still open: turning ratio decay into a transfer-matrix gap, and the
geometric bridge that derives the criterion's hypothesis from `ContourCount`.
-/

namespace PMAction.MassGap.PolymerConvergence
open Finset

variable {P : Type*} [DecidableEq P] (inc : P → P → Prop) [DecidableRel inc] (w : P → ℝ)

/-- A family of pairwise-compatible polymers. -/
def Independent (I : Finset P) : Prop := ∀ a ∈ I, ∀ b ∈ I, a ≠ b → ¬ inc a b

instance (I : Finset P) : Decidable (Independent inc I) := by
  unfold Independent; infer_instance

/-- Polymer partition function of the allowed set `S`. -/
def Z (S : Finset P) : ℝ :=
  ∑ I ∈ S.powerset.filter (Independent inc), ∏ γ ∈ I, w γ

/-- The polymers of `S` other than `γ` that are compatible with `γ`. -/
def compat (S : Finset P) (γ : P) : Finset P := (S.erase γ).filter fun b => ¬ inc γ b

theorem Z_empty : Z inc w ∅ = 1 := by
  have h : Independent inc (∅ : Finset P) := by simp [Independent]
  unfold Z
  rw [powerset_empty, filter_singleton]
  simp only [h, ite_true]
  simp

omit [DecidableRel inc] in
lemma independent_insert (hsymm : ∀ a b, inc a b → inc b a) {γ : P} {J : Finset P}
    (hγ : γ ∉ J) :
    Independent inc (insert γ J) ↔ Independent inc J ∧ ∀ b ∈ J, ¬ inc γ b := by
  constructor
  · intro h
    refine ⟨fun a ha b hb hab => h a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab,
      fun b hb => h γ (mem_insert_self γ J) b (mem_insert_of_mem hb) ?_⟩
    rintro rfl; exact hγ hb
  · rintro ⟨hJ, hg⟩ a ha b hb hab
    rw [mem_insert] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · subst ha; exact hg b hb
    · subst hb; exact fun h => hg a ha (hsymm _ _ h)
    · exact hJ a ha b hb hab

/-- **Deletion recursion.** -/
theorem Z_recursion (hsymm : ∀ a b, inc a b → inc b a) (S : Finset P) {γ : P} (hγ : γ ∈ S) :
    Z inc w S = Z inc w (S.erase γ) + w γ * Z inc w (compat inc S γ) := by
  set T := S.erase γ with hT
  have hγT : γ ∉ T := by simp [T]
  have hS : S = insert γ T := (insert_erase hγ).symm
  have hdisj : Disjoint (T.powerset.filter (Independent inc))
      ((T.powerset.image (insert γ)).filter (Independent inc)) := by
    rw [disjoint_left]
    intro A hA hB
    simp only [mem_filter, mem_powerset, mem_image] at hA hB
    obtain ⟨J, -, rfl⟩ := hB.1
    exact hγT (hA.1 (mem_insert_self γ J))
  have hinj : Set.InjOn (insert γ)
      (((T.powerset.filter fun J => Independent inc (insert γ J)) : Finset (Finset P)) :
        Set (Finset P)) := by
    intro J₁ h₁ J₂ h₂ he
    simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq] at h₁ h₂
    have n₁ : γ ∉ J₁ := fun h => hγT (h₁.1 h)
    have n₂ : γ ∉ J₂ := fun h => hγT (h₂.1 h)
    rw [← erase_insert n₁, ← erase_insert n₂, he]
  have hset : (T.powerset.filter fun J => Independent inc (insert γ J)) =
      (compat inc S γ).powerset.filter (Independent inc) := by
    ext J
    simp only [mem_filter, mem_powerset, compat, ← hT]
    constructor
    · rintro ⟨hJT, hJ⟩
      have nJ : γ ∉ J := fun h => hγT (hJT h)
      obtain ⟨hJ1, hJ2⟩ := (independent_insert inc hsymm nJ).mp hJ
      exact ⟨fun b hb => mem_filter.mpr ⟨hJT hb, hJ2 b hb⟩, hJ1⟩
    · rintro ⟨hJT, hJ⟩
      have hJT' : J ⊆ T := fun b hb => (mem_filter.mp (hJT hb)).1
      have nJ : γ ∉ J := fun h => hγT (hJT' h)
      exact ⟨hJT', (independent_insert inc hsymm nJ).mpr
        ⟨hJ, fun b hb => (mem_filter.mp (hJT hb)).2⟩⟩
  unfold Z
  rw [hS, powerset_insert, filter_union, sum_union hdisj, filter_image,
    sum_image hinj, ← hS, hset, mul_sum]
  congr 1
  refine sum_congr rfl fun J hJ => ?_
  have nJ : γ ∉ J := by
    simp only [mem_filter, mem_powerset, compat] at hJ
    intro h; simpa using (hJ.1 h)
  rw [prod_insert nJ]

/-! ### Dobrushin's criterion -/

/-- The polymers incompatible with `γ`, other than `γ`. -/
def nbhd [Fintype P] (γ : P) : Finset P := univ.filter fun b => b ≠ γ ∧ inc γ b

/-- The good-ratio property of a set `S`. -/
def Good (x : P → ℝ) (S : Finset P) : Prop :=
  0 < Z inc w S ∧ ∀ γ ∈ S, (1 - x γ) * Z inc w (S.erase γ) ≤ Z inc w S ∧
    Z inc w S ≤ (1 + x γ) * Z inc w (S.erase γ)

omit [DecidableEq P] in
lemma prod_pos_of_lt_one (x : P → ℝ) (hx1 : ∀ γ, x γ < 1) (R : Finset P) :
    0 < ∏ γ ∈ R, (1 - x γ) :=
  prod_pos fun γ _ => by linarith [hx1 γ]

/-- **Peeling.** If every subset of `T` is good, then removing a subset `R` of `T` shrinks the
partition function by at most `Π_R (1 − x)`. -/
lemma peel (x : P → ℝ) (hx1 : ∀ γ, x γ < 1) (T : Finset P) (hgood : ∀ U ⊆ T, Good inc w x U)
    (R : Finset P) (hR : R ⊆ T) :
    Z inc w (T \ R) * ∏ γ ∈ R, (1 - x γ) ≤ Z inc w T := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert a R ha ih =>
    have hRT : R ⊆ T := fun b hb => hR (mem_insert_of_mem hb)
    have haT : a ∈ T := hR (mem_insert_self a R)
    have haTR : a ∈ T \ R := mem_sdiff.mpr ⟨haT, ha⟩
    have hg := ((hgood (T \ R) sdiff_subset).2 a haTR).1
    have heq : T \ insert a R = (T \ R).erase a := by
      ext b; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
    rw [prod_insert ha, heq]
    have hP := (prod_pos_of_lt_one x hx1 R).le
    calc Z inc w ((T \ R).erase a) * ((1 - x a) * ∏ γ ∈ R, (1 - x γ))
        = ((1 - x a) * Z inc w ((T \ R).erase a)) * ∏ γ ∈ R, (1 - x γ) := by ring
      _ ≤ Z inc w (T \ R) * ∏ γ ∈ R, (1 - x γ) := mul_le_mul_of_nonneg_right hg hP
      _ ≤ Z inc w T := ih hRT

/-- **Dobrushin's criterion.** Under `|w γ| ≤ x γ · Π_{nbhd γ} (1 − x)` with `0 ≤ x < 1`, every
allowed set is good: positive partition function and ratio bounds `1 ± x γ`, at every volume. -/
theorem dobrushin [Fintype P] (hsymm : ∀ a b, inc a b → inc b a) (x : P → ℝ)
    (hx0 : ∀ γ, 0 ≤ x γ) (hx1 : ∀ γ, x γ < 1)
    (hw : ∀ γ, |w γ| ≤ x γ * ∏ b ∈ nbhd inc γ, (1 - x b)) (S : Finset P) :
    Good inc w x S := by
  have key : ∀ n, ∀ S : Finset P, S.card ≤ n → Good inc w x S := by
    intro n
    induction n with
    | zero =>
      intro S hS
      rw [card_eq_zero.mp (Nat.le_zero.mp hS)]
      exact ⟨by rw [Z_empty]; norm_num, by simp⟩
    | succ n ih =>
      intro S hS
      have hstep : ∀ γ ∈ S, (1 - x γ) * Z inc w (S.erase γ) ≤ Z inc w S ∧
          Z inc w S ≤ (1 + x γ) * Z inc w (S.erase γ) := by
        intro γ hγ
        set T := S.erase γ with hT
        have hTcard : T.card ≤ n := by rw [hT, card_erase_of_mem hγ]; omega
        have hgoodT : ∀ U ⊆ T, Good inc w x U :=
          fun U hU => ih U ((card_le_card hU).trans hTcard)
        set R := T.filter fun b => inc γ b with hRdef
        have hRT : R ⊆ T := filter_subset _ _
        have hC : compat inc S γ = T \ R := by
          ext b; simp only [compat, hRdef, hT, mem_sdiff, mem_filter]; tauto
        have hpeel := peel inc w x hx1 T hgoodT R hRT
        have hZC : 0 < Z inc w (T \ R) := (hgoodT (T \ R) sdiff_subset).1
        have hPR := prod_pos_of_lt_one x hx1 R
        have hRN : R ⊆ nbhd inc γ := by
          intro b hb
          simp only [hRdef, hT, mem_filter, mem_erase] at hb
          simp only [nbhd, mem_filter, mem_univ, true_and]
          exact ⟨hb.1.1, hb.2⟩
        have hNR : ∏ b ∈ nbhd inc γ, (1 - x b) ≤ ∏ b ∈ R, (1 - x b) := by
          rw [← prod_sdiff hRN]
          have h1 : ∏ b ∈ nbhd inc γ \ R, (1 - x b) ≤ 1 :=
            prod_le_one₀ (fun b _ => by linarith [hx1 b]) (fun b _ => by linarith [hx0 b])
          have h2 := hPR.le
          nlinarith
        have hwR : |w γ| ≤ x γ * ∏ b ∈ R, (1 - x b) :=
          (hw γ).trans (mul_le_mul_of_nonneg_left hNR (hx0 γ))
        have hbound : |w γ * Z inc w (T \ R)| ≤ x γ * Z inc w T := by
          rw [abs_mul, abs_of_pos hZC]
          calc |w γ| * Z inc w (T \ R) ≤ (x γ * ∏ b ∈ R, (1 - x b)) * Z inc w (T \ R) :=
                mul_le_mul_of_nonneg_right hwR hZC.le
            _ = x γ * (Z inc w (T \ R) * ∏ b ∈ R, (1 - x b)) := by ring
            _ ≤ x γ * Z inc w T := mul_le_mul_of_nonneg_left hpeel (hx0 γ)
        have hrec := Z_recursion inc w hsymm S hγ
        rw [← hT, hC] at hrec
        obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
        constructor
        · rw [hrec, sub_mul, one_mul]; linarith
        · rw [hrec, add_mul, one_mul]; linarith
      refine ⟨?_, hstep⟩
      rcases S.eq_empty_or_nonempty with h | ⟨γ, hγ⟩
      · rw [h, Z_empty]; norm_num
      · have hT := (ih (S.erase γ) (by rw [card_erase_of_mem hγ]; omega)).1
        have h1 := (hstep γ hγ).1
        have h2 : 0 < (1 - x γ) * Z inc w (S.erase γ) := mul_pos (by linarith [hx1 γ]) hT
        linarith
  exact key S.card S le_rfl

/-- **Extensive lower bound.** `Π_S (1 − x) ≤ Z S`. -/
theorem Z_lower [Fintype P] (hsymm : ∀ a b, inc a b → inc b a) (x : P → ℝ)
    (hx0 : ∀ γ, 0 ≤ x γ) (hx1 : ∀ γ, x γ < 1)
    (hw : ∀ γ, |w γ| ≤ x γ * ∏ b ∈ nbhd inc γ, (1 - x b)) (S : Finset P) :
    ∏ γ ∈ S, (1 - x γ) ≤ Z inc w S := by
  have h := peel inc w x hx1 S (fun U _ => dobrushin inc w hsymm x hx0 hx1 hw U) S subset_rfl
  rwa [sdiff_self, bot_eq_empty, Z_empty, one_mul] at h

/-- **Extensive upper bound.** `Z S ≤ Π_S (1 + x)`. -/
theorem Z_upper [Fintype P] (hsymm : ∀ a b, inc a b → inc b a) (x : P → ℝ)
    (hx0 : ∀ γ, 0 ≤ x γ) (hx1 : ∀ γ, x γ < 1)
    (hw : ∀ γ, |w γ| ≤ x γ * ∏ b ∈ nbhd inc γ, (1 - x b)) (S : Finset P) :
    Z inc w S ≤ ∏ γ ∈ S, (1 + x γ) := by
  induction S using Finset.induction_on with
  | empty => rw [Z_empty, prod_empty]
  | @insert a R ha ih =>
    have hg := ((dobrushin inc w hsymm x hx0 hx1 hw (insert a R)).2 a (mem_insert_self a R)).2
    rw [erase_insert ha] at hg
    rw [prod_insert ha]
    exact hg.trans (mul_le_mul_of_nonneg_left ih (by linarith [hx0 a]))

omit [DecidableEq P] in
/-- **Weierstrass product inequality.** `Π (1 − x_i) ≥ 1 − Σ x_i` for `x_i ∈ [0,1]`. -/
theorem prod_one_sub_ge {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have ha0 := h0 a (mem_insert_self a s)
    have ha1 := h1 a (mem_insert_self a s)
    have hs0 : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith [mul_le_mul_of_nonneg_left ih' (by linarith : (0:ℝ) ≤ 1 - x a)]

end PMAction.MassGap.PolymerConvergence
