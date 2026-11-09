import PMAction.MassGap.ParitySigns

/-!
# Walsh expansion of slice functions

Every function `φ` on slice states `V → Bool` is a combination of parity characters
`χ_A(s) = Π_{a ∈ A} sgn(s a)`:

* `walsh`: `φ s = Σ_A ĉ_A χ_A(s)` with `ĉ_A = 2^{-|V|} Σ_t φ t χ_A(t)`.
* `coef_odd`: if `φ` is invariant under the global flip, `ĉ_A = 0` for every odd `A`.

So a flip-even function is a combination of even characters only.
-/

namespace PMAction.MassGap.Walsh
open Finset ParitySigns

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Walsh coefficient. -/
noncomputable def coef (φ : (V → Bool) → ℝ) (A : Finset V) : ℝ :=
  (2 ^ Fintype.card V : ℝ)⁻¹ * ∑ t, φ t * ∏ a ∈ A, sgn (t a)

omit [DecidableEq V] in
lemma char_sum (s t : V → Bool) :
    ∑ A : Finset V, (∏ a ∈ A, sgn (t a)) * ∏ a ∈ A, sgn (s a) =
      if t = s then (2 ^ Fintype.card V : ℝ) else 0 := by
  have h : ∑ A : Finset V, (∏ a ∈ A, sgn (t a)) * ∏ a ∈ A, sgn (s a) =
      ∏ v, (1 + sgn (t v) * sgn (s v)) := by
    rw [prod_one_add, powerset_univ]
    exact sum_congr rfl fun A _ => (prod_mul_distrib).symm
  rw [h]
  split_ifs with hts
  · subst hts
    rw [prod_congr rfl fun v _ => show 1 + sgn (t v) * sgn (t v) = 2 by
      cases t v <;> norm_num [sgn], prod_const, card_univ]
  · obtain ⟨v, hv⟩ : ∃ v, t v ≠ s v := by
      by_contra hc; push Not at hc; exact hts (funext hc)
    refine prod_eq_zero (mem_univ v) ?_
    cases ht : t v <;> cases hs : s v <;> simp_all [sgn]

/-- **Walsh expansion.** -/
theorem walsh (φ : (V → Bool) → ℝ) (s : V → Bool) :
    φ s = ∑ A : Finset V, coef φ A * ∏ a ∈ A, sgn (s a) := by
  simp only [coef, mul_assoc, ← mul_sum, sum_mul]
  rw [sum_comm]
  simp only [← mul_sum, char_sum]
  rw [sum_eq_single s (fun t _ hts => by simp [hts]) (by simp)]
  simp only [↓reduceIte]
  have : (2 ^ Fintype.card V : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Even functions have even spectra.** -/
theorem coef_odd (φ : (V → Bool) → ℝ) (hφ : ∀ s, φ (fun v => !s v) = φ s) {A : Finset V}
    (hA : Odd A.card) : coef φ A = 0 := by
  have hflip : Function.Involutive fun (s : V → Bool) v => !s v := fun s => by funext v; simp
  set S := ∑ t, φ t * ∏ a ∈ A, sgn (t a)
  have hS : S = -S := by
    conv_lhs => rw [show S = ∑ t : V → Bool, φ (fun v => !t v) * ∏ a ∈ A, sgn (!t a) from
      (Equiv.sum_comp hflip.toPerm (fun t : V → Bool => φ t * ∏ a ∈ A, sgn (t a))).symm]
    have : ∀ t : V → Bool, φ (fun v => !t v) * ∏ a ∈ A, sgn (!t a) =
        -(φ t * ∏ a ∈ A, sgn (t a)) := fun t => by
      have h1 : ∀ a, sgn (!t a) = -1 * sgn (t a) := fun a => by cases t a <;> simp [sgn]
      rw [hφ, prod_congr rfl fun a _ => h1 a, prod_mul_distrib, prod_const, hA.neg_one_pow]
      ring
    rw [sum_congr rfl fun t _ => this t, sum_neg_distrib]
  have : S = 0 := by linarith
  unfold coef; rw [show (∑ t, φ t * ∏ a ∈ A, sgn (t a)) = S from rfl, this, mul_zero]

end PMAction.MassGap.Walsh
