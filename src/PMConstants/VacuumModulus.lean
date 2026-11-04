import PMConstants.PersistenceClosures

/-!
# θ = 0 is unique under the modulus too, once the trivial sector counts

`PersistenceClosures.strict_vafa_witten` makes `θ = 0` the unique least-cost vacuum when the cost
is read from `Re Z`; `abs_not_unique` shows the modulus `‖Z‖` does not decide when only the windings
`±1` are weighted (then `‖Z(π)‖ = Z(0)`). That counterexample omits the topologically trivial sector.

Premise: the zero-winding sector, the vacuum persisting without tunnelling, has positive weight
`w₀ > 0` (the weights are nonnegative because the transfer operator `e^{−H}` is positive). With it:

* `pair_strict`: `‖w₀ + w₁ e^{iθ}‖ < w₀ + w₁` whenever `w₀, w₁ > 0` and `cos θ < 1`.
* `strict_modulus`: if `0` and `1` are both weighted, `‖Z(θ)‖ < Z(0)` for every `θ ≠ 0` in `(−π, π]`.
  So `θ = 0` is the unique least-cost vacuum for the cost `−log ‖Z‖` as well; the `Re Z` premise
  is replaced by the positivity of the trivial sector's weight.
* `abs_counterexample_lacks_zero`: the `abs_not_unique` weights sit on `{−1, 1}`, without `0`.
-/

noncomputable section
namespace PMConstants.VacuumModulus
open Complex HermitianMass

lemma cos_lt_one_of {θ : ℝ} (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (hne : θ ≠ 0) :
    Real.cos θ < 1 := by
  refine lt_of_le_of_ne (Real.cos_le_one θ) (fun h => ?_)
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff θ).mp h
  have hpi := Real.pi_pos
  obtain ⟨h1, h2⟩ := hθ
  have hk1 : (k : ℝ) < 1 := by
    by_contra hc; push Not at hc; nlinarith
  have hk2 : (-1 : ℝ) < k := by
    by_contra hc; push Not at hc; nlinarith
  have : k = 0 := by
    have a : k < 1 := by exact_mod_cast hk1
    have b : -1 < k := by exact_mod_cast hk2
    omega
  subst this; simp at hk; exact hne hk.symm

/-- **Two weighted sectors with different phases give a strictly shorter sum.** -/
theorem pair_strict (w0 w1 θ : ℝ) (h0 : 0 < w0) (h1 : 0 < w1) (hc : Real.cos θ < 1) :
    ‖(w0 : ℂ) + (w1 : ℂ) * exp ((θ : ℂ) * I)‖ < w0 + w1 := by
  have hsq : ‖(w0 : ℂ) + (w1 : ℂ) * exp ((θ : ℂ) * I)‖ ^ 2 =
      w0 ^ 2 + w1 ^ 2 + 2 * w0 * w1 * Real.cos θ := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, exp_ofReal_mul_I_re,
      exp_ofReal_mul_I_im]
    have := Real.sin_sq_add_cos_sq θ
    nlinarith [this]
  have hn : 0 ≤ ‖(w0 : ℂ) + (w1 : ℂ) * exp ((θ : ℂ) * I)‖ := norm_nonneg _
  by_contra hge
  push Not at hge
  have : (w0 + w1) ^ 2 ≤ ‖(w0 : ℂ) + (w1 : ℂ) * exp ((θ : ℂ) * I)‖ ^ 2 := by
    nlinarith [hge]
  rw [hsq] at this
  nlinarith [mul_pos h0 h1]

lemma term_norm (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n) (θ : ℝ) (n : ℤ) :
    ‖(w n : ℂ) * exp ((((n : ℝ) * θ : ℝ) : ℂ) * I)‖ = w n := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hw n)]

/-- **With the trivial sector weighted, the modulus selects `θ = 0` uniquely.** -/
theorem strict_modulus (S : Finset ℤ) (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (h0 : (0 : ℤ) ∈ S) (h1 : (1 : ℤ) ∈ S) (hw0 : 0 < w 0) (hw1 : 0 < w 1)
    (θ : ℝ) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (hne : θ ≠ 0) :
    ‖Z S w θ‖ < ∑ n ∈ S, w n := by
  set f : ℤ → ℂ := fun n => (w n : ℂ) * exp ((((n : ℝ) * θ : ℝ) : ℂ) * I) with hf
  have h1' : (1 : ℤ) ∈ S.erase 0 := Finset.mem_erase.mpr ⟨by norm_num, h1⟩
  set T := (S.erase 0).erase 1
  have hZ : Z S w θ = (f 0 + f 1) + ∑ n ∈ T, f n := by
    unfold Z
    rw [← Finset.add_sum_erase S _ h0, ← Finset.add_sum_erase (S.erase 0) _ h1', add_assoc]
  have hW : ∑ n ∈ S, w n = (w 0 + w 1) + ∑ n ∈ T, w n := by
    rw [← Finset.add_sum_erase S _ h0, ← Finset.add_sum_erase (S.erase 0) _ h1', add_assoc]
  have hpair : ‖f 0 + f 1‖ < w 0 + w 1 := by
    have e : f 0 + f 1 = (w 0 : ℂ) + (w 1 : ℂ) * exp ((θ : ℂ) * I) := by
      simp [hf]
    rw [e]
    exact pair_strict (w 0) (w 1) θ hw0 hw1 (cos_lt_one_of hθ hne)
  have hrest : ‖∑ n ∈ T, f n‖ ≤ ∑ n ∈ T, w n :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => term_norm w hw θ n))
  rw [hZ, hW]
  calc ‖(f 0 + f 1) + ∑ n ∈ T, f n‖ ≤ ‖f 0 + f 1‖ + ‖∑ n ∈ T, f n‖ := norm_add_le _ _
    _ < (w 0 + w 1) + ∑ n ∈ T, w n := by linarith

theorem abs_counterexample_lacks_zero : (0 : ℤ) ∉ ({-1, 1} : Finset ℤ) := by decide

end PMConstants.VacuumModulus
