import PMConstants.RunningResponseLink
import PMConstants.StableReadout
import PMAction.FluctuationPremises

/-!
# Paper III's running tests on derived coefficients

Paper II now derives every term of the one-loop coefficient:

- spin `1/2` and spin `0` (`PMAction.RunningResponse`);
- spin `1` (`PMAction.GaugeFluctuation`);
- the gauge-invariance, charge-action and Landau-spectrum inputs (`PMAction.FluctuationPremises`).

This module restates Paper III's running results on those terms.

* `standard_coefficients_derived`: `b₃ = 7`, `b₂ = 19/6` and `b_Y = −41/6` as explicit sums of
  `spinTerm 2 = 2² − 1/3`, `spinTerm 1 = −(1² − 1/3)` and `spinTerm 0 = 0² − 1/3`.
* `freedom_needs_spin`: without the derived spin-1 Zeeman coupling (`a = 0` instead of `a = 2`),
  colour would screen at every flavour number. Asymptotic freedom, for `n_f ≤ 16`, is the
  paramagnetic `2F` term of the gauge fluctuation operator.
* `colour_never_stationary_derived`: colour runs at every flavour number, because
  `3 · (4 − 1/3) = 11` is not a multiple of `2/3`.
* `abelian_screens`: an abelian coupling with active charged matter has `b < 0`. This is the
  sign of the derived spin-`1/2` and spin-`0` terms. It underlies the `α(0)` plateau of
  `StableReadout`.
-/

noncomputable section
namespace PMConstants.RunningDerived
open PMAction.RunningCoefficients

/-- The three Standard-Model coefficients, as sums of derived spin terms. -/
theorem standard_coefficients_derived :
    bContent 3 (3 * 2) 0 = spinTerm 2 * 3 + spinTerm 1 * 6 ∧
    bContent 2 (3 * 2) (1 / 2) = spinTerm 2 * 2 + spinTerm 1 * 6 + spinTerm 0 * (1 / 2) ∧
    bContent 0 (3 * (10 / 3)) (2 * (1 / 2) ^ 2) = spinTerm 1 * 10 + spinTerm 0 * (1 / 2) ∧
    spinTerm 2 = 2 ^ 2 - 1 / 3 ∧ spinTerm 1 = -(1 ^ 2 - 1 / 3) ∧ spinTerm 0 = 0 ^ 2 - 1 / 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [bContent, spinTerm] <;> norm_num

/-- **Asymptotic freedom is the spin-1 Zeeman term.** With `a = 0` for the gauge pair, the colour
coefficient would be negative for every `n_f`. With the derived `a = 2`, it is positive exactly
for `n_f ≤ 16`. -/
theorem freedom_needs_spin (nf : ℕ) :
    3 * ((0 : ℚ) ^ 2 - 1 / 3) + spinTerm 1 * nf < 0 ∧
      (0 < 3 * ((2 : ℚ) ^ 2 - 1 / 3) + spinTerm 1 * nf ↔ nf ≤ 16) := by
  have h1 : spinTerm 1 = -2 / 3 := spin_terms.2.1
  refine ⟨?_, ?_⟩
  · rw [h1]; have : (0 : ℚ) ≤ nf := by positivity
    linarith
  · have e : 3 * ((2 : ℚ) ^ 2 - 1 / 3) + spinTerm 1 * nf = b0 3 nf 0 := by
      rw [b0_formula, h1]; ring
    rw [e]; exact asymptotic_freedom_iff nf

/-- Colour runs at every flavour number, stated on the derived terms. -/
theorem colour_never_stationary_derived (nf : ℕ) :
    spinTerm 2 * 3 + spinTerm 1 * nf ≠ 0 := by
  rw [← RunningResponseLink.strong_coefficients_derived]
  exact StableReadout.colour_never_stationary nf

/-- **Charged matter screens an abelian coupling.** Both derived matter terms are negative, so
any active matter gives `b < 0`. With no matter, `b = 0`. -/
theorem abelian_screens (weyl scalar : ℚ) (hw : 0 ≤ weyl) (hs : 0 ≤ scalar)
    (h : weyl ≠ 0 ∨ scalar ≠ 0) : bContent 0 weyl scalar < 0 := by
  have hne : bContent 0 weyl scalar ≠ 0 := by
    intro h0
    obtain ⟨a, b⟩ := (StableReadout.abelian_stationary_iff weyl scalar hw hs).mp h0
    rcases h with h | h <;> contradiction
  have hle : bContent 0 weyl scalar ≤ 0 := by
    rw [bContent_formula]; linarith
  exact lt_of_le_of_ne hle hne

end PMConstants.RunningDerived
