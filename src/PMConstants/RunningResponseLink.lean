import PMAction.RunningResponse
import PMAction.GaugeFluctuation
import PMConstants.MatterRunning

/-!
# Matter running coefficients from Paper II's spin and orbital response

Paper II's `PMAction.RunningResponse` derives the `B²` heat-kernel coefficient of a helicity pair
with Zeeman factor `a = 2s`: it is `a² − 1/3` (`pair_coefficient`). The `1/3` is the Landau
diamagnetic term (`landau_sum`, `pair_kernel`). For spin `1/2`, `a = 1` is derived from the
Clifford relations (`zeeman`, `concrete_spin`). For spin `0`, `a = 0`.

* `weyl_term_derived`, `scalar_term_derived`: `spinTerm 1` and `spinTerm 0` are the statistics
  sign times the derived pair coefficient at `a = 1` and `a = 0`.
* `flavour_step`, `scalar_step`: each added Dirac flavour changes `b₀` by `spinTerm 1 = −2/3`, and
  each added real scalar by `spinTerm 0 / 2 = −1/6`. These are the steps used at the quark
  thresholds in `StrongRunning`.
* `hyper_coefficient_derived`: the hypercharge coefficient `b_Y = −41/6` of
  `MatterRunning.standard_coefficients` has no gauge part, so it is built only from the derived
  spin-`1/2` and spin-`0` terms.
* `gauge_term_derived`: the gauge part `spinTerm 2 = 11/3`. Paper II's `GaugeFluctuation`
  derives the gauge-fixed Yang–Mills fluctuation operator `−D² + 2[F, ·]` (`quad_eq_hess`). One
  `F` comes from the commutator `[D_μ, D_ν]` and one from the cubic cross term. On a charged mode
  in a planar field, the spin coupling is `2qb` times a helicity matrix with spectrum
  `{1, −1, 0, 0}` (`charged_spin`, `helicity_spectrum`). The ghost operator has no spin term
  (`ghost_operator`). The vector-minus-ghost kernel is a helicity pair with `a = 2`
  (`vector_kernel`), and its `B²` coefficient is `11/3` (`vector_coefficient`).
* `gauge_coefficient_derived`, `strong_coefficients_derived`: Paper III's `gaugeCoeff`, and
  `b₀(SU(3), n_f)` at its thresholds, use only these derived terms.

**Premises** (from Paper II's modules):

- the Landau spectrum `(2n+1)|b|` and the degeneracy of a continuum charged field (the
  substrate's matter hops are the continuum covariant operators: `PMAction.Machine.MatterContinuum`;
  in momentum space the orbital `−1/3` is the D₄ moment average
  `PMAction.PolarizationAverage.orbital_third` over the shell `PMAction.LeadingLog.leading_log`);
- background Feynman gauge;
- two Faddeev–Popov ghost components with fermionic sign;
- the charge action `[f, ·] = i q b` on a charged adjoint mode.
-/

noncomputable section
namespace PMConstants.RunningResponseLink
open PMAction.RunningCoefficients PMAction.RunningResponse

/-- Spin `1/2`: statistics sign `−1` times the pair coefficient `1² − 1/3`. -/
theorem weyl_term_derived :
    ((spinTerm 1 : ℚ) : ℝ) = -((1 : ℝ) ^ 2 - 1 / 3) ∧ spinTerm 1 = -2 / 3 := by
  refine ⟨?_, spin_terms.2.1⟩
  rw [spin_term_from_response]; norm_num

/-- Spin `0`: statistics sign `+1` times the pair coefficient `0² − 1/3`. -/
theorem scalar_term_derived :
    ((spinTerm 0 : ℚ) : ℝ) = (0 : ℝ) ^ 2 - 1 / 3 ∧ spinTerm 0 = -1 / 3 := by
  refine ⟨?_, spin_terms.2.2⟩
  rw [spin_term_from_response]; norm_num

/-- The spin-`1/2` pair coefficient `1² − 1/3` is the derived `B²` term of `pair_coefficient`. -/
theorem weyl_pair_expansion :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      |x / Real.sinh x * (Real.exp x + Real.exp (-x)) - 2 - (2 / 3) * x ^ 2| ≤ C * x ^ 4 := by
  obtain ⟨C, hC, h⟩ := pair_coefficient 1
  refine ⟨C, hC, fun x hx h1 => ?_⟩
  have := h x hx h1 (by simpa using h1)
  simp only [one_mul] at this
  convert this using 3; norm_num

/-- One more Dirac flavour (two Weyl states, index `1/2`) shifts `b₀` by `spinTerm 1`. -/
theorem flavour_step (N nf ns : ℕ) : b0 N (nf + 1) ns - b0 N nf ns = spinTerm 1 := by
  rw [b0_formula, b0_formula, spin_terms.2.1]; push_cast; ring

/-- One more real scalar shifts `b₀` by `spinTerm 0 / 2`. -/
theorem scalar_step (N nf ns : ℕ) : b0 N nf (ns + 1) - b0 N nf ns = spinTerm 0 / 2 := by
  rw [b0_formula, b0_formula, spin_terms.2.2]; push_cast; ring

/-- The quark-threshold steps used in Paper III's strong running are the derived Weyl term. -/
theorem threshold_steps :
    b0 3 5 0 - b0 3 4 0 = spinTerm 1 ∧ b0 3 4 0 - b0 3 3 0 = spinTerm 1 :=
  ⟨flavour_step 3 4 0, flavour_step 3 3 0⟩

/-- **`b_Y` uses only derived terms.** With no gauge part, `bContent 0 weyl scalar` is
`spinTerm 1 · weyl + spinTerm 0 · scalar`, and the Standard-Model content gives `−41/6`. -/
theorem hyper_coefficient_derived :
    bContent 0 (3 * (10 / 3)) (2 * (1 / 2) ^ 2) =
        spinTerm 1 * (3 * (10 / 3)) + spinTerm 0 * (2 * (1 / 2) ^ 2) ∧
      bContent 0 (3 * (10 / 3)) (2 * (1 / 2) ^ 2) = -41 / 6 := by
  refine ⟨?_, MatterRunning.standard_coefficients.2.2⟩
  unfold bContent; ring

/-- **The gauge part.** `spinTerm 2` equals the bosonic sign times the `B²` coefficient
`2² − 1/3` of Paper II's vector-minus-ghost kernel, and that kernel's expansion holds. -/
theorem gauge_term_derived :
    ((spinTerm 2 : ℚ) : ℝ) = (2 : ℝ) ^ 2 - 1 / 3 ∧ spinTerm 2 = 11 / 3 ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 / 2 →
        |(∑ i, x / Real.sinh x * Real.exp (2 * PMAction.GaugeFluctuation.helicityEig i * x)) -
            2 * (x / Real.sinh x) - 2 - 11 / 3 * x ^ 2| ≤ C * x ^ 4 :=
  ⟨PMAction.GaugeFluctuation.spin_one_term, spin_terms.1,
    PMAction.GaugeFluctuation.vector_coefficient⟩

/-- Paper III's gauge coefficient is the derived spin-1 term times `C_A`. -/
theorem gauge_coefficient_derived (cA : ℚ) :
    BetaUniversality.gaugeCoeff cA = spinTerm 2 * cA :=
  RunningLinks.gauge_coefficient cA

/-- `b₀(SU(3), n_f)` is built only from the derived spin-1 and spin-`1/2` terms. -/
theorem strong_coefficients_derived (nf : ℕ) :
    b0 3 nf 0 = spinTerm 2 * 3 + spinTerm 1 * nf := by
  rw [b0_formula, spin_terms.1, spin_terms.2.1]; ring

end PMConstants.RunningResponseLink
