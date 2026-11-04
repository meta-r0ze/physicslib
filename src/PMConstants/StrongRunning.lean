import PMConstants.ScaleResponse

/-!
# The strong-coupling running test to the tau mass

The paper runs `α_s` from the Z mass to the tau mass with one-loop `β₀ = 9` (three flavours)
across the whole interval, then multiplies by `15/16` ("sterile channel").

* `flavour_order`: with Paper V's own quark masses (in electron units),
  `m_c < m_τ < m_b < M_Z`. Under the species-additive, threshold response of
  `ScaleResponse` (a species screens only above its mass), five flavours are active on
  `[m_b, M_Z]` and four on `[m_τ, m_b]`.
* `three_flavours_inflate`: for any positive log intervals, using three flavours throughout
  gives a strictly smaller `α_s⁻¹` (larger `α_s`) at the tau mass than the threshold law.
  The excess is `(1/2π)((4/3)L₁ + (2/3)L₂)`.
* `uniform_factor_scale_free`: a multiplicative `15/16` changes the coupling by the same
  relative amount `1/16` at every scale, so it cannot be negligible at weak coupling and
  significant only at strong coupling. Applied at the Z mass it gives `α_s < 0.1106`.
* `locked_channel_share`: a probability vector over sixteen channels always has total mass
  one. Its non-reference mass is `15/16` iff the reference channel carries exactly `1/16`;
  the normalization constraint alone does not supply that.
-/

noncomputable section
namespace PMConstants.StrongRunning
open PMConstants CertifiedConstants

/-! ## Flavour thresholds from Paper V's masses (units of `m_e`) -/

def mCharm : ℝ := 4 * 43^2 / (overhead * (5 - 2))
def mTau : ℝ := -4 + 43^2 * 2 - 43 * 5 - 2
def mBottom : ℝ := 43^2 * (4 + 2/5) / overhead
def mZ : ℝ := 91187.6 / 0.51099895

theorem flavour_order : mCharm < mTau ∧ mTau < mBottom ∧ mBottom < mZ := by
  norm_num [mCharm, mTau, mBottom, mZ, overhead]

/-! ## One-loop inverse coupling over two intervals -/

/-- Threshold law: `L₁ = log(M_Z/m_b)` with five flavours, `L₂ = log(m_b/m_τ)` with four. -/
def invThreshold (a L₁ L₂ : ℝ) : ℝ :=
  1/a - (11 - 2*5/3)/(2*Real.pi) * L₁ - (11 - 2*4/3)/(2*Real.pi) * L₂

def invThree (a L₁ L₂ : ℝ) : ℝ := 1/a - 9/(2*Real.pi) * (L₁ + L₂)

theorem three_flavours_excess (a L₁ L₂ : ℝ) :
    invThreshold a L₁ L₂ - invThree a L₁ L₂ =
      (1/(2*Real.pi)) * ((4/3)*L₁ + (2/3)*L₂) := by
  unfold invThreshold invThree; ring

theorem three_flavours_inflate {a L₁ L₂ : ℝ} (h1 : 0 < L₁) (h2 : 0 < L₂)
    (hpos : 0 < invThree a L₁ L₂) :
    1 / invThreshold a L₁ L₂ < 1 / invThree a L₁ L₂ := by
  have hx := three_flavours_excess a L₁ L₂
  have hp : 0 < (1/(2*Real.pi)) * ((4/3)*L₁ + (2/3)*L₂) := by positivity
  apply one_div_lt_one_div_of_lt hpos
  linarith

/-! ## A uniform factor is scale-free -/

theorem uniform_factor_scale_free (a : ℝ) (ha : a ≠ 0) :
    (a - (15/16) * a) / a = 1/16 := by field_simp; ring

theorem factor_at_z : (15/16) * strongCoupling α < 0.1106 := by
  have := strong_bounds; nlinarith [this.2]

/-! ## Normalization does not lock a share -/

theorem locked_channel_share (p : Fin 16 → ℝ) (hs : ∑ i, p i = 1) (ref : Fin 16) :
    (∑ i, p i) - p ref = 15/16 ↔ p ref = 1/16 := by
  rw [hs]; constructor <;> intro h <;> linarith

/-- A normalized vector whose reference channel does not carry `1/16`. -/
theorem locked_share_not_forced :
    ∃ p : Fin 16 → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ p 0 ≠ 1/16 := by
  refine ⟨fun i => if i = 0 then 1 else 0, fun i => by dsimp only; split_ifs <;> norm_num, ?_, by simp⟩
  simp [Finset.sum_ite_eq']

end PMConstants.StrongRunning
