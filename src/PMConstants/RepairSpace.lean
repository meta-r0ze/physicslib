import PMConstants.GaugeSpectrum

/-!
# Which changes could repair the joint electroweak residuals?

Two residuals are already certified: the electron closure ratio `y_e v/(√2 m_e)` and the
uncorrected W/Z masses. Here we separate the parameters that can move them.

* **Gauge sector.** Over the whole efficiency range `0 ≤ η ≤ 1`, the overhead changes only the
  mixing fraction `s(η) = 43/(177+16η)`. The products `m_W² s` and `m_Z² s(1−s)` equal `π α v²`
  for every `η`. Relative to the paper's `η = 171/172`, the best `η` raises `m_W²` by less than
  `0.05%` and `m_Z²` by less than `0.04%`. A common scale factor on `α v²` moves both masses
  together, and one such factor reaches a target pair iff the pair's ratio is `1 − s(η)`.
* **Electron closure.** A scalar-field rescaling `y ↦ y/c, v ↦ c v` leaves `y v/√2` unchanged,
  `√2` conventions multiply the ratio by powers of `√2`, and holding the Fermi formula fixed
  pins `c = ±1`. None of these can move a ratio in `(0.99972687, 0.99972689)` to one.

No measured value is used. Interpretation against data is outside this module.
-/

noncomputable section
namespace PMConstants.RepairSpace
open PMConstants PMConstants.ElectroweakE8 PMConstants.GaugeSpectrum

/-! ## Gauge response across `0 ≤ η ≤ 1` -/

def foot (η : ℝ) : ℝ := 172 + 16*η + 5
def mix (η : ℝ) : ℝ := 43 / foot η

/-- Uncorrected masses squared, as functions of `η` and the common scale `a v²`. -/
def wSq (η a v : ℝ) : ℝ := (4*Real.pi*a/mix η) * v^2 / 4
def zSq (η a v : ℝ) : ℝ := (4*Real.pi*a/mix η + 4*Real.pi*a/(1-mix η)) * v^2 / 4

lemma foot_pos {η : ℝ} (h : 0 ≤ η) : 0 < foot η := by unfold foot; linarith
lemma foot_gt {η : ℝ} (h : 0 ≤ η) : 43 < foot η := by unfold foot; linarith

/-- The paper's gauge response is the `η = 171/172` member of this family. -/
theorem paper_member (a me : ℝ) :
    wMassSquared a me = wSq (171/172) a (vev a me) ∧
      zMassSquared a me = zSq (171/172) a (vev a me) := by
  have hc : clockRatio = mix (171/172) := by
    norm_num [clockRatio, footprint, overhead, mix, foot]
  refine ⟨?_, ?_⟩
  · unfold wMassSquared wSq weakSquared; rw [hc]
  · unfold zMassSquared zSq weakSquared hyperchargeSquared; rw [hc]

theorem w_closed (η a v : ℝ) (h : 0 ≤ η) : wSq η a v = Real.pi*a*v^2 * foot η / 43 := by
  have := foot_pos h
  unfold wSq mix; field_simp

theorem z_closed (η a v : ℝ) (h : 0 ≤ η) :
    zSq η a v = Real.pi*a*v^2 * (foot η)^2 / (43*(foot η - 43)) := by
  have h1 := foot_pos h; have h2 := foot_gt h
  have h3 : foot η - 43 ≠ 0 := by linarith
  unfold zSq mix
  have h4 : (1 : ℝ) - 43/foot η = (foot η - 43)/foot η := by field_simp
  rw [h4]; field_simp; ring

/-- The `η`-free invariants: the overhead cannot change `π α v²`. -/
theorem w_invariant (η a v : ℝ) (h : 0 ≤ η) : wSq η a v * mix η = Real.pi*a*v^2 := by
  rw [w_closed η a v h]; have := foot_pos h; unfold mix; field_simp

theorem z_invariant (η a v : ℝ) (h : 0 ≤ η) :
    zSq η a v * (mix η * (1 - mix η)) = Real.pi*a*v^2 := by
  rw [z_closed η a v h]
  have h1 := foot_pos h; have h2 := foot_gt h
  have h3 : foot η - 43 ≠ 0 := by linarith
  unfold mix
  have h4 : (1 : ℝ) - 43/foot η = (foot η - 43)/foot η := by field_simp
  rw [h4]; field_simp

theorem mass_ratio (η a v : ℝ) (h : 0 ≤ η) (_hs : Real.pi*a*v^2 ≠ 0) :
    wSq η a v = (1 - mix η) * zSq η a v := by
  rw [w_closed η a v h, z_closed η a v h]
  have h1 := foot_pos h; have h2 := foot_gt h
  have h3 : foot η - 43 ≠ 0 := by linarith
  unfold mix; field_simp

/-- Both masses are increasing in `η`, so `η = 1` bounds every efficiency. -/
theorem w_eta_bound {η a v : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (hs : 0 ≤ Real.pi*a*v^2) :
    wSq η a v ≤ wSq 1 a v := by
  rw [w_closed η a v h0, w_closed 1 a v (by norm_num)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_left _ hs
  unfold foot; linarith

theorem z_eta_bound {η a v : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (hs : 0 ≤ Real.pi*a*v^2) :
    zSq η a v ≤ zSq 1 a v := by
  rw [z_closed η a v h0, z_closed 1 a v (by norm_num)]
  have hF := foot_gt h0
  have hF1 : foot η ≤ 193 := by unfold foot; linarith
  have hd : 0 < foot η - 43 := by linarith
  rw [mul_div_assoc, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hs
  rw [div_le_div_iff₀ (by positivity) (by norm_num [foot])]
  norm_num [foot]
  nlinarith [hF, hF1]

/-- Relative to the paper's `η`, no efficiency raises `m_W²` by more than `0.05%`. -/
theorem w_headroom {η a v : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (hs : 0 < Real.pi*a*v^2) :
    wSq η a v < (1 + 1/2000) * wSq (171/172) a v := by
  have hb := w_eta_bound h0 h1 hs.le
  rw [w_closed 1 a v (by norm_num)] at hb
  rw [w_closed (171/172) a v (by norm_num)]
  refine lt_of_le_of_lt hb ?_
  norm_num [foot]
  nlinarith

/-- Relative to the paper's `η`, no efficiency raises `m_Z²` by more than `0.04%`. -/
theorem z_headroom {η a v : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (hs : 0 < Real.pi*a*v^2) :
    zSq η a v < (1 + 1/2500) * zSq (171/172) a v := by
  have hb := z_eta_bound h0 h1 hs.le
  rw [z_closed 1 a v (by norm_num)] at hb
  rw [z_closed (171/172) a v (by norm_num)]
  refine lt_of_le_of_lt hb ?_
  norm_num [foot]
  nlinarith

/-- A common factor on `α v²` scales both masses equally. -/
theorem common_scale (η a v k : ℝ) :
    wSq η (k*a) v = k * wSq η a v ∧ zSq η (k*a) v = k * zSq η a v := by
  unfold wSq zSq; constructor <;> ring

/-- One common factor reaches a target pair iff the pair has the model's mass ratio. -/
theorem one_factor_iff (η a v W Z : ℝ) (h : 0 ≤ η) (hs : Real.pi*a*v^2 ≠ 0) (hZ : 0 < Z) :
    (∃ k, wSq η (k*a) v = W ∧ zSq η (k*a) v = Z) ↔ W = (1 - mix η) * Z := by
  have hz : zSq η a v ≠ 0 := by
    rw [z_closed η a v h]
    have := foot_gt h
    have : foot η - 43 ≠ 0 := by linarith
    have : foot η ≠ 0 := by linarith
    positivity
  constructor
  · rintro ⟨k, hw, hzk⟩
    rw [← hw, ← hzk, (common_scale η a v k).1, (common_scale η a v k).2,
      mass_ratio η a v h hs]; ring
  · intro hW
    refine ⟨Z / zSq η a v, ?_, ?_⟩
    · rw [(common_scale η a v _).1, mass_ratio η a v h hs, hW]; field_simp
    · rw [(common_scale η a v _).2]; field_simp

/-! ## Electron closure: normalization cannot help -/

/-- A scalar-field rescaling leaves the mass law unchanged. -/
theorem rescale_invariant (y v c : ℝ) (hc : c ≠ 0) :
    (y/c) * (c*v) / Real.sqrt 2 = y * v / Real.sqrt 2 := by
  field_simp

/-- Holding the Fermi formula fixed pins the rescaling. -/
theorem fermi_pins_scale (v c : ℝ) (hv : v ≠ 0)
    (h : 1/(Real.sqrt 2 * (c*v)^2) = 1/(Real.sqrt 2 * v^2)) : c = 1 ∨ c = -1 := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have h2 : (c*v)^2 = v^2 := by
    have hcv : Real.sqrt 2 * (c*v)^2 = Real.sqrt 2 * v^2 := by
      have := congrArg (fun x => 1/x) h
      simpa using this
    exact mul_left_cancel₀ hs.ne' hcv
  have hv2 : v^2 ≠ 0 := pow_ne_zero 2 hv
  have hc2 : c^2 * v^2 = 1 * v^2 := by
    calc c^2 * v^2 = (c*v)^2 := by ring
      _ = v^2 := h2
      _ = 1 * v^2 := by ring
  have hc : (c - 1) * (c + 1) = 0 := by
    have := mul_right_cancel₀ hv2 hc2
    nlinarith [this]
  rcases mul_eq_zero.mp hc with h | h
  · left; linarith
  · right; linarith

/-- `√2` conventions multiply the closure ratio by an integer power of `√2`; none of them
moves a ratio in the certified interval to one. -/
theorem no_sqrt_two_convention (r : ℝ) (h : 0.99972687 < r ∧ r < 0.99972689) (k : ℤ) :
    r * Real.sqrt 2 ^ k ≠ 1 := by
  have hs : (1.4142135623 : ℝ) < Real.sqrt 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by linarith
  have hpos : 0 < Real.sqrt 2 := by linarith
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have hle : Real.sqrt 2 ^ k ≤ Real.sqrt 2 ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ hs1 (by omega)
    have hinv : Real.sqrt 2 ^ (-1 : ℤ) < 1/1.4142135623 := by
      rw [zpow_neg_one, one_div]
      exact inv_strictAnti₀ (by norm_num) hs
    have : r * Real.sqrt 2 ^ k < 1 := by
      have hz : 0 < Real.sqrt 2 ^ k := zpow_pos hpos k
      calc r * Real.sqrt 2 ^ k ≤ 1 * Real.sqrt 2 ^ k := by
            apply mul_le_mul_of_nonneg_right _ hz.le; linarith
        _ < 1 := by
            rw [one_mul]; refine lt_of_le_of_lt hle (lt_trans hinv (by norm_num))
    exact this.ne
  · simp; linarith
  · have hge : Real.sqrt 2 ^ (1 : ℤ) ≤ Real.sqrt 2 ^ k := zpow_le_zpow_right₀ hs1 (by omega)
    rw [zpow_one] at hge
    have : 1 < r * Real.sqrt 2 ^ k := by nlinarith
    exact this.ne'

end PMConstants.RepairSpace
