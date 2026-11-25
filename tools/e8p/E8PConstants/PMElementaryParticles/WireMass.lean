import E8PConstants.Format
import PMConstants.Values
import PMKAutomaton.RestoringRingToll

/-!
The frozen comparison for the normalized resonant Schur model. For a
principal pulse matched to the steady two-leg current, the restoring/direct
coefficient is the area ratio times the direct/restoring duration ratio.
The common-duration case is an explicit benchmark. The duration interval
for matching the bare ratio follows from `bare_duration_ratio_sq`; the
positive-offset case has a separate necessary lower bound.
-/
namespace E8PConstants.WireMass

open PMConstants.WireMassBounds

private def bareBounds : Rat × Rat := (0.0044, 0.0045)
private def shiftedUpper : Rat := 0.00730
private def rateBounds : Rat × Rat := (0.0470, 0.0472)
private def areaRatioBounds : Rat × Rat := (0.03845, 0.03849)
private def bareDurationBounds : Rat × Rat := (1.2620, 1.2635)
private def shiftedDurationLower : Rat := 1.2612

theorem bare_bounds_valid :
    let k := PMConstants.CertifiedConstants.α / 2
    let ratio := Real.sqrt (3 * k ^ 2) / Real.sqrt (2 + k ^ 2)
    (bareBounds.1 : ℝ) < ratio ∧ ratio < (bareBounds.2 : ℝ) := by
  have h := bare_middle_heavy_bounds
  norm_num [bareBounds] at h ⊢
  exact h

theorem shifted_upper_valid (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) :
    let k := PMConstants.CertifiedConstants.α / 2
    ∃ m₁ m₂ m₃ : ℝ, 0 < m₁ ∧ m₁ < m₂ ∧ m₂ < m₃ ∧ m₂ / m₃ < (shiftedUpper : ℝ) ∧
      ∀ m : ℝ, 0 ≤ m →
        (m ^ 2 ∈ spectrum ℝ (PMAction.WireResonanceSpectrum.gram k s) ↔
          m = m₁ ∨ m = m₂ ∨ m = m₃) := by
  have h := shifted_middle_heavy_bound s hs hs₁
  norm_num [shiftedUpper] at h ⊢
  exact h

theorem rate_bounds_valid :
    (rateBounds.1 : ℝ) < Real.sqrt (3 * kRate ^ 2) / Real.sqrt (2 + kRate ^ 2) ∧
      Real.sqrt (3 * kRate ^ 2) / Real.sqrt (2 + kRate ^ 2) < (rateBounds.2 : ℝ) := by
  have h := rate_middle_heavy_bounds
  norm_num [rateBounds] at h ⊢
  exact h

theorem area_ratio_bounds_valid :
    (areaRatioBounds.1 : ℝ) < kRate ∧ kRate < (areaRatioBounds.2 : ℝ) := by
  have h := kRate_bounds
  norm_num [areaRatioBounds] at h ⊢
  exact h

theorem shifted_rate_upper_valid (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) :
    ∃ m₁ m₂ m₃ : ℝ, 0 < m₁ ∧ m₁ < m₂ ∧ m₂ < m₃ ∧ m₂ / m₃ < (rateBounds.2 : ℝ) ∧
      ∀ m : ℝ, 0 ≤ m →
        (m ^ 2 ∈ spectrum ℝ (PMAction.WireResonanceSpectrum.gram kRate s) ↔
          m = m₁ ∨ m = m₂ ∨ m = m₃) := by
  have h := shifted_rate_middle_heavy_bound s hs hs₁
  norm_num [rateBounds] at h ⊢
  exact h

/-- Monotone quotient bounds built from the two positive reference intervals.
This is an endpoint envelope for the stated inputs, with no covariance model. -/
private def referenceEnvelope (muon tau : ExpRef) : Rat × Rat :=
  ((muon.value - muon.uncertainty) / (tau.value + tau.uncertainty),
   (muon.value + muon.uncertainty) / (tau.value - tau.uncertainty))

private def firstReferences : Option (ExpRef × ExpRef) := do
  let muon ← (expRefs .muonRatio).head?
  let tau ← (expRefs .tauRatio).head?
  return (muon, tau)

/-- Both reported Schur cases fall below the frozen reference envelope. -/
theorem reference_separation :
    firstReferences.any (fun (muon, tau) =>
      decide (0 < tau.value - tau.uncertainty ∧
        bareBounds.2 < (referenceEnvelope muon tau).1 ∧
        shiftedUpper < (referenceEnvelope muon tau).1)) = true := by decide +kernel

/-- **The rate reading is below the reference envelope as well.** So the common-duration reading
of `α/2` is excluded, not only the admittance reading. -/
theorem rate_reading_still_below :
    firstReferences.any (fun (muon, tau) =>
      decide (0 < tau.value - tau.uncertainty ∧
        rateBounds.2 < (referenceEnvelope muon tau).1)) = true := by decide +kernel

/-- Square of the exact bare-model inversion. On the reference interval the
numerator increases with the reference ratio and the factor `3-r²` decreases. -/
private def bareDurationSq (r k : Rat) : Rat :=
  2 * r ^ 2 / ((3 - r ^ 2) * k ^ 2)

theorem duration_checks :
    firstReferences.any (fun (muon, tau) =>
      let (lo, hi) := referenceEnvelope muon tau
      decide (0 < lo ∧ lo ≤ hi ∧ hi < 1 ∧
        bareDurationBounds.1 ^ 2 < bareDurationSq lo areaRatioBounds.2 ∧
        bareDurationSq hi areaRatioBounds.1 < bareDurationBounds.2 ^ 2 ∧
        (3 / 2) * areaRatioBounds.2 ^ 2 * shiftedDurationLower ^ 2 < lo ^ 2)) = true := by
  decide +kernel

private theorem bareDurationSq_cast (r k : Rat) :
    (bareDurationSq r k : ℝ) = 2 * (r : ℝ) ^ 2 / ((3 - (r : ℝ) ^ 2) * (k : ℝ) ^ 2) := by
  push_cast [bareDurationSq]
  rfl

private theorem duration_sq_le {r₁ r₂ k₁ k₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (hr : r₁ ≤ r₂) (hr₂ : r₂ < 1) (hk₂ : 0 < k₂) (hk : k₂ ≤ k₁) :
    2 * r₁ ^ 2 / ((3 - r₁ ^ 2) * k₁ ^ 2) ≤
      2 * r₂ ^ 2 / ((3 - r₂ ^ 2) * k₂ ^ 2) := by
  have hrSq := pow_le_pow_left₀ hr₁ hr 2
  have hr₂Sq : r₂ ^ 2 ≤ 1 := (pow_le_pow_left₀ (hr₁.trans hr) hr₂.le 2).trans (by norm_num)
  have hden : 0 < 3 - r₂ ^ 2 := by linarith
  apply div_le_div₀ (by positivity) (by linarith) (mul_pos hden (by positivity))
  exact mul_le_mul (by linarith) (pow_le_pow_left₀ hk₂.le hk 2) (by positivity)
    (hden.le.trans (by linarith))

/-- Exact duration enclosure for a positive bare-model duration ratio
whose mass ratio is within the frozen reference envelope. -/
theorem bare_duration_enclosure {muon tau : ExpRef}
    (hRef : firstReferences = some (muon, tau)) {r d : ℝ}
    (hlo : ((referenceEnvelope muon tau).1 : ℝ) ≤ r)
    (hhi : r ≤ ((referenceEnvelope muon tau).2 : ℝ))
    (hd : 0 < d)
    (hRatio : r = Real.sqrt (3 * (kRate * d) ^ 2) / Real.sqrt (2 + (kRate * d) ^ 2)) :
    (bareDurationBounds.1 : ℝ) < d ∧ d < (bareDurationBounds.2 : ℝ) := by
  have hchecks := duration_checks
  rw [hRef] at hchecks
  simp only [Option.any, decide_eq_true_eq] at hchecks
  obtain ⟨hr₀, _, hr₁, hlow, hhigh, _⟩ := hchecks
  have hr₀' : 0 < ((referenceEnvelope muon tau).1 : ℝ) := by exact_mod_cast hr₀
  have hr₁' : ((referenceEnvelope muon tau).2 : ℝ) < 1 := by exact_mod_cast hr₁
  have hk₀ : (0 : ℝ) < (areaRatioBounds.1 : ℝ) := by norm_num [areaRatioBounds]
  have hk := area_ratio_bounds_valid
  have hs := PMAction.WireResonanceSpectrum.bare_duration_ratio_sq
    (hk₀.trans hk.1).ne' hRatio
  constructor
  · apply (sq_lt_sq₀ (by norm_num [bareDurationBounds]) hd.le).mp
    rw [hs]
    refine lt_of_lt_of_le ?_ (duration_sq_le hr₀'.le hlo (hhi.trans_lt hr₁')
      (hk₀.trans hk.1) hk.2.le)
    rw [← bareDurationSq_cast]
    exact_mod_cast hlow
  · apply (sq_lt_sq₀ hd.le (by norm_num [bareDurationBounds])).mp
    rw [hs]
    refine lt_of_le_of_lt (duration_sq_le (hr₀'.le.trans hlo) hhi hr₁' hk₀ hk.1.le) ?_
    rw [← bareDurationSq_cast]
    exact_mod_cast hhigh

/-- The uniform shifted-spectrum bound forces a minimum duration ratio
whenever a positive-offset model reaches the frozen reference envelope. -/
theorem shifted_duration_lower {muon tau : ExpRef}
    (hRef : firstReferences = some (muon, tau)) {r d : ℝ}
    (hlo : ((referenceEnvelope muon tau).1 : ℝ) ≤ r) (hd : 0 < d)
    (hspectrum : r < Real.sqrt (3 / 2) * (kRate * d)) :
    (shiftedDurationLower : ℝ) < d := by
  have hchecks := duration_checks
  rw [hRef] at hchecks
  simp only [Option.any, decide_eq_true_eq] at hchecks
  obtain ⟨hr₀, _, _, _, _, hrequired⟩ := hchecks
  have hr₀' : 0 < ((referenceEnvelope muon tau).1 : ℝ) := by exact_mod_cast hr₀
  have hk₀ : (0 : ℝ) < (areaRatioBounds.1 : ℝ) := by norm_num [areaRatioBounds]
  have hk := area_ratio_bounds_valid
  by_contra! h
  have hbound : Real.sqrt (3 / 2) * (kRate * d) ≤
      Real.sqrt (3 / 2) * ((areaRatioBounds.2 : ℝ) * (shiftedDurationLower : ℝ)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul hk.2.le h hd.le (hk₀.trans (hk.1.trans hk.2)).le) (Real.sqrt_nonneg _)
  have hlt : Real.sqrt (3 / 2) * ((areaRatioBounds.2 : ℝ) * (shiftedDurationLower : ℝ)) <
      ((referenceEnvelope muon tau).1 : ℝ) := by
    apply (sq_lt_sq₀ (by norm_num [areaRatioBounds, shiftedDurationLower]) hr₀'.le).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← mul_assoc]
    have hcast :
        ((3 / 2 * areaRatioBounds.2 ^ 2 * shiftedDurationLower ^ 2 : Rat) : ℝ) <
          (((referenceEnvelope muon tau).1 ^ 2 : Rat) : ℝ) := by exact_mod_cast hrequired
    push_cast at hcast
    exact hcast
  exact (hspectrum.trans_le (hbound.trans hlt.le)).not_ge hlo

/-- The bare-model duration window has one integer restoring span
at a 24-tick direct flip. This is a test of the booked span. -/
theorem bare_short_clock (ticks : ℕ) (ht : 0 < ticks) :
    ((bareDurationBounds.1 : ℝ) < 24 / (ticks : ℝ) ∧
      24 / (ticks : ℝ) < (bareDurationBounds.2 : ℝ)) ↔ ticks = 19 := by
  have ht' : 0 < (ticks : ℝ) := by exact_mod_cast ht
  rw [lt_div_iff₀ ht', div_lt_iff₀ ht']
  constructor
  · rintro ⟨hlo, hhi⟩
    norm_num [bareDurationBounds] at hlo hhi
    have hlo' : (18 : ℝ) < ticks := by linarith
    have hhi' : (ticks : ℝ) < 20 := by linarith
    have hloNat : 18 < ticks := by exact_mod_cast hlo'
    have hhiNat : ticks < 20 := by exact_mod_cast hhi'
    omega
  · rintro rfl
    norm_num [bareDurationBounds]

open PMKAutomaton in
/-- When the receiver keeps the marker for the entire bare-model restoring
span, the required short-clock duration lands on the record side. -/
theorem bare_short_retained_exit_excluded (either : Bool)
    (q : RestoringRingHistory.History) (hLive : RestoringRingHistory.liveExit either q = true)
    (ticks : ℕ) (ht : 0 < ticks)
    (hWindow : (bareDurationBounds.1 : ℝ) < 24 / (ticks : ℝ) ∧
      24 / (ticks : ℝ) < (bareDurationBounds.2 : ℝ)) :
    RingReceiver.slotValue
      (((RingReceiver.tick PMAction.Delta either)^[ticks] (RestoringRingHistory.seed q)).2.2.2)
      (42, false) = false := by
  rw [RestoringRingHistory.successful_live_slot_even either q hLive,
    (bare_short_clock ticks ht).mp hWindow]
  rfl

def lines : List String :=
  ["Charged-lepton wire m_mu/m_tau (unscored Schur benchmark)",
   "  Normalization: common unit crossing, real resonance, steady two-leg current match.",
   "  Historical benchmark (coefficient set to alpha/2):",
   s!"    Bare (static offset = 0): {ratDecimal bareBounds.1 4} < m_2/m_3 < {ratDecimal bareBounds.2 4}.",
   s!"    Shifted (0 < static offset < 1): three positive modes, m_2/m_3 < {ratDecimal shiftedUpper 5}.",
   "  Rate reading ((2/pi) arcsin sqrt(alpha/2), common duration):",
   s!"    Bare: {ratDecimal rateBounds.1 4} < m_2/m_3 < {ratDecimal rateBounds.2 4}.",
   s!"    Shifted (0 < static offset < 1): m_2/m_3 < {ratDecimal rateBounds.2 4}."] ++
  (match firstReferences with
   | none => ["  No frozen m_mu/m_tau reference pair."]
   | some (muon, tau) =>
     let center := muon.value / tau.value
     let (lo, hi) := referenceEnvelope muon tau
     [s!"  Frozen reference central ratio: {ratDecimal center 8} ({muon.citation}, {tau.citation}).",
      s!"  Reference endpoint envelope: [{fixedDecimal (lowerScaled lo 8) 8}, {fixedDecimal (upperScaled hi 8) 8}].",
      "  The common-duration model falls below the envelope throughout the displayed offset range.",
      s!"  Bare-model required duration ratio: ({ratDecimal bareDurationBounds.1 4}, {ratDecimal bareDurationBounds.2 4}).",
      "  A 24-tick direct flip requires a 19-tick restoring span in the bare model.",
      "  The closed ring has no live exit at tick 19 when the marker stays on the ring.",
      s!"  Positive-offset necessary duration ratio: > {ratDecimal shiftedDurationLower 4}."]) ++
  ["  Duration ratios above are direct/restoring diagnostic constraints from the reference.",
   "  The native rates and the full-wall mass spectrum are open."]

end E8PConstants.WireMass
