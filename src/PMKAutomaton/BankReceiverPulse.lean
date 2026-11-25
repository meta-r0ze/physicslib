import PMKAutomaton.RestoringExtraction
import PMKAutomaton.ClockedRootTrials
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Coherent timing of the staged bank exchange

With the two inputs already staged on the native receiver at site zero,
the existing receiver root exchanges the two carrier doublets. The
positive principal half-pulse gives the exact permutation including
phase. The spatial work that stages the inputs has a separate account.
-/

namespace PMKAutomaton.BankReceiverPulse

open PMAction Matrix RootTransferPhase
open TwoSiteHandoff (Site Carrier State field receiverRoot receiverRoot_involutive)

/-- On staged inputs the root acts only on the receiver's live and record
doublets. The spectator sender stays intact. -/
theorem receiver_on_staged_field (s : State (Fin 2 → ℂ)) :
    receiverRoot.permMatrix ℂ *ᵥ field s =
      field (OpenReferenceFlow.exchangeAt 0 s) := by
  let u := (TwoSiteHandoff.step false).symm s
  have hu : TwoSiteHandoff.step false u = s := (TwoSiteHandoff.step false).apply_symm_apply s
  have h := TwoSiteHandoff.native_step_observed true u
  change (receiverRoot.permMatrix ℂ * TwoSiteHandoff.hop.permMatrix ℂ) *ᵥ field u =
    field (TwoSiteHandoff.step true u) at h
  rw [← Matrix.mulVec_mulVec, TwoSiteHandoff.arrivals_observed, hu] at h
  have hs : TwoSiteHandoff.step true u =
      OpenReferenceFlow.exchangeAt 0 (TwoSiteHandoff.step false u) := rfl
  rwa [hs, hu] at h

/-- The native comparison measures the discrepancy between the already
staged receiver and bank; the other site's inputs contribute no flag. -/
theorem staged_receiver_flag (s : State (Fin 2 → ℂ)) :
    CommonResponse.stateFlag (receiverRoot.permMatrix ℂ) (field s) =
      CommonResponse.nsq ((s 0).1 - (s 0).2) / 2 := by
  let u := (TwoSiteHandoff.step false).symm s
  have hu : TwoSiteHandoff.step false u = s := (TwoSiteHandoff.step false).apply_symm_apply s
  have h₀ : s 0 = u 1 := by
    rw [← hu, (TwoSiteHandoff.step_trace false u).1]
    rfl
  rw [h₀, ← hu, TwoSiteHandoff.exchange_flag]

/-- The staged bank exchange and the reload use the same root operation.
The condition on `q` expresses one quarter-time in `q` substrate ticks
under the two-tick statistical-pair convention. -/
theorem staged_exchange_in_ticks (s : State (Fin 2 → ℂ)) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1 / 2) (q : ℕ)
    (hclock : quarterTime p = (q : ℝ) / 2) :
    NormedSpace.exp ((-((2 * q : ℕ) : ℂ) * Complex.I) •
      ClockedRootTrials.tickGenerator receiverRoot p) *ᵥ field s =
      field (OpenReferenceFlow.exchangeAt 0 s) := by
  rw [show ((2 * q : ℕ) : ℂ) = ((((2 * q : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
    ClockedRootTrials.phase_in_ticks]
  have ht : ((2 * q : ℕ) : ℝ) / 2 = 2 * quarterTime p := by
    rw [hclock]
    push_cast
    ring
  rw [ht, TwoSiteHandoff.receiver_half_pulse p hp hp']
  exact receiver_on_staged_field s

private abbrev probe : Site × Carrier := (0, ActualRootRepair.label (.inl 0))

private theorem probe_moves : receiverRoot probe ≠ probe := by decide +kernel

/-- The changed-label probability of two trials of this receiver root. -/
noncomputable def bankTrialWeight (p : ℝ) : ℝ :=
  RootClockCalibration.trialWeight receiverRoot probe p

/-- The receiver trial observable is exactly what fixes a specified
whole-tick principal clock. The integer itself is a measured or derived
clock input. -/
theorem trial_weight_iff_quarter_ticks (p : ℝ) (hp' : p < 1 / 2)
    (q : ℕ) (hq : 0 < q) :
    quarterTime p = (q : ℝ) / 2 ↔
      bankTrialWeight p = (1 - Real.exp (-(Real.pi / (q : ℝ)))) / 2 := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq₀ := hq'.ne'
  constructor
  · intro hclock
    have hgap : Real.pi = (q : ℝ) * gap p := by
      unfold quarterTime at hclock
      have hg : gap p ≠ 0 := by
        intro hz
        rw [hz, mul_zero, div_zero] at hclock
        linarith
      have h := (div_eq_iff (mul_ne_zero two_ne_zero hg)).1 hclock
      linarith only [h, show (q : ℝ) / 2 * (2 * gap p) = (q : ℝ) * gap p by ring]
    have h := ClockedRootTrials.principal_weight_in_ticks receiverRoot receiverRoot_involutive
      probe probe_moves p hp' (2 * q) (by omega) (by push_cast; linarith)
    have htime : -(2 * Real.pi) / ((2 * q : ℕ) : ℝ) = -(Real.pi / (q : ℝ)) := by
      push_cast
      field_simp [hq₀]
    rw [htime] at h
    exact h
  · intro h
    have hg := RootClockCalibration.gap_from_trials receiverRoot receiverRoot_involutive probe
      probe_moves p hp'
    change gap p = -Real.log (1 - 2 * bankTrialWeight p) at hg
    rw [h, show 1 - 2 * ((1 - Real.exp (-(Real.pi / (q : ℝ)))) / 2) =
      Real.exp (-(Real.pi / (q : ℝ))) by ring, Real.log_exp] at hg
    have hgap : gap p = Real.pi / (q : ℝ) := by rw [hg, neg_neg]
    rw [quarterTime, hgap]
    field_simp [Real.pi_ne_zero, hq₀]

/-- A trial probability as small as the geometric handoff weight cannot
calibrate a staged half-pulse that fits in the 86-tick receiver block. -/
theorem geometric_trial_exceeds_block (p : ℝ) (hp' : p < 1 / 2)
    (q : ℕ) (hq : 0 < q) (hclock : quarterTime p = (q : ℝ) / 2)
    (hweight : bankTrialWeight p = PMSubstrate.causalCoupling) : 86 < 2 * q := by
  by_contra! hfit
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq43 : (q : ℝ) ≤ 43 := by exact_mod_cast (show q ≤ 43 by omega)
  have hx : (3 : ℝ) / 43 < Real.pi / (q : ℝ) := by
    calc
      (3 : ℝ) / 43 < Real.pi / 43 := div_lt_div_of_pos_right Real.pi_gt_three (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_left Real.pi_pos.le hq' hq43
  have he := Real.add_one_le_exp (Real.pi / (q : ℝ))
  have he' : (46 : ℝ) / 43 < Real.exp (Real.pi / (q : ℝ)) := by linarith
  have hinv := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 46 / 43) he'
  rw [one_div, ← Real.exp_neg] at hinv
  have hw := (trial_weight_iff_quarter_ticks p hp' q hq).mp hclock
  rw [hweight] at hw
  linarith [PMConstants.CertifiedConstants.alpha_bounds.2]

end PMKAutomaton.BankReceiverPulse
