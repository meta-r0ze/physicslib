import PMKAutomaton.Machine.RootPulseEvents
import PMAction.OtherWallFlipEvent
import PMKAutomaton.OddReferenceSource
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# What calibrates the clock of a moving carrier root

Coherent samples at integer ticks see the phase gap modulo a full turn.
The squared statistical transfer of the same reconstructed root gives a
second observable, the two-trial probability of changing the root label.
That probability fixes the gap on the admissible lazy-transfer interval.
The resulting clock test concerns a supplied pair of trials and a supplied
coherent pulse. Their physical admission and time calibration are inputs.

## Interface, clock and admission notes

### Root calibration

A moving label reads the full complex phase of the reconstructed pulse.
Gaps π and 3π give the same coherent history at integer ticks, including
a reflection on the first tick. See `phase_alias_iff`,
`integer_samples_agree` and `ambiguous_exchange_clock`.

A two-trial test can instead read the probability on the two record-port
labels of the prepared vector-class odd live seed
(`RootClockCalibration.odd_seed_trial_weight`). In statistical-pair time,
a reflection at elapsed time `N` requires `−N log(1−2w) = π + 2πk`. The
principal calibration gives `w = (1 − exp(−π/N))/2` and can also use a
coherent flag on the principal range (`exchange_tick_iff`,
`principal_trial_weight`, `principal_flag_inj`).

The reference excursion retains the request bits and advances to phase
2. A moved input changes exactly when the bits differ
(`ClockedRootTrials.pair_endpoint`, `shared_fire`). With the same
statistical pair occupying two substrate ticks, the coherent reflection
test becomes `−N log(1−2w)/2 = π + 2πk`. Its principal weight is
`(1 − exp(−2π/N))/2` (`exchange_in_ticks_iff`, `principal_weight_in_ticks`).

On a moving input, the action that charges each change in the two-tick
trace at the same supplied price `c` takes the values `0, c, c, 2c` on
the four retained histories. The idle and double-fire histories have the
same endpoint and different actions for nonzero `c`. The equal-prior
Gibbs law for these four histories factorizes, with each slot's rate
`p = exp(−βc)/(1 + exp(−βc))`. The expected action is `2cp`, and the
endpoint-change weight is `2p(1−p)` (`history_action_additive`,
`no_endpoint_action`, `history_pmf_factorizes`,
`expected_history_action`, `history_endpoint_weight`).

The physical protocol still needs to admit the four equally counted
histories, identify and price the two local registrations, and place its
coherent pulse on the same clock.

The isolated trial's requests persist unchanged. Its carrier is idle
in phases 2–42 (`iterate_controls`, `quiet_trial_tick`,
`trial_period_endpoint`). The [admission check](OVERVIEW.md#admission)
enumerates the four retained pairs. The shared-request preparation
has only the two equal-bit histories. Physical prior counts require
the actual controller background.

### Clock placement

Spatial stabilizers fix the scalar phase. This alone places no
operation. The prescribed trial has its own phases 0 and 1. In
the wider closed root-excursion family the one-phase mask at
phase 2 fires at phases 1 and 2
(`Components.shifted_excursion_boundaries`). The period and the
non-idle minimum are the same as for the prescribed excursion
(`ClockControlledRoot.cycle_closes`,
`Components.shifted_excursion_same_cost`,
`CarrierReferenceCycle.minimum_nonidle_carrier_cost`). Fixing
physical pulse or exchange slots still needs the joint placement
and timing T/G. The shift example concerns the excursion family.
It does not move a prescribed trial slot.
-/

noncomputable section
namespace PMKAutomaton.RootClockCalibration

open Matrix PMAction RootTransferPhase
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (e : Equiv.Perm n) (he : Function.Involutive e)
variable (a : n) (moves : e a ≠ a)

private theorem exp_angle_iff (x y : ℝ) :
    Complex.exp (-(x : ℂ) * Complex.I) = Complex.exp (-(y : ℂ) * Complex.I) ↔
      ∃ k : ℤ, x - y = (k : ℝ) * (2 * Real.pi) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have h := congrArg Complex.im hk
    simp [Complex.mul_im] at h
    push_cast
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    refine Complex.ext ?_ ?_
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
      linarith

/-- The observed probability of a changed label after two lazy trials,
on a known moved input. -/
def trialWeight (e : Equiv.Perm n) (a : n) (p : ℝ) : ℝ :=
  ((transfer e p * transfer e p) (e a) a).re

include he a moves

/-- A moving basis label detects the full complex phase through its diagonal
amplitude. The full coherent maps coincide exactly at a full-turn difference. -/
theorem phase_alias_iff (p q t u : ℝ) :
    phase e p t = phase e q u ↔
      ∃ k : ℤ, gap p * t - gap q * u = (k : ℝ) * (2 * Real.pi) := by
  rw [← exp_angle_iff]
  constructor
  · intro h
    have hd := congrArg (fun M : Matrix n n ℂ => M a a) h
    simp only [RootPulseEvents.phase_diagonal e he, moves, ite_false] at hd
    linear_combination 2 * hd
  · intro h
    rw [phase_formula e he, phase_formula e he, h]

/-- Equality of the full coherent map after one unit tick implies equality
at every integer tick, including after the substrate's whole clock period. -/
theorem integer_samples_agree (p q : ℝ) (h : phase e p 1 = phase e q 1) (N : ℕ) :
    phase e p N = phase e q N := by
  obtain ⟨k, hk⟩ := (phase_alias_iff e he a moves p q 1 1).mp h
  have hg : gap p - gap q = (k : ℝ) * (2 * Real.pi) := by simpa using hk
  refine (phase_alias_iff e he a moves p q N N).mpr ⟨k * (N : ℤ), ?_⟩
  calc
    gap p * N - gap q * N = (gap p - gap q) * N := by ring
    _ = _ := by rw [hg]; push_cast; ring

theorem trial_weight (p : ℝ) :
    trialWeight e a p = (1 - RootTransferPhase.residual p ^ 2) / 2 := by
  unfold trialWeight
  rw [RootTransferPhase.square e he]
  simp [InvolutionSpectral.plus, InvolutionSpectral.minus, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, moves, he a, Complex.mul_re, ← Complex.ofReal_pow]
  ring

theorem gap_from_trials (p : ℝ) (hp : p < 1 / 2) :
    gap p = -Real.log (1 - 2 * trialWeight e a p) := by
  rw [trial_weight e he a moves p, show 1 - 2 * ((1 - RootTransferPhase.residual p ^ 2) / 2) =
    RootTransferPhase.residual p ^ 2 by ring, ← heat_scalar p hp, Real.log_exp, neg_neg]

/-- The two-trial statistic separates all the coherent clock aliases in
the admissible interval. -/
theorem trial_weight_inj (p q : ℝ) (hp : p < 1 / 2) (hq : q < 1 / 2)
    (h : trialWeight e a p = trialWeight e a q) : p = q := by
  have hg : gap p = gap q := by
    rw [gap_from_trials e he a moves p hp, gap_from_trials e he a moves q hq, h]
  have hl : Real.log (RootTransferPhase.residual p) = Real.log (RootTransferPhase.residual q) := by
    unfold gap at hg
    linarith
  have hr := congrArg Real.exp hl
  rw [Real.exp_log (residual_positive p hp), Real.exp_log (residual_positive q hq)] at hr
  unfold RootTransferPhase.residual at hr
  linarith

/-- A single coherent comparison flag also fixes the rate if the
one-tick gap is known independently to lie in the first half-turn. -/
theorem principal_flag_inj (p q : ℝ) (hp : p < 1 / 2) (hq : q < 1 / 2)
    (hpBand : gap p ∈ Set.Icc 0 Real.pi) (hqBand : gap q ∈ Set.Icc 0 Real.pi)
    (h : InterferenceReadout.flagProbability (phase e p 1) a =
      InterferenceReadout.flagProbability (phase e q 1) a) : p = q := by
  simp only [RootPulseEvents.phase_flag e he, moves, ite_false, mul_one] at h
  have hg : gap p = gap q := Real.strictAntiOn_cos.injOn hpBand hqBand (by linarith)
  apply trial_weight_inj e he a moves p q hp hq
  rw [trial_weight e he a moves p, trial_weight e he a moves q, ← heat_scalar p hp,
    ← heat_scalar q hq, hg]

/-- Given the independently specified trial observable, this is the exact
whole-tick condition for an exchange. The integer records its phase winding. -/
theorem exchange_tick_iff (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) (N : ℕ) :
    phase e p N = e.permMatrix ℂ ↔
      ∃ k : ℤ, (-Real.log (1 - 2 * trialWeight e a p)) * N =
        Real.pi + (k : ℝ) * (2 * Real.pi) := by
  rw [← RootTransferPhase.half_pulse e he p hp hp',
    phase_alias_iff e he a moves, ← gap_from_trials e he a moves p hp']
  have hπ : gap p * (2 * quarterTime p) = Real.pi := by
    have h := RootPulseEvents.quarter_angle p hp hp'
    linarith
  rw [hπ]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by linarith⟩

/-- Two admissible lazy transfers give exactly the same coherent data
at every integer tick and complete the same exchange at the first tick.
The independent changed-label test distinguishes them. -/
theorem ambiguous_exchange_clock :
    ∃ p q : ℝ, 0 < p ∧ p < 1 / 2 ∧ 0 < q ∧ q < 1 / 2 ∧
      phase e p 1 = e.permMatrix ℂ ∧
      (∀ N : ℕ, phase e p N = phase e q N) ∧
      trialWeight e a p ≠ trialWeight e a q := by
  let p := OtherWallFlipEvent.attempt (Real.pi / 2)
  let q := OtherWallFlipEvent.attempt (3 * Real.pi / 2)
  have hp : 0 < p ∧ p < 1 / 2 := OtherWallFlipEvent.attempt_range (by positivity)
  have hq : 0 < q ∧ q < 1 / 2 := OtherWallFlipEvent.attempt_range (by positivity)
  have hgp : gap p = Real.pi := by
    have h := OtherWallFlipEvent.attempt_probability (Real.pi / 2)
    change -gap p / 2 = -(Real.pi / 2) at h
    linarith
  have hgq : gap q = 3 * Real.pi := by
    have h := OtherWallFlipEvent.attempt_probability (3 * Real.pi / 2)
    change -gap q / 2 = -(3 * Real.pi / 2) at h
    linarith
  have exchange : phase e p 1 = e.permMatrix ℂ := by
    have h := (exchange_tick_iff e he a moves p hp.1 hp.2 1).mpr (by
      rw [← gap_from_trials e he a moves p hp.2, hgp]
      exact ⟨0, by simp⟩)
    simpa only [Nat.cast_one] using h
  have same : phase e p 1 = phase e q 1 := by
    apply (phase_alias_iff e he a moves p q 1 1).mpr
    rw [hgp, hgq]
    exact ⟨-1, by norm_num; ring⟩
  refine ⟨p, q, hp.1, hp.2, hq.1, hq.2, exchange, integer_samples_agree e he a moves p q same, ?_⟩
  intro h
  have hpq := trial_weight_inj e he a moves p q hp.2 hq.2 h
  rw [hpq, hgq] at hgp
  linarith [Real.pi_pos]

/-- The principal exchange condition gives the exact required two-trial
probability for a positive whole-tick duration. -/
theorem principal_trial_weight (p : ℝ) (hp' : p < 1 / 2) (N : ℕ) (hN : 0 < N)
    (principal : gap p * N = Real.pi) :
    trialWeight e a p = (1 - Real.exp (-Real.pi / N)) / 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : gap p = Real.pi / N := (eq_div_iff hn.ne').mpr principal
  rw [trial_weight e he a moves p, ← heat_scalar p hp', hg, neg_div]

omit he a moves in
/-- Reading the carrier distribution of the occupied odd seed and testing
the record port after two statistical trials gives the same calibration.
The detector can sum the two record signs. -/
theorem odd_seed_trial_weight (p : ℝ) :
    let initial : ActualRootRepair.C → ℂ :=
      fun v => (Complex.normSq (OddReferenceSource.localMode 0 false false v) : ℂ)
    let T := transfer ActualRootRepair.root p
    (∑ i : Fin 2, (((T * T) *ᵥ initial) (ActualRootRepair.label (.inr i))).re) =
      trialWeight ActualRootRepair.root (ActualRootRepair.label (.inl 0)) p := by
  dsimp only
  let initial : ActualRootRepair.C → ℂ :=
    fun v => (Complex.normSq (OddReferenceSource.localMode 0 false false v) : ℂ)
  have hseed : OddReferenceSource.localMode 0 false false =
      ActualRootRepair.pack OddReferenceSource.oddReference 0 :=
    OddReferenceSource.first_wall_ports false
  have hr (i : Fin 2) : initial (ActualRootRepair.label (.inr i)) = 0 := by
    simp [initial, hseed, ActualRootRepair.pack, ActualRootRepair.encoded_coordinate]
  have hl (i : Fin 2) : initial (ActualRootRepair.label (.inl i)) =
      (Complex.normSq (OddReferenceSource.oddReference i) : ℂ) := by
    simp [initial, hseed, ActualRootRepair.pack, ActualRootRepair.encoded_coordinate]
  have he := CarrierEvents.reflection_involutive 0
  have hm := ActualRootRepair.label_moves (.inl 0)
  let T := transfer ActualRootRepair.root p
  have hport (i : Fin 2) : ((T * T) *ᵥ initial) (ActualRootRepair.label (.inr i)) =
      (((1 - RootTransferPhase.residual p ^ 2) / 2 : ℝ) : ℂ) *
        initial (ActualRootRepair.label (.inl i)) := by
    dsimp only [T]
    rw [RootTransferPhase.square _ he]
    simp [InvolutionSpectral.plus, InvolutionSpectral.minus, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.permMatrix_mulVec, hr, ActualRootRepair.label_exchange,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_pow]
    ring
  change (∑ i : Fin 2, (((T * T) *ᵥ initial) (ActualRootRepair.label (.inr i))).re) = _
  simp_rw [hport, hl, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← Finset.mul_sum, ← LinkExpansion.nsq_eq, OddReferenceSource.odd_reference_population,
    mul_one, trial_weight _ he _ hm]

end PMKAutomaton.RootClockCalibration
