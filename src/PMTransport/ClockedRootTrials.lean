import PMAction.EventAccounting
import PMTransport.Machine.ClockControlledRoot
import PMTransport.Machine.RootTransferAccounting
import PMTransport.RootClockCalibration

/-!
# A two-tick root trial schedule

The boundaries of the native reference excursion provide two consecutive
opportunities to apply the same E8 reflection. The update retains both
request controls. Their joint law controls whether the carrier moves after
the pair. In the two-tick statistical model the logarithmic generator is
normalized to the pair.
-/

noncomputable section
namespace PMTransport.ClockedRootTrials

open Matrix PMSubstrate.Lattices PMAction
open scoped Matrix.Norms.Operator

def fire (requests : Bool × Bool) (t : Fin Delta) : Bool :=
  if t = 0 then requests.1 else if t = 1 then requests.2 else false

/-- A substrate clock tick controlled by two retained requests. -/
def tick : Equiv.Perm ((Bool × Bool) × ClockControlledRoot.State) :=
  Equiv.prodCongrRight fun requests =>
    (ClockControlledRoot.controlled (fire requests)).trans ClockControlledRoot.clock

theorem ticks_zero_one (requests : Bool × Bool) (z : SubstrateReflection.Lattice) :
    tick (requests, (z, 0)) =
      (requests, (if requests.1 then SubstrateReflection.reflect z else z, 1)) := by
  change (requests, (if fire requests 0 then SubstrateReflection.reflect z else z,
    finRotate Delta 0)) = _
  simp [fire]

theorem ticks_one_two (requests : Bool × Bool) (z : SubstrateReflection.Lattice) :
    tick (requests, (z, 1)) =
      (requests, (if requests.2 then SubstrateReflection.reflect z else z, 2)) := by
  change (requests, (if fire requests 1 then SubstrateReflection.reflect z else z,
    finRotate Delta 1)) = _
  simp [fire]

theorem pair_endpoint (a b : Bool) (z : SubstrateReflection.Lattice) :
    tick (tick ((a, b), (z, 0))) =
      ((a, b), (if a ≠ b then SubstrateReflection.reflect z else z, 2)) := by
  rw [ticks_zero_one, ticks_one_two]
  cases a <;> cases b <;> simp [SubstrateReflection.involutive z]

/-- A single retained request drives both boundaries of the original excursion. -/
theorem shared_fire (b : Bool) (t : Fin Delta) :
    fire (b, b) t = (b && ClockControlledRoot.fire CarrierReferenceCycle.excursionMask t) := by
  revert t
  cases b <;> decide +kernel

/-- On an input moved by the root, these are exactly the histories with
a changed endpoint in the scheduled experiment. -/
theorem endpoint_changed_iff (a b : Bool) (z : SubstrateReflection.Lattice)
    (hmoves : SubstrateReflection.reflect z ≠ z) :
    (tick (tick ((a, b), (z, 0)))).2.1 ≠ z ↔ a ≠ b := by
  rw [pair_endpoint]
  by_cases h : a = b <;> simp [h, hmoves]

theorem shared_request_returns (b : Bool) (z : SubstrateReflection.Lattice) :
    tick (tick ((b, b), (z, 0))) = ((b, b), (z, 2)) := by
  rw [pair_endpoint]
  simp

open PersistenceMechanics.Gibbs RootTransferAccounting

/-- Charge each actual lattice change in the two-tick trace once, at the
supplied per-change action. A return can contain two registrations. -/
def historyAction (cost : ℝ) (z : SubstrateReflection.Lattice)
    (requests : Bool × Bool) : ℝ :=
  let middle := tick (requests, (z, 0))
  let last := tick middle
  (if middle.2.1 ≠ z then cost else 0) +
    (if last.2.1 ≠ middle.2.1 then cost else 0)

theorem history_action_additive (cost : ℝ) (z : SubstrateReflection.Lattice)
    (hmoves : SubstrateReflection.reflect z ≠ z) (requests : Bool × Bool) :
    historyAction cost z requests =
      attemptAction cost requests.1 + attemptAction cost requests.2 := by
  rcases requests with ⟨a, b⟩
  dsimp only [historyAction]
  rw [pair_endpoint, ticks_zero_one]
  cases a <;> cases b <;> simp [attemptAction, hmoves, Ne.symm hmoves]

/-- This history returns to its input while moving at both slots. -/
theorem double_fire_action (cost : ℝ) (z : SubstrateReflection.Lattice)
    (hmoves : SubstrateReflection.reflect z ≠ z) :
    historyAction cost z (true, true) = 2 * cost := by
  rw [history_action_additive cost z hmoves]
  simp [attemptAction, two_mul]

/-- The final lattice position alone cannot account for the two moves
in a returning history with nonzero per-change action. -/
theorem no_endpoint_action (cost : ℝ) (z : SubstrateReflection.Lattice)
    (hmoves : SubstrateReflection.reflect z ≠ z) (hcost : cost ≠ 0)
    (price : SubstrateReflection.Lattice → ℝ) :
    ¬ ∀ requests : Bool × Bool,
      historyAction cost z requests = price (tick (tick (requests, (z, 0)))).2.1 := by
  intro h
  have idle := h (false, false)
  have fired := h (true, true)
  rw [shared_request_returns, history_action_additive cost z hmoves] at idle
  rw [shared_request_returns, double_fire_action cost z hmoves] at fired
  simp [attemptAction] at idle
  exact hcost (by linarith)

/-- Apply the equal-count Gibbs law to the four retained request histories. -/
def historyMass (β cost : ℝ) (z : SubstrateReflection.Lattice) (requests : Bool × Bool) : ℝ :=
  probability β (historyAction cost z) requests

private theorem single_attempt_mass (β cost : ℝ) (b : Bool) :
    probability β (attemptAction cost) b = EventAccounting.binaryMass (gibbsRate β cost) b := by
  cases b
  · have h := probabilities_sum_one β (attemptAction cost)
    simp only [Fintype.sum_bool] at h
    change probability β (attemptAction cost) false = 1 - gibbsRate β cost
    unfold gibbsRate
    linarith
  · rfl

/-- With all four histories equally counted before survival filtering,
pricing local movement produces the product law on a moving root orbit. -/
theorem history_mass_factorizes (β cost : ℝ) (z : SubstrateReflection.Lattice)
    (hmoves : SubstrateReflection.reflect z ≠ z) (requests : Bool × Bool) :
    historyMass β cost z requests =
      EventAccounting.binaryMass (gibbsRate β cost) requests.1 *
        EventAccounting.binaryMass (gibbsRate β cost) requests.2 := by
  have hw (r : Bool × Bool) : weight β (historyAction cost z r) =
      weight β (attemptAction cost r.1) * weight β (attemptAction cost r.2) := by
    rw [history_action_additive cost z hmoves, weight_add]
  have hpart : partition β (historyAction cost z) = partition β (attemptAction cost) ^ 2 := by
    simp only [partition, Fintype.sum_prod_type, hw, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  rw [← single_attempt_mass, ← single_attempt_mass]
  simp only [historyMass, probability, hw, hpart, pow_two, mul_div_mul_comm]

theorem expected_history_action (β cost : ℝ) (z : SubstrateReflection.Lattice)
    (hmoves : SubstrateReflection.reflect z ≠ z) :
    (∑ requests, historyMass β cost z requests * historyAction cost z requests) =
      2 * cost * gibbsRate β cost := by
  simp only [history_mass_factorizes β cost z hmoves, history_action_additive cost z hmoves,
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp [attemptAction, EventAccounting.binaryMass]
  ring

def changedWeight (mass : Bool × Bool → ℝ) : ℝ :=
  mass (true, false) + mass (false, true)

/-- With equal Bernoulli marginals, the parity statistic detects the
joint true-true weight. A common request has joint weight p and cancels. -/
theorem changed_weight (mass : Bool × Bool → ℝ) (p : ℝ)
    (first : mass (true, false) + mass (true, true) = p)
    (second : mass (false, true) + mass (true, true) = p) :
    changedWeight mass = 2 * (p - mass (true, true)) := by
  unfold changedWeight
  linarith

open RootTransferPhase

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (e : Equiv.Perm n) (he : Function.Involutive e) (a : n) (moves : e a ≠ a)

include he moves in
theorem matches_independent_trial_weight (mass : Bool × Bool → ℝ) (p : ℝ)
    (first : mass (true, false) + mass (true, true) = p)
    (second : mass (false, true) + mass (true, true) = p) :
    changedWeight mass = RootClockCalibration.trialWeight e a p ↔
      mass (true, true) = p ^ 2 := by
  rw [changed_weight mass p first second, RootClockCalibration.trial_weight e he a moves]
  unfold RootTransferPhase.residual
  constructor <;> intro h <;> nlinarith

include he moves in
theorem independent_trial_weight (p : ℝ) :
    changedWeight (fun b => EventAccounting.binaryMass p b.1 *
      EventAccounting.binaryMass p b.2) = RootClockCalibration.trialWeight e a p := by
  rw [RootClockCalibration.trial_weight e he a moves]
  simp [changedWeight, EventAccounting.binaryMass, RootTransferPhase.residual]
  ring

include he moves in
theorem history_endpoint_weight (β cost : ℝ) (z : SubstrateReflection.Lattice)
    (hmoves : SubstrateReflection.reflect z ≠ z) :
    changedWeight (historyMass β cost z) = RootClockCalibration.trialWeight e a (gibbsRate β cost) := by
  have hmass := funext (history_mass_factorizes β cost z hmoves)
  rw [hmass]
  exact independent_trial_weight e he a moves (gibbsRate β cost)

/-- Normalization for one elapsed clock tick when the squared transfer
represents the two scheduled ticks. -/
def tickGenerator (p : ℝ) : Matrix n n ℂ :=
  (1 / 2 : ℂ) • generator e p

include he in
theorem heat_after_two_ticks (p : ℝ) (hp : p < 1 / 2) :
    NormedSpace.exp ((-2 : ℂ) • tickGenerator e p) = transfer e p * transfer e p := by
  rw [tickGenerator, smul_smul, show (-2 : ℂ) * (1 / 2) = -1 by norm_num, neg_one_smul]
  exact heat_matches e he p hp

theorem phase_in_ticks (p t : ℝ) :
    NormedSpace.exp ((-(t : ℂ) * Complex.I) • tickGenerator e p) = phase e p (t / 2) := by
  rw [tickGenerator, phase, smul_smul]
  push_cast
  congr 2
  ring

include he moves in
theorem exchange_in_ticks_iff (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) (N : ℕ) :
    phase e p ((N : ℝ) / 2) = e.permMatrix ℂ ↔
      ∃ k : ℤ, -Real.log (1 - 2 * RootClockCalibration.trialWeight e a p) *
        ((N : ℝ) / 2) = Real.pi + (k : ℝ) * (2 * Real.pi) := by
  rw [← half_pulse e he p hp hp', RootClockCalibration.phase_alias_iff e he a moves,
    ← RootClockCalibration.gap_from_trials e he a moves p hp']
  have hπ : gap p * (2 * quarterTime p) = Real.pi := by
    have h := RootPulseEvents.quarter_angle p hp hp'
    linarith
  rw [hπ]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by linarith⟩

include he moves in
theorem principal_weight_in_ticks (p : ℝ) (hp : p < 1 / 2) (N : ℕ) (hN : 0 < N)
    (principal : gap p * ((N : ℝ) / 2) = Real.pi) :
    RootClockCalibration.trialWeight e a p = (1 - Real.exp (-(2 * Real.pi) / N)) / 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hg : gap p = (2 * Real.pi) / N := (eq_div_iff hN').mpr (by linarith)
  rw [RootClockCalibration.trial_weight e he a moves, ← heat_scalar p hp, hg, neg_div]

end PMTransport.ClockedRootTrials
