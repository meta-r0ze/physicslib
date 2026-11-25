import PMKAutomaton.RingReceiver
import PMConstants.CertifiedConstants

/-!
# Recurring restoring histories on the closed clock ring

The initial field contains a single live marker immediately before the entry
at site 0. The exit is the upstream neighbour, on the record stream's path.
Only these two sites carry requests. The ring is closed, so its recurrence
checks the marker, requests, phase and probes without an external reset.
-/

namespace PMKAutomaton.RestoringRingHistory

open PMAction LocalController RingReceiver

/-- The retained request pair at entry and the retained request pair at exit. -/
abbrev History := Requests × Requests

private abbrev exitSite : Fin Delta := 42

private def marker : PortField Delta := fun x => (decide (x = exitSite), false)

private def requests (q : History) : RequestsField Delta :=
  fun x => if x = 0 then q.1 else if x = exitSite then q.2 else (false, false)

/-- The phase-zero seed has resting probe sides and the isolated live marker. -/
def seed (q : History) : RingReceiver.State Delta :=
  (0, (requests q, (fun _ => false, marker)))

private def switches (entry exit : Bool) (x : Fin Delta) : Bool :=
  if x = 0 then entry else if x = exitSite then exit else false

private theorem exchange_requests (either : Bool) (q : History) :
    exchange either ∘ requests q = switches (exchange either q.1) (exchange either q.2) := by
  funext x
  simp only [Function.comp_apply, requests, switches]
  split_ifs <;> cases either <;> rfl

private theorem marker_slot (p : Slot Delta) :
    slotValue marker p = decide (p = (exitSite, false)) := by
  rcases p with ⟨x, side⟩
  cases side <;> simp [slotValue, marker, Prod.mk.injEq]

private theorem marker_return_source :
    ∀ entry exit : Bool,
      (portSource (switches entry exit))^[2 * Delta] (exitSite, false) =
        (exitSite, false) := by
  decide +kernel

private theorem marker_return_slots (entry exit : Bool) (p : Slot Delta) :
    slotValue marker ((portSource (switches entry exit))^[2 * Delta] p) =
      slotValue marker p := by
  have hinj := (portSource_injective (switches entry exit)).iterate (2 * Delta)
  simp only [marker_slot]
  have h : ((portSource (switches entry exit))^[2 * Delta] p = (exitSite, false)) ↔
      p = (exitSite, false) := by
    nth_rw 1 [← marker_return_source entry exit]
    exact hinj.eq_iff
  simp only [h]

private theorem marker_one_period_slot :
    ∀ entry exit : Bool,
      slotValue marker ((portSource (switches entry exit))^[Delta] (exitSite, false)) =
        !(entry || exit) := by
  decide +kernel

private theorem marker_exit_slot :
    ∀ entry exit : Bool,
      slotValue marker ((portSource (switches entry exit))^[2] (exitSite, false)) =
        (entry && exit) := by
  decide +kernel

private theorem seed_slot (either : Bool) (q : History) (p : Slot Delta) (n : ℕ) :
    slotValue (((tick Delta either)^[n] (seed q)).2.2.2) p =
      slotValue marker ((portSource (switches (exchange either q.1) (exchange either q.2)))^[n] p) := by
  rw [ports_iterate, port_iterate_source]
  change slotValue marker ((portSource (exchange either ∘ requests q))^[n] p) = _
  rw [exchange_requests]

/-- Every request pair on this spatial support recurs after two clock
periods under either native reversible receiver. -/
theorem seed_returns (either : Bool) (q : History) :
    (tick Delta either)^[2 * Delta] (seed q) = seed q := by
  apply ring_return_of_ports either (seed q) rfl _ dvd_rfl
  have h (p : Slot Delta) :
      slotValue ((portStep either (requests q))^[2 * Delta] marker) p =
        slotValue marker p := by
    rw [port_iterate_source, exchange_requests, marker_return_slots]
  funext x
  exact Prod.ext (h (x, false)) (h (x, true))

/-- Restoring the marker to the live exit needs the joint guard event. -/
def liveExit (either : Bool) (q : History) : Bool :=
  slotValue (((tick Delta either)^[2] (seed q)).2.2.2) (exitSite, false)

theorem live_exit (either : Bool) (q : History) :
    liveExit either q = (exchange either q.1 && exchange either q.2) :=
  (seed_slot either q _ 2).trans (marker_exit_slot _ _)

/-- A seed that executes the restoration cannot close after one clock period. -/
theorem live_exit_ne_one_period (either : Bool) (q : History) (h : liveExit either q = true) :
    (tick Delta either)^[Delta] (seed q) ≠ seed q := by
  rw [live_exit, Bool.and_eq_true] at h
  intro hreturn
  have hslot := (seed_slot either q (exitSite, false) Delta).trans (marker_one_period_slot _ _)
  rw [hreturn, h.1, h.2] at hslot
  exact Bool.false_ne_true hslot.symm

/-- A restoring seed has exact period 86. The common phase rules out
the shorter divisors 1 and 2, and the live marker rules out 43. -/
theorem restoring_minimal_period (either : Bool) (q : History)
    (h : liveExit either q = true) :
    Function.minimalPeriod (tick Delta either) (seed q) = 2 * Delta := by
  let m := Function.minimalPeriod (tick Delta either) (seed q)
  have hr : Function.IsPeriodicPt (tick Delta either) (2 * Delta) (seed q) := seed_returns either q
  have hmDvd : m ∣ 86 := hr.minimalPeriod_dvd
  have hmLe : m ≤ 86 := Nat.le_of_dvd (by decide) hmDvd
  have hm : Function.IsPeriodicPt (tick Delta either) m (seed q) :=
    Function.isPeriodicPt_minimalPeriod _ _
  have hphase : ((finRotate Delta)^[m]) (0 : Phase) = 0 :=
    (phase_iterate either (seed q) m).symm.trans (congrArg Prod.fst hm.eq)
  have hcases : ∀ k : Fin 87, k.val ∣ 86 →
      k.val = 1 ∨ k.val = 2 ∨ k.val = 43 ∨ k.val = 86 := by decide +kernel
  change m = 86
  have hs : m = 1 ∨ m = 2 ∨ m = 43 ∨ m = 86 := hcases ⟨m, by omega⟩ hmDvd
  rcases hs with h₁ | h₂ | h₄₃ | h₈₆
  · rw [h₁] at hphase
    exact False.elim ((by decide : (finRotate Delta)^[1] (0 : Phase) ≠ 0) hphase)
  · rw [h₂] at hphase
    exact False.elim ((by decide : (finRotate Delta)^[2] (0 : Phase) ≠ 0) hphase)
  · rw [h₄₃] at hm
    exact False.elim (live_exit_ne_one_period either q h hm.eq)
  · exact h₈₆

private theorem exit_arrivals (either : Bool) (q : History) :
    arrivals (tick Delta either (seed q)).2.2.2 exitSite = (false, exchange either q.1) := by
  change ((tick Delta either (seed q)).2.2.2 41 |>.1,
    (tick Delta either (seed q)).2.2.2 0 |>.2) = _
  rw [tick_ports, tick_ports]
  change ((applyGuard (fun _ => exchange either (requests q 41)) (false, false)).1,
    (applyGuard (fun _ => exchange either q.1) (true, false)).2) = _
  cases exchange either q.1 <;> simp [applyGuard]

/-- A successful restoration receives the marker on the live stream at
entry and on the record stream at exit. -/
theorem successful_arrivals (either : Bool) (q : History) (h : liveExit either q = true) :
    arrivals (seed q).2.2.2 0 = (true, false) ∧
      arrivals (tick Delta either (seed q)).2.2.2 (42 : Fin Delta) = (false, true) := by
  rw [live_exit, Bool.and_eq_true] at h
  exact ⟨rfl, (exit_arrivals either q).trans (congrArg (fun b => (false, b)) h.1)⟩

/-- The comparison flags on the entry visit and its downstream exit visit.
A successful return records two mismatches. An exit with no marker
contributes zero even if the exit controller calls for a swap. -/
theorem two_visit_flags (either : Bool) (q : History) :
    receiverFlag either (seed q) 0 +
      receiverFlag either (tick Delta either (seed q)) exitSite =
        (if exchange either q.1 then 1 else 0) + (if liveExit either q then 1 else 0) := by
  rw [receiver_flag_eq, receiver_flag_eq, exit_arrivals, live_exit]
  have hreq : (tick Delta either (seed q)).2.1 exitSite = q.2 := rfl
  rw [hreq]
  change (if exchange either q.1 = true ∧ true ≠ false then (1 : ℝ) else 0) +
    (if exchange either q.2 = true ∧ false ≠ exchange either q.1 then 1 else 0) = _
  cases exchange either q.1 <;> cases exchange either q.2 <;> simp

open scoped BigOperators

/-- Whatever the correlation of the two requests, their marginal swap
probabilities give a lower bound on the live-exit weight. This applies to
any normalized weights on the certified recurring history family. -/
theorem weighted_exit_ge (either : Bool) (mass : History → ℝ)
    (hnonneg : ∀ q, 0 ≤ mass q) (hnorm : ∑ q, mass q = 1) :
    (∑ q, if exchange either q.1 then mass q else 0) +
      (∑ q, if exchange either q.2 then mass q else 0) - 1 ≤
      ∑ q, if liveExit either q then mass q else 0 := by
  rw [← hnorm, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro q _
  rw [live_exit]
  cases exchange either q.1 <;> cases exchange either q.2 <;> simp [hnonneg q]

/-- Under OR, retaining swap marginals of at least three quarters at both
sites forces at least half the prior weight to leave live. Correlating the
requests cannot recover the steady two-leg weight with these marginals. -/
theorem or_exit_weight_ge_half (mass : History → ℝ)
    (hnonneg : ∀ q, 0 ≤ mass q) (hnorm : ∑ q, mass q = 1)
    (hentry : (3 / 4 : ℝ) ≤ ∑ q, if exchange true q.1 then mass q else 0)
    (hexit : (3 / 4 : ℝ) ≤ ∑ q, if exchange true q.2 then mass q else 0) :
    (1 / 2 : ℝ) ≤ ∑ q, if liveExit true q then mass q else 0 := by
  linarith [weighted_exit_ge true mass hnonneg hnorm]

open PMSubstrate.NetCost

/-- Uniform weight on the 16 ordered entry/exit request pairs. Each case
recurs, so this sampling convention counts phase-zero seeds once. -/
noncomputable def uniformExitWeight (either : Bool) : ℝ :=
  prob (Finset.univ.filter fun q : History => liveExit either q = true)

/-- Uniform weight on the four seeds with a shared entry/exit request. -/
noncomputable def sharedExitWeight (either : Bool) : ℝ :=
  prob (Finset.univ.filter fun q : Requests => liveExit either (q, q) = true)

theorem uniform_exit_weights :
    uniformExitWeight false = 1 / 16 ∧ uniformExitWeight true = 9 / 16 := by
  simp only [uniformExitWeight, live_exit, prob]
  have h₁ : (Finset.univ.filter fun q : History =>
      (exchange false q.1 && exchange false q.2) = true).card = 1 := by decide +kernel
  have h₂ : (Finset.univ.filter fun q : History =>
      (exchange true q.1 && exchange true q.2) = true).card = 9 := by decide +kernel
  rw [h₁, h₂]
  norm_num [History, Requests, Fintype.card_prod]

theorem shared_exit_weights :
    sharedExitWeight false = 1 / 4 ∧ sharedExitWeight true = 3 / 4 := by
  simp only [sharedExitWeight, live_exit, prob]
  have h₁ : (Finset.univ.filter fun q : Requests =>
      (exchange false q && exchange false q) = true).card = 1 := by decide +kernel
  have h₂ : (Finset.univ.filter fun q : Requests =>
      (exchange true q && exchange true q) = true).card = 3 := by decide +kernel
  rw [h₁, h₂]
  norm_num [Requests, Fintype.card_prod]

/-- Both uniform sampling conventions give larger transfer weights than
the steady two-leg coefficient, for either controller. -/
theorem steady_lt_recurring_weights (either : Bool) :
    PMSubstrate.causalCoupling / 2 < uniformExitWeight either ∧
      PMSubstrate.causalCoupling / 2 < sharedExitWeight either := by
  have hα := PMConstants.CertifiedConstants.alpha_bounds.2
  cases either
  · rw [uniform_exit_weights.1, shared_exit_weights.1]
    constructor <;> linarith
  · rw [uniform_exit_weights.2, shared_exit_weights.2]
    constructor <;> linarith

end PMKAutomaton.RestoringRingHistory
