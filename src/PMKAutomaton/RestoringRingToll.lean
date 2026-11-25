import PMKAutomaton.RestoringRingHistory
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Receiver Toll over a closed restoring cycle

The occupied receiver carries one marker. A tick contributes one mismatch
flag exactly when the switch it reaches exchanges. Following the marker
through the full 86-tick return accounts for every receiver comparison
on the ring, including later encounters after the first two visits.
-/

namespace PMKAutomaton.RestoringRingHistory

open PMAction LocalController RingReceiver
open scoped BigOperators

private def arrivalSite {n : ℕ} (p : Slot n) : Fin n :=
  if p.2 then (finRotate n).symm p.1 else finRotate n p.1

private def forwardSlot {n : ℕ} (firing : Fin n → Bool) (p : Slot n) : Slot n :=
  (arrivalSite p, p.2 != firing (arrivalSite p))

private theorem source_forward {n : ℕ} (firing : Fin n → Bool) (p : Slot n) :
    portSource firing (forwardSlot firing p) = p := by
  rcases p with ⟨x, side⟩
  cases side
  · cases h : firing (finRotate n x) <;>
      simp [portSource, forwardSlot, arrivalSite, h, -finRotate_apply, -finRotate_symm_apply]
  · cases h : firing ((finRotate n).symm x) <;>
      simp [portSource, forwardSlot, arrivalSite, h, -finRotate_apply, -finRotate_symm_apply]

private def singleMarker {n : ℕ} (p : Slot n) : PortField n :=
  fun x => (decide ((x, false) = p), decide ((x, true) = p))

private theorem single_slot {n : ℕ} (p r : Slot n) :
    slotValue (singleMarker p) r = decide (r = p) := by
  rcases r with ⟨x, side⟩
  cases side <;> rfl

private theorem step_single {n : ℕ} (either : Bool) (q : RequestsField n) (p : Slot n) :
    portStep either q (singleMarker p) = singleMarker (forwardSlot (exchange either ∘ q) p) := by
  have h (r : Slot n) : slotValue (portStep either q (singleMarker p)) r =
      slotValue (singleMarker (forwardSlot (exchange either ∘ q) p)) r := by
    rw [port_step_source, single_slot, single_slot]
    have hinj := (portSource_injective (exchange either ∘ q)).eq_iff
      (a := r) (b := forwardSlot (exchange either ∘ q) p)
    rw [source_forward] at hinj
    simp only [hinj]
  funext x
  exact Prod.ext (h (x, false)) (h (x, true))

private theorem single_arrival_mismatch {n : ℕ} (p : Slot n) (x : Fin n) :
    (arrivals (singleMarker p) x).1 ≠ (arrivals (singleMarker p) x).2 ↔
      x = arrivalSite p := by
  rcases p with ⟨i, side⟩
  cases side <;> simp [arrivals, OpenReferenceFlow.streamShift, singleMarker, arrivalSite,
    Prod.mk.injEq, Equiv.symm_apply_eq, -finRotate_apply,
    -finRotate_symm_apply]
  exact (finRotate n).eq_symm_apply.symm

private theorem tick_flags_single {n : ℕ} (either : Bool) (s : RingReceiver.State n)
    (p : Slot n) (hp : s.2.2.2 = singleMarker p) :
    (∑ x, receiverFlag either s x) = if exchange either (s.2.1 (arrivalSite p)) then 1 else 0 := by
  simp only [receiver_flag_eq, hp, single_arrival_mismatch]
  rw [Finset.sum_eq_single_of_mem (arrivalSite p) (Finset.mem_univ _)]
  · simp
  · intro x _ hx
    simp [hx]

/-- The full receiver comparison account for a fixed number of ticks. -/
noncomputable def receiverToll (either : Bool) (q : History) (ticks : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ticks, ∑ x, receiverFlag either ((tick Delta either)^[i] (seed q)) x

private def flagCount {n : ℕ} (firing : Fin n → Bool) : ℕ → Slot n → ℕ
  | 0, _ => 0
  | k + 1, p => (if firing (arrivalSite p) then 1 else 0) +
    flagCount firing k (forwardSlot firing p)

private theorem sum_flags {n : ℕ} (either : Bool) (k : ℕ)
    (s : RingReceiver.State n) (p : Slot n) (hp : s.2.2.2 = singleMarker p) :
    (∑ i ∈ Finset.range k, ∑ x, receiverFlag either ((tick n either)^[i] s) x) =
      (flagCount (exchange either ∘ s.2.1) k p : ℝ) := by
  induction k generalizing s p with
  | zero => simp [flagCount]
  | succ k ih =>
    rw [Finset.sum_range_succ', Function.iterate_zero_apply, tick_flags_single either s p hp]
    simp_rw [Function.iterate_succ_apply]
    have hports : (tick n either s).2.2.2 =
        singleMarker (forwardSlot (exchange either ∘ s.2.1) p) := by
      change portStep either s.2.1 s.2.2.2 = _
      rw [hp, step_single]
    rw [ih (tick n either s) _ hports]
    change (flagCount (exchange either ∘ s.2.1) k (forwardSlot (exchange either ∘ s.2.1) p) : ℝ) +
      (if exchange either (s.2.1 (arrivalSite p)) then 1 else 0) = _
    simp only [flagCount, Nat.cast_add, Function.comp_apply]
    split <;> simp [add_comm]

private def twoSwitches (entry exit : Bool) (x : Fin Delta) : Bool :=
  if x = 0 then entry else if x = 42 then exit else false

private theorem seed_firing (either : Bool) (q : History) :
    exchange either ∘ (seed q).2.1 = twoSwitches (exchange either q.1) (exchange either q.2) := by
  funext x
  change exchange either (if x = 0 then q.1 else if x = (42 : Fin Delta) then q.2
    else (false, false)) = _
  unfold twoSwitches
  split_ifs <;> cases either <;> rfl

private theorem seed_single (q : History) : (seed q).2.2.2 = singleMarker (42, false) := by
  funext x
  change (decide (x = (42 : Fin Delta)), false) = _
  simp [singleMarker, Prod.mk.injEq]

private theorem closed_count : ∀ entry exit : Bool,
    flagCount (twoSwitches entry exit) (2 * Delta) (42, false) =
      if entry && exit then 2 * Delta else if entry || exit then 2 else 0 := by
  decide +kernel

/-- The full return records 86 flags when both switches fire, two when
exactly one fires, and zero with both idle. -/
theorem full_receiver_toll (either : Bool) (q : History) :
    receiverToll either q (2 * Delta) =
      if liveExit either q then 86 else if exchange either q.1 || exchange either q.2 then 2 else 0 := by
  rw [receiverToll, sum_flags either _ (seed q) _ (seed_single q), seed_firing, closed_count, live_exit]
  split <;> simp

private theorem two_switch_slot_iterate (n : ℕ) :
    (portSource (twoSwitches true true))^[n] (42, false) =
      if n % 2 = 0 then (42, false) else (0, true) := by
  have hfirst : portSource (twoSwitches true true) (42, false) = (0, true) := by decide
  have hsecond : portSource (twoSwitches true true) (0, true) = (42, false) := by decide
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · simp [h, hfirst, show (n + 1) % 2 ≠ 0 by omega]
    · simp [h, hsecond, show (n + 1) % 2 = 0 by omega]

/-- While the successful marker stays in the closed receiver, its live
exit is occupied at even ticks. An odd tick carries it on the record side. -/
theorem successful_live_slot_even (either : Bool) (q : History) (h : liveExit either q = true)
    (n : ℕ) :
    slotValue (((tick Delta either)^[n] (seed q)).2.2.2) (42, false) =
      decide (n % 2 = 0) := by
  rw [live_exit, Bool.and_eq_true] at h
  rw [ports_iterate, port_iterate_source, seed_firing, h.1, h.2, two_switch_slot_iterate,
    seed_single, single_slot]
  split <;> simp_all

/-- At every even tick the successful marker's entire port field has
returned, so the live output can be exchanged without a second marker
remaining on the ring. -/
theorem successful_ports_even (either : Bool) (q : History) (h : liveExit either q = true)
    (n : ℕ) (hn : n % 2 = 0) :
    ((tick Delta either)^[n] (seed q)).2.2.2 = (seed q).2.2.2 := by
  rw [live_exit, Bool.and_eq_true] at h
  let route := portSource (twoSwitches true true)
  have hfix : route^[n] (42, false) = (42, false) := by
    dsimp only [route]
    simp only [two_switch_slot_iterate, hn, ite_true]
  have hslot (p : Slot Delta) :
      slotValue (((tick Delta either)^[n] (seed q)).2.2.2) p =
        slotValue (seed q).2.2.2 p := by
    rw [ports_iterate, port_iterate_source, seed_firing, h.1, h.2, seed_single,
      single_slot, single_slot]
    change decide (route^[n] p = (42, false)) = decide (p = (42, false))
    have hi : (route^[n] p = (42, false)) ↔ p = (42, false) := by
      nth_rw 1 [← hfix]
      exact ((portSource_injective _).iterate n).eq_iff
    simp only [hi]
  funext x
  exact Prod.ext (hslot (x, false)) (hslot (x, true))

/-- The first two ticks of a successful seed each contribute one
receiver flag when summed over the entire ring. -/
theorem successful_receiver_toll_two (either : Bool) (q : History)
    (h : liveExit either q = true) : receiverToll either q 2 = 2 := by
  rw [live_exit, Bool.and_eq_true] at h
  rw [receiverToll, sum_flags either _ (seed q) _ (seed_single q), seed_firing, h.1, h.2]
  rfl

/-- With a supplied positive history prior, charging the entire return
changes the odds of a successful history against an idle history by the
survival factor of 86 receiver flags. -/
theorem full_cycle_live_idle_odds (either : Bool) (prior : History → ℝ)
    (hprior : ∀ q, 0 < prior q) (β : ℝ) (live idle : History)
    (hlive : liveExit either live = true)
    (hentry : exchange either idle.1 = false) (hexit : exchange either idle.2 = false) :
    let action q := receiverToll either q (2 * Delta)
    PersistenceMechanics.Selection.survivor prior β action live /
      PersistenceMechanics.Selection.survivor prior β action idle =
      prior live / prior idle * Real.exp (-β * 86) := by
  intro action
  have hL : action live = 86 := by
    change receiverToll either live (2 * Delta) = 86
    rw [full_receiver_toll, hlive]
    rfl
  have hI : action idle = 0 := by
    change receiverToll either idle (2 * Delta) = 0
    rw [full_receiver_toll, live_exit, hentry, hexit]
    rfl
  rw [PersistenceMechanics.Selection.survivor_odds hprior, hL, hI, sub_zero]

open PersistenceMechanics.Gibbs

/-- The survivor's live-exit probability for a uniformly sampled seed
ensemble with a specified action. -/
noncomputable def exitShare {ι : Type*} [Fintype ι] (either : Bool)
    (historyOf : ι → History) (action : History → ℝ) (β : ℝ) : ℝ :=
  ∑ i, if liveExit either (historyOf i) then
    probability β (action ∘ historyOf) i else 0

private theorem exit_share_eq {ι : Type*} [Fintype ι] (either : Bool)
    (historyOf : ι → History) (action : History → ℝ) (β : ℝ) :
    exitShare either historyOf action β =
      (∑ i, if liveExit either (historyOf i) then weight β (action (historyOf i)) else 0) /
      partition β (action ∘ historyOf) := by
  rw [exitShare, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp [probability, *]

theorem exit_share_mem_Icc {ι : Type*} [Fintype ι] [Nonempty ι] (either : Bool)
    (historyOf : ι → History) (action : History → ℝ) (β : ℝ) :
    exitShare either historyOf action β ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    split
    · exact (probability_pos _ _ _).le
    · exact le_rfl
  · rw [← probabilities_sum_one β (action ∘ historyOf)]
    apply Finset.sum_le_sum
    intro i _
    split
    · exact le_rfl
    · exact (probability_pos _ _ _).le

/-- The action charges every receiver comparison in the full ring cycle. -/
noncomputable def cycleExitShare {ι : Type*} [Fintype ι] (either : Bool)
    (historyOf : ι → History) (β : ℝ) : ℝ :=
  exitShare either historyOf (fun q => receiverToll either q (2 * Delta)) β

/-- The action charges the two booked comparisons of the initial attempt. -/
noncomputable def visitToll (either : Bool) (q : History) : ℝ :=
  receiverFlag either (seed q) 0 +
    receiverFlag either (tick Delta either (seed q)) 42

/-- The 16 seed weights are grouped by their full-cycle flag counts. -/
theorem independent_cycle_share (either : Bool) (β : ℝ) :
    cycleExitShare either (id : History → History) β =
      (if either then 9 else 1) * weight β 86 /
        ((if either then 1 else 9) + 6 * weight β 2 + (if either then 9 else 1) * weight β 86) := by
  rw [cycleExitShare, exit_share_eq, partition]
  simp only [Function.comp_apply, id_eq, full_receiver_toll, live_exit, History, Requests,
    Fintype.sum_prod_type, Fintype.sum_bool]
  cases either <;> simp [exchange, weight] <;> ring

/-- The four shared-request seeds have only idle and full-swap actions. -/
theorem shared_cycle_share (either : Bool) (β : ℝ) :
    cycleExitShare either (fun q : Requests => (q, q)) β =
      (if either then 3 else 1) * weight β 86 /
        ((if either then 1 else 3) + (if either then 3 else 1) * weight β 86) := by
  rw [cycleExitShare, exit_share_eq, partition]
  simp only [Function.comp_apply, full_receiver_toll, live_exit, Requests, Fintype.sum_prod_type, Fintype.sum_bool]
  cases either <;> simp [exchange, weight] <;> ring

private theorem full_flag_weight_lt : weight 1 86 < (1 : ℝ) / 2 ^ 86 := by
  have h₂ : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  have hexp : Real.exp 86 = Real.exp 1 ^ 86 := by
    simp [← Real.exp_nat_mul]
  have hpower : (2 : ℝ) ^ 86 < Real.exp 86 := by
    rw [hexp]
    exact pow_lt_pow_left₀ h₂ (by norm_num) (by decide)
  rw [weight, neg_one_mul, Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt (by positivity) hpower

private theorem unitShare_bound {idle once full : ℝ}
    (hi : 1 ≤ idle) (ho : 0 ≤ once) (hf : 0 ≤ full) (h₉ : full ≤ 9) :
    full * weight 1 86 / (idle + once * weight 1 2 + full * weight 1 86) <
      (9 : ℝ) / 2 ^ 86 := by
  have h₂ := weight_pos 1 2
  have h₈₆ := weight_pos 1 86
  have hd : 1 ≤ idle + once * weight 1 2 + full * weight 1 86 := by
    linarith [mul_nonneg ho h₂.le, mul_nonneg hf h₈₆.le]
  have hle := div_le_self (mul_nonneg hf h₈₆.le) hd
  exact hle.trans_lt ((mul_le_mul_of_nonneg_right h₉ h₈₆.le).trans_lt
    (by simpa [div_eq_mul_inv] using
      mul_lt_mul_of_pos_left full_flag_weight_lt (by norm_num : (0 : ℝ) < 9)))

/-- At the unflagged unit scale, either uniform seed convention gives a
live-exit share below the steady two-leg weight when all receiver flags
in the 86-tick cycle are charged. -/
theorem unit_cycle_shares_lt_steady (either : Bool) :
    cycleExitShare either (id : History → History) 1 < PMSubstrate.causalCoupling / 2 ∧
      cycleExitShare either (fun q : Requests => (q, q)) 1 < PMSubstrate.causalCoupling / 2 := by
  have hα : (9 : ℝ) / 2 ^ 86 < PMSubstrate.causalCoupling / 2 := by
    have h := PMConstants.CertifiedConstants.alpha_bounds.1
    norm_num
    linarith
  rw [independent_cycle_share, shared_cycle_share]
  cases either
  · exact ⟨(unitShare_bound (idle := 9) (once := 6) (full := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hα,
      (by simpa using (unitShare_bound (idle := 3) (once := 0) (full := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hα)⟩
  · exact ⟨(unitShare_bound (idle := 1) (once := 6) (full := 9)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hα,
      (by simpa using (unitShare_bound (idle := 1) (once := 0) (full := 3)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hα)⟩

private theorem visit_toll_nonneg (either : Bool) (q : History) : 0 ≤ visitToll either q := by
  rw [visitToll, two_visit_flags]
  split <;> split <;> norm_num

private theorem visit_toll_live (either : Bool) (q : History) (h : liveExit either q = true) :
    visitToll either q = 2 := by
  have he := h
  rw [live_exit, Bool.and_eq_true] at he
  rw [visitToll, two_visit_flags, he.1, h]
  norm_num

private theorem visit_weight_gt : (1 : ℝ) / 9 < weight 1 2 := by
  have h : Real.exp 2 < 9 := by
    have hsq : Real.exp 2 = (Real.exp 1) ^ 2 := by simp [← Real.exp_nat_mul]
    rw [hsq]
    exact (pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by decide : 2 ≠ 0)).trans_le
      (by norm_num)
  rw [weight, neg_one_mul, Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt (Real.exp_pos _) h

/-- With at most 16 equally weighted seeds and at least one live exit,
billing the two visits gives a strictly positive floor above the steady
two-leg weight at the unit scale. -/
theorem steady_lt_visit_share {ι : Type*} [Fintype ι] (either : Bool) (historyOf : ι → History)
    (hsize : Fintype.card ι ≤ 16) (hlive : ∃ i, liveExit either (historyOf i) = true) :
    PMSubstrate.causalCoupling / 2 < exitShare either historyOf (visitToll either) 1 := by
  obtain ⟨i, hi⟩ := hlive
  have : Nonempty ι := ⟨i⟩
  let S := visitToll either ∘ historyOf
  let numerator := ∑ j, if liveExit either (historyOf j) then weight 1 (S j) else 0
  have hnum : weight 1 2 ≤ numerator := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset ι))
      (f := fun j => if liveExit either (historyOf j) then weight 1 (S j) else 0)
      (fun j _ => by split; exact (weight_pos _ _).le; exact le_rfl) (Finset.mem_univ i)
    simpa [S, numerator, hi, visit_toll_live either (historyOf i) hi] using h
  have hd : partition 1 S ≤ 16 := by
    calc
      partition 1 S ≤ ∑ _ : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have h := (weight_order (by norm_num : (0 : ℝ) < 1)).2
          (visit_toll_nonneg either (historyOf j))
        simpa [weight, S] using h
      _ ≤ 16 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact_mod_cast hsize
  have hα := PMConstants.CertifiedConstants.alpha_bounds.2
  rw [exit_share_eq]
  change PMSubstrate.causalCoupling / 2 < numerator / partition 1 S
  apply (lt_div_iff₀ (partition_pos _ _)).2
  have hα₀ := PMSubstrate.causalCoupling_bounds.1
  have hm := mul_le_mul_of_nonneg_left hd (div_nonneg hα₀.le (by norm_num : (0 : ℝ) ≤ 2))
  linarith [visit_weight_gt]

/-- Both uniform seed conventions cross to the other side of the steady
coefficient when only the two visits are paid. -/
theorem steady_lt_unit_visit_shares (either : Bool) :
    PMSubstrate.causalCoupling / 2 < exitShare either (id : History → History) (visitToll either) 1 ∧
      PMSubstrate.causalCoupling / 2 <
        exitShare either (fun q : Requests => (q, q)) (visitToll either) 1 := by
  constructor
  · apply steady_lt_visit_share
    · norm_num [History, Requests, Fintype.card_prod]
    · refine ⟨((true, true), (true, true)), ?_⟩
      rw [live_exit]
      cases either <;> rfl
  · apply steady_lt_visit_share
    · norm_num [Requests, Fintype.card_prod]
    · refine ⟨(true, true), ?_⟩
      rw [live_exit]
      cases either <;> rfl

end PMKAutomaton.RestoringRingHistory
