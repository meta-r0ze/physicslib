import PMKAutomaton.RestoringRingToll

/-!
# Booked live extraction from the restoring ring

At the first two-visit live output a separate bank exchanges its prepared
reference with the live port. The exchange is reversible. For a successful
seed the receiver ports then carry only the reference, while the bank
retains the old payload. The rest of the clock block restores phase and
probe state. A second supplied bank can load a fresh seed.
-/

namespace PMKAutomaton.RestoringExtraction

open PMAction LocalController RingReceiver RestoringRingHistory
open scoped BigOperators

/-- Exchange a live slot and a bank, keeping all records and other live slots. -/
def exchangeLive {X V : Type*} [DecidableEq X] (site : X) :
    Equiv.Perm (OpenReferenceFlow.State X V × V) :=
  let swap : OpenReferenceFlow.State X V × V → OpenReferenceFlow.State X V × V :=
    fun s => (fun x => (if x = site then s.2 else (s.1 x).1, (s.1 x).2), (s.1 site).1)
  Function.Involutive.toPerm swap (by
    rintro ⟨ports, bank⟩
    apply Prod.ext
    · funext x
      by_cases hx : x = site <;> simp [swap, hx]
    · simp [swap])

/-- When the live value and prepared bank arrive on the two streams,
the native two-site exchange has the same local outputs as the bank swap. -/
theorem exchange_live_receiver {X V : Type*} [DecidableEq X] (site : X)
    (s : OpenReferenceFlow.State X V × V) (edge : TwoSiteHandoff.State V)
    (h : edge 1 = ((s.1 site).1, s.2)) :
    let extracted := exchangeLive site s
    ((extracted.1 site).1, extracted.2) = TwoSiteHandoff.step true edge 0 := by
  intro extracted
  rw [(TwoSiteHandoff.step_trace true edge).1, h]
  change ((if site = site then s.2 else (s.1 site).1), (s.1 site).1) = _
  simp

/-- The fixed receiver guard routes arbitrary values by the same stream and exchange stencil. -/
def valueStep {n : ℕ} {V : Type*} (either : Bool) (q : RequestsField n)
    (ports : OpenReferenceFlow.State (Fin n) V) : OpenReferenceFlow.State (Fin n) V :=
  fun x =>
    let p := OpenReferenceFlow.streamShift (finRotate n) ports x
    if exchange either (q x) then p.swap else p

/-- Interpret the absent marker as the prepared reference and the marker as a payload. -/
def liftPorts {n : ℕ} {V : Type*} (reference payload : V) (ports : PortField n) :
    OpenReferenceFlow.State (Fin n) V :=
  fun x => (if (ports x).1 then payload else reference, if (ports x).2 then payload else reference)

theorem value_step_lift {n : ℕ} {V : Type*} (either : Bool) (s : RingReceiver.State n)
    (reference payload : V) :
    valueStep either s.2.1 (liftPorts reference payload s.2.2.2) =
      liftPorts reference payload (tick n either s).2.2.2 := by
  funext x
  rw [liftPorts, tick_ports]
  cases h : exchange either (s.2.1 x) <;>
    simp [valueStep, liftPorts, arrivals, OpenReferenceFlow.streamShift, applyGuard, h]

theorem value_trace_lift {n : ℕ} {V : Type*} (either : Bool) (s : RingReceiver.State n)
    (reference payload : V) (k : ℕ) :
    (valueStep either s.2.1)^[k] (liftPorts reference payload s.2.2.2) =
      liftPorts reference payload (((tick n either)^[k] s).2.2.2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    have h := value_step_lift either (((tick n either)^[k] s)) reference payload
    rwa [requests_iterate] at h

private abbrev exitSite : Fin Delta := 42

/-- The typed bank receives the original payload, and the entire typed
receiver field carries the prepared reference after the booked exchange. -/
theorem extract_values {V : Type*} (either : Bool) (q : History)
    (hLive : liveExit either q = true) (reference payload : V) :
    exchangeLive exitSite
      ((valueStep either (seed q).2.1)^[2] (liftPorts reference payload (seed q).2.2.2), reference) =
        (fun _ => (reference, reference), payload) := by
  rw [value_trace_lift, successful_ports_even either q hLive 2 (by decide)]
  apply Prod.ext
  · funext x
    by_cases hx : x = exitSite <;>
      change ((if x = exitSite then reference else
        if decide (x = exitSite) then payload else reference), reference) = _
    all_goals simp [hx]
  · rfl

/-- Reload the reference-only field from a separately supplied typed
bank. The reload returns the prepared reference to that bank. -/
theorem reload_values {V : Type*} (q : History) (reference fresh : V) :
    exchangeLive exitSite ((fun _ => (reference, reference)), fresh) =
      (liftPorts reference fresh (seed q).2.2.2, reference) := by
  refine Prod.ext ?_ rfl
  funext x
  change ((if x = exitSite then fresh else reference), reference) =
    ((if decide (x = exitSite) then fresh else reference), reference)
  by_cases hx : x = exitSite <;> simp [hx]

private def replacePorts {n : ℕ} (s : RingReceiver.State n) (ports : PortField n) :
    RingReceiver.State n :=
  (s.1, (s.2.1, (s.2.2.1, ports)))

private theorem replace_ports_same {n : ℕ} (s : RingReceiver.State n) :
    replacePorts s s.2.2.2 = s := by
  rcases s with ⟨a, b, c, d⟩
  rfl

/-- Attach the bank swap to the ring state, retaining the requests, phase and probes. -/
def exchangeBank {n : ℕ} (site : Fin n) : Equiv.Perm (RingReceiver.State n × Bool) :=
  let swap : RingReceiver.State n × Bool → RingReceiver.State n × Bool :=
    fun s =>
      let x := exchangeLive site (s.1.2.2.2, s.2)
      (replacePorts s.1 x.1, x.2)
  Function.Involutive.toPerm swap (by
    rintro ⟨s, b⟩
    have h := (exchangeLive site).symm_apply_apply (s.2.2.2, b)
    change exchangeLive site (exchangeLive site (s.2.2.2, b)) = _ at h
    change (replacePorts s (exchangeLive site (exchangeLive site (s.2.2.2, b))).1,
      (exchangeLive site (exchangeLive site (s.2.2.2, b))).2) = _
    rw [h, replace_ports_same])

private def blankPorts {n : ℕ} : PortField n := fun _ => (false, false)

private theorem blank_tick {n : ℕ} (either : Bool) (s : RingReceiver.State n) :
    tick n either (replacePorts s blankPorts) = replacePorts (tick n either s) blankPorts := by
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  funext x
  rw [tick_ports]
  change applyGuard (fun _ => exchange either (s.2.1 x)) (false, false) = (false, false)
  simp [applyGuard]

private theorem blank_iterate {n : ℕ} (either : Bool) (s : RingReceiver.State n) (k : ℕ) :
    (tick n either)^[k] (replacePorts s blankPorts) =
      replacePorts ((tick n either)^[k] s) blankPorts := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, blank_tick]

/-- The reversible extraction is booked after the two receiver ticks. -/
def extract (either : Bool) (q : History) : RingReceiver.State Delta × Bool :=
  exchangeBank exitSite (((tick Delta either)^[2] (seed q)), false)

theorem extract_success (either : Bool) (q : History) (hLive : liveExit either q = true) :
    extract either q =
      (replacePorts (((tick Delta either)^[2] (seed q))) blankPorts, true) := by
  change (replacePorts (((tick Delta either)^[2] (seed q)))
    (exchangeLive exitSite ((((tick Delta either)^[2] (seed q))).2.2.2, false)).1,
      (exchangeLive exitSite ((((tick Delta either)^[2] (seed q))).2.2.2, false)).2) = _
  rw [successful_ports_even either q hLive 2 (by decide)]
  have hx : exchangeLive exitSite ((seed q).2.2.2, false) = (blankPorts, true) := by
    refine Prod.ext ?_ rfl
    funext x
    change ((if x = exitSite then false else decide (x = exitSite)), false) = (false, false)
    by_cases hx : x = exitSite <;> simp [hx]
  rw [hx]

theorem extract_miss (either : Bool) (q : History) (hLive : liveExit either q = false) :
    extract either q = (((tick Delta either)^[2] (seed q)), false) := by
  let s := (tick Delta either)^[2] (seed q)
  have h : (s.2.2.2 exitSite).1 = false := hLive
  apply Prod.ext
  · refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    funext x
    change ((if x = exitSite then false else (s.2.2.2 x).1), (s.2.2.2 x).2) = s.2.2.2 x
    by_cases hx : x = exitSite
    · subst x
      exact Prod.ext h.symm rfl
    · simp only [hx, ite_false]
  · exact h

/-- Finish the clock block after extracting. On success the bank keeps
the payload and the receiver has its original controls over clean ports. -/
theorem finish_after_extraction (either : Bool) (q : History) (hLive : liveExit either q = true) :
    ((tick Delta either)^[2 * Delta - 2] (extract either q).1, (extract either q).2) =
      (replacePorts (seed q) blankPorts, true) := by
  rw [extract_success either q hLive]
  refine Prod.ext ?_ rfl
  rw [blank_iterate]
  have h := (Function.iterate_add_apply (f := tick Delta either) (2 * Delta - 2) 2 (seed q)).symm
  rw [show 2 * Delta - 2 + 2 = 2 * Delta by decide, seed_returns] at h
  exact congrArg (fun s => replacePorts s blankPorts) h

/-- A fresh occupied bank reinstalls the original marker field at the
next phase-zero seed. The extracted output can be retained separately. -/
theorem reload_clean (q : History) :
    exchangeBank exitSite (replacePorts (seed q) blankPorts, true) = (seed q, false) := by
  apply Prod.ext
  · refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    funext x
    change ((if x = exitSite then true else false), false) = (decide (x = exitSite), false)
    by_cases hx : x = exitSite <;> simp [hx]
  · rfl

/-- An extracted output stays in its bank while a separately supplied
occupied bank reloads the receiver at the next phase-zero seed. -/
theorem restart_with_fresh_bank (either : Bool) (q : History) (hLive : liveExit either q = true) :
    let finished := ((tick Delta either)^[2 * Delta - 2] (extract either q).1, (extract either q).2)
    let restarted := exchangeBank exitSite (finished.1, true)
    (restarted.1, finished.2, restarted.2) = (seed q, true, false) := by
  intro finished restarted
  have hf : finished = (replacePorts (seed q) blankPorts, true) :=
    finish_after_extraction either q hLive
  have hr : restarted = (seed q, false) := by
    dsimp only [restarted]
    rw [hf]
    exact reload_clean q
  rw [hf, hr]

/-- Charge the comparisons performed by the ring tick, before and after
the bank exchange. The separate bank exchange and later carrier work
have their own admission and toll accounts. -/
noncomputable def extractedReceiverToll (either : Bool) (q : History) : ℝ :=
  receiverToll either q 2 +
    ∑ i ∈ Finset.range (2 * Delta - 2), ∑ x,
      receiverFlag either ((tick Delta either)^[i] (extract either q).1) x

theorem extracted_receiver_toll (either : Bool) (q : History) :
    extractedReceiverToll either q =
      if exchange either q.1 || exchange either q.2 then 2 else 0 := by
  cases h : liveExit either q with
  | false =>
    rw [extractedReceiverToll, extract_miss either q h]
    let cost (i : ℕ) := ∑ x, receiverFlag either ((tick Delta either)^[i] (seed q)) x
    have hadd : 2 + (2 * Delta - 2) = 2 * Delta := by decide
    have he := Finset.sum_range_add cost 2 (2 * Delta - 2)
    rw [hadd] at he
    have hsplit :
        receiverToll either q (2 * Delta) =
          receiverToll either q 2 + ∑ i ∈ Finset.range (2 * Delta - 2), ∑ x,
            receiverFlag either ((tick Delta either)^[i] ((tick Delta either)^[2] (seed q))) x := by
      change (∑ i ∈ Finset.range (2 * Delta), cost i) = (∑ i ∈ Finset.range 2, cost i) + _
      have htail : (∑ i ∈ Finset.range (2 * Delta - 2), cost (2 + i)) =
          ∑ i ∈ Finset.range (2 * Delta - 2), ∑ x,
            receiverFlag either ((tick Delta either)^[i] ((tick Delta either)^[2] (seed q))) x := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [cost]
        rw [Nat.add_comm 2, Function.iterate_add_apply]
      rw [he, htail]
    rw [← hsplit, full_receiver_toll, h]
    rfl
  | true =>
    have hex := h
    rw [live_exit, Bool.and_eq_true] at hex
    rw [extractedReceiverToll, successful_receiver_toll_two either q h,
      extract_success either q h, hex.1, hex.2]
    have hz : (∑ i ∈ Finset.range (2 * Delta - 2), ∑ x,
      receiverFlag either ((tick Delta either)^[i]
        (replacePorts ((tick Delta either)^[2] (seed q)) blankPorts)) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro x _
      rw [blank_iterate, receiver_flag_eq]
      change (if exchange either _ = true ∧ false ≠ false then (1 : ℝ) else 0) = 0
      simp
    rw [hz]
    norm_num

/-- If the extraction runs as an additional receiver comparison, the
orthogonal basis-marker account charges it only on a live exit. -/
theorem bank_comparison_flag (either : Bool) (q : History) :
    exchangeFlag (fun _ => true) (liveExit either q, false) basisValue =
      if liveExit either q then 1 else 0 := by
  cases liveExit either q <;>
    norm_num [exchangeFlag, basisValue, LinkExpansion.nsq_eq, Fin.sum_univ_two,
      Pi.single_apply, Complex.normSq_apply]

/-- For the ring comparison account with extraction, a successful
history has the survival penalty of two flags against an idle history. -/
theorem extracted_live_idle_odds (either : Bool) (prior : History → ℝ)
    (hprior : ∀ q, 0 < prior q) (β : ℝ) (live idle : History)
    (hlive : liveExit either live = true)
    (hentry : exchange either idle.1 = false) (hexit : exchange either idle.2 = false) :
    PersistenceMechanics.Selection.survivor prior β (extractedReceiverToll either) live /
      PersistenceMechanics.Selection.survivor prior β (extractedReceiverToll either) idle =
      prior live / prior idle * Real.exp (-β * 2) := by
  rw [live_exit, Bool.and_eq_true] at hlive
  rw [PersistenceMechanics.Selection.survivor_odds hprior,
    extracted_receiver_toll, extracted_receiver_toll, hlive.1, hlive.2, hentry, hexit]
  norm_num

end PMKAutomaton.RestoringExtraction
