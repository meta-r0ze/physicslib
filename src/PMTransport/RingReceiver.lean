import PMTransport.LocalController
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Closed two-stream receiver

A periodic identification closes the encoded root line. It supplies a
finite state space with internal arrivals. The retained requests still
belong to that state. The test keeps every initial request and port field.
-/

namespace PMTransport.RingReceiver

open PMAction LocalController
open scoped BigOperators

abbrev RequestsField (n : ℕ) := Fin n → Requests
abbrev ProbeField (n : ℕ) := Fin n → Bool
abbrev PortField (n : ℕ) := OpenReferenceFlow.State (Fin n) Bool
abbrev Fields (n : ℕ) := RequestsField n × (ProbeField n × PortField n)
abbrev State (n : ℕ) := Phase × Fields n

/-- False selects AND and true selects OR. -/
def exchange (either : Bool) (c : Requests) : Bool :=
  if either then c.1 || c.2 else c.1 && c.2

def arrivals {n : ℕ} (ports : PortField n) :=
  OpenReferenceFlow.streamShift (finRotate n) ports

private def scatter {n : ℕ} (either : Bool) (requests : RequestsField n)
    (ports : PortField n) : PortField n :=
  fun x => applyGuard (fun _ => exchange either (requests x)) (ports x)

private theorem scatter_twice {n : ℕ} (either : Bool) (requests : RequestsField n) :
    Function.Involutive (scatter either requests) := by
  intro ports
  funext x
  rcases hp : ports x with ⟨live, record⟩
  cases hx : exchange either (requests x) <;> simp [scatter, applyGuard, hx, hp]

def portStep {n : ℕ} (either : Bool) (requests : RequestsField n) : Equiv.Perm (PortField n) :=
  (OpenReferenceFlow.shiftEquiv (finRotate n)).trans ((scatter_twice either requests).toPerm _)

private def probeStep {n : ℕ} (phase : Phase) (requests : RequestsField n)
    (side : ProbeField n) : ProbeField n :=
  fun x => (advanceProbe phase (requests x, side x)).2

private theorem probe_twice {n : ℕ} (phase : Phase) (requests : RequestsField n) :
    Function.Involutive (probeStep phase requests) := by
  intro side
  funext x
  cases h : ClockedRootTrials.fire (requests x) phase <;> simp [probeStep, advanceProbe, h]

/-- Undo the phase advance, then both on-site involutions, then the
    stream shift. The resulting tick is a bijection for either rule. -/
def tick (n : ℕ) (either : Bool) : Equiv.Perm (State n) :=
  (Equiv.prodCongrRight fun phase =>
    Equiv.prodCongrRight fun requests =>
      Equiv.prodCongr ((probe_twice phase requests).toPerm _) (portStep either requests)).trans
    (Equiv.prodCongr (finRotate Delta) (Equiv.refl _))

theorem tick_bijective (n : ℕ) (either : Bool) : Function.Bijective (tick n either) :=
  (tick n either).bijective

theorem tick_ports {n : ℕ} (either : Bool) (s : State n) (x : Fin n) :
    (tick n either s).2.2.2 x =
      applyGuard (fun _ => exchange either (s.2.1 x)) (arrivals s.2.2.2 x) := rfl

theorem receiver_realisation {n : ℕ} (either : Bool) (s : State n) (x : Fin n)
    (edge : TwoSiteHandoff.State Bool) (h : edge 1 = arrivals s.2.2.2 x) :
    (tick n either s).2.2.2 x = TwoSiteHandoff.step (exchange either (s.2.1 x)) edge 0 := by
  rw [tick_ports, (TwoSiteHandoff.step_trace _ edge).1, ← h]
  rfl

theorem probe_realisation {n : ℕ} (either : Bool) (s : State n) (x : Fin n)
    (z : SubstrateReflection.Lattice) :
    ClockedRootTrials.tick (s.2.1 x, (orbitPoint z (s.2.2.1 x), s.1)) =
      ((tick n either s).2.1 x, (orbitPoint z ((tick n either s).2.2.1 x), (tick n either s).1)) :=
  LocalController.probe_realises_trial s.1 (s.2.1 x, s.2.2.1 x) z

/-- Two sites identify the incoming neighbours. Three and four sites
    both retain the centre and its two distinct neighbours. -/
theorem ring_neighbourhood :
    (∀ x : Fin 2, finRotate 2 x = (finRotate 2).symm x) ∧
    (∀ x : Fin 3, finRotate 3 x ≠ x ∧ (finRotate 3).symm x ≠ x ∧
      finRotate 3 x ≠ (finRotate 3).symm x) ∧
    (∀ x : Fin 4, finRotate 4 x ≠ x ∧ (finRotate 4).symm x ≠ x ∧
      finRotate 4 x ≠ (finRotate 4).symm x) := by
  decide +kernel

/-! ## Exact cyclic traffic -/

abbrev Slot (n : ℕ) := Fin n × Bool

/-- Source of an output slot. False is live and true is record. -/
def portSource {n : ℕ} (switches : Fin n → Bool) (p : Slot n) : Slot n :=
  let record := p.2 != switches p.1
  if record then (finRotate n p.1, true) else ((finRotate n).symm p.1, false)

def slotValue {n : ℕ} (ports : PortField n) (p : Slot n) : Bool :=
  if p.2 then (ports p.1).2 else (ports p.1).1

theorem port_step_source {n : ℕ} (either : Bool) (q : RequestsField n)
    (ports : PortField n) (p : Slot n) :
    slotValue (portStep either q ports) p =
      slotValue ports (portSource (exchange either ∘ q) p) := by
  rcases p with ⟨x, bit⟩
  change (if bit then (scatter either q (arrivals ports) x).2
    else (scatter either q (arrivals ports) x).1) = _
  cases bit <;> cases hx : exchange either (q x) <;>
    simp [scatter, applyGuard, arrivals, OpenReferenceFlow.streamShift, portSource,
      slotValue, hx]

private theorem port_iterate_source {n : ℕ} (either : Bool) (q : RequestsField n)
    (ports : PortField n) (p : Slot n) (k : ℕ) :
    slotValue ((portStep either q)^[k] ports) p =
      slotValue ports ((portSource (exchange either ∘ q))^[k] p) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', port_step_source, ih, Function.iterate_succ_apply]

/-- Certify the common port periods on all exchange patterns, rather than
    iterate the clocked state space with its duplicate phase and probe data. -/
theorem slot_period_three :
    ∀ q : Fin 3 → Bool, ∀ p : Slot 3, (portSource q)^[12] p = p := by
  decide +kernel

theorem slot_period_four :
    ∀ q : Fin 4 → Bool, ∀ p : Slot 4, (portSource q)^[24] p = p := by
  decide +kernel

private def probeClock (u : Phase × (Requests × Bool)) : Phase × (Requests × Bool) :=
  (finRotate Delta u.1, advanceProbe u.1 u.2)

private theorem probe_return :
    ∀ c : Requests, ∀ b : Bool, (probeClock^[2 * Delta]) (0, (c, b)) = (0, (c, b)) := by
  decide +kernel

/-- One phase-zero block flips the probe side exactly for mixed requests. -/
theorem probe_one_period :
    ∀ c : Requests, ∀ b : Bool, (probeClock^[Delta]) (0, (c, b)) =
      (0, (c, if c.1 = c.2 then b else !b)) := by
  decide +kernel

theorem phase_iterate {n : ℕ} (either : Bool) (s : State n) (k : ℕ) :
    ((tick n either)^[k] s).1 = (finRotate Delta)^[k] s.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact congrArg (finRotate Delta) ih

theorem requests_iterate {n : ℕ} (either : Bool) (s : State n) (k : ℕ) :
    ((tick n either)^[k] s).2.1 = s.2.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih

theorem ports_iterate {n : ℕ} (either : Bool) (s : State n) (k : ℕ) :
    ((tick n either)^[k] s).2.2.2 = (portStep either s.2.1)^[k] s.2.2.2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change portStep either ((tick n either)^[k] s).2.1
      ((tick n either)^[k] s).2.2.2 = _
    rw [requests_iterate, ih]

private theorem probe_iterate {n : ℕ} (either : Bool) (s : State n) (x : Fin n) (k : ℕ) :
    (((tick n either)^[k] s).1, (((tick n either)^[k] s).2.1 x,
      ((tick n either)^[k] s).2.2.1 x)) =
      (probeClock^[k]) (s.1, (s.2.1 x, s.2.2.1 x)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

/-- Combine any common slot period with the two-clock probe period. -/
theorem ring_return {n k t : ℕ} (either : Bool) (s : State n) (hs : s.1 = 0)
    (hslot : ∀ p : Slot n, (portSource (exchange either ∘ s.2.1))^[k] p = p)
    (hk : k ∣ t) (hc : 2 * Delta ∣ t) : (tick n either)^[t] s = s := by
  let u := (tick n either)^[t] s
  have hphase : Function.IsPeriodicPt (finRotate Delta) Delta s.1 :=
    CarrierReferenceCycle.clock_closes s.1
  have hphase' := (hphase.trans_dvd (dvd_trans (dvd_mul_left Delta 2) hc)).eq
  have hprobe (x : Fin n) :
      Function.IsPeriodicPt probeClock (2 * Delta) (s.1, (s.2.1 x, s.2.2.1 x)) := by
    rw [hs]
    exact probe_return (s.2.1 x) (s.2.2.1 x)
  have hprobes (x : Fin n) : (u.1, (u.2.1 x, u.2.2.1 x)) =
      (s.1, (s.2.1 x, s.2.2.1 x)) :=
    (probe_iterate either s x t).trans ((hprobe x).trans_dvd hc).eq
  have hp (p : Slot n) : slotValue u.2.2.2 p = slotValue s.2.2.2 p := by
    have h : Function.IsPeriodicPt (portSource (exchange either ∘ s.2.1)) k p := hslot p
    change slotValue ((tick n either)^[t] s).2.2.2 p = _
    rw [ports_iterate, port_iterate_source, (h.trans_dvd hk).eq]
  change u = s
  refine Prod.ext ((phase_iterate either s t).trans hphase') (Prod.ext (requests_iterate either s t) ?_)
  apply Prod.ext
  · funext x
    exact congrArg (fun p : Phase × (Requests × Bool) => p.2.2) (hprobes x)
  · funext x
    exact Prod.ext (hp (x, false)) (hp (x, true))

theorem ring_return_three (either : Bool) (s : State 3) (hs : s.1 = 0) :
    (tick 3 either)^[516] s = s :=
  ring_return either s hs (slot_period_three _) (by decide +kernel) (by decide +kernel)

theorem ring_return_four (either : Bool) (s : State 4) (hs : s.1 = 0) :
    (tick 4 either)^[1032] s = s :=
  ring_return either s hs (slot_period_four _) (by decide +kernel) (by decide +kernel)

/-- Starting the enumeration at phase zero loses no orbit. -/
theorem phase_zero_seed {n : ℕ} (either : Bool) (s : State n) :
    ∃ fields : Fields n, (tick n either)^[s.1.val] (0, fields) = s := by
  obtain ⟨u, hu⟩ := ((tick n either).surjective.iterate s.1.val) s
  have hp : (finRotate Delta)^[s.1.val] u.1 = s.1 := by
    rw [← phase_iterate either u s.1.val, hu]
  have h0 := ((finRotate Delta).injective.iterate s.1.val)
    (hp.trans (CarrierReferenceCycle.clock_visits s.1).symm)
  exact ⟨u.2, (congrArg (fun y : Phase => (tick n either)^[s.1.val] (y, u.2))
    h0.symm).trans hu⟩

local instance (n : ℕ) : DecidableEq (RequestsField n) :=
  Fintype.decidablePiFintype (β := fun _ : Fin n => Requests)

local instance (n : ℕ) : DecidableEq (ProbeField n) :=
  Fintype.decidablePiFintype (β := fun _ : Fin n => Bool)

local instance (n : ℕ) : DecidableEq (PortField n) :=
  Fintype.decidablePiFintype (β := fun _ : Fin n => Ports)

def orbitWithin {n : ℕ} (either : Bool) (bound : ℕ) (s : State n) : Finset (State n) :=
  (Finset.range bound).image fun k => (tick n either)^[k] s

theorem mem_orbitWithin_iff {n bound : ℕ} (either : Bool) (s t : State n)
    (hb : 0 < bound) (h : Function.IsPeriodicPt (tick n either) bound s) :
    t ∈ orbitWithin either bound s ↔ ∃ k : ℕ, (tick n either)^[k] s = t := by
  simp only [orbitWithin, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, _, hkt⟩
    exact ⟨k, hkt⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k % bound, Nat.mod_lt _ hb, h.iterate_mod_apply _⟩

/-- Distinct orbit sets, with equal sets counted once. -/
def enumerateOrbits (n : ℕ) (either : Bool) (bound : ℕ) : Finset (Finset (State n)) :=
  (Finset.univ : Finset (Fields n)).image fun fields => orbitWithin either bound (0, fields)

theorem orbit_enumeration_covers {n bound : ℕ} (either : Bool) (hb : 0 < bound)
    (h : ∀ fields : Fields n, Function.IsPeriodicPt (tick n either) bound (0, fields))
    (s : State n) : ∃ orbit ∈ enumerateOrbits n either bound, s ∈ orbit := by
  obtain ⟨fields, hf⟩ := phase_zero_seed either s
  refine ⟨orbitWithin either bound (0, fields), ?_,
    (mem_orbitWithin_iff either _ _ hb (h fields)).mpr ⟨s.1.val, hf⟩⟩
  unfold enumerateOrbits
  exact Finset.mem_image.mpr ⟨fields, Finset.mem_univ _, rfl⟩

/-- The stationary average gives equal weight to each distinct state of
    a single orbit. The caller supplies any map from values to populations. -/
noncomputable def orbitAverage {n : ℕ} (orbit : Finset (State n)) (f : State n → ℝ) : ℝ :=
  (∑ s ∈ orbit, f s) / orbit.card

noncomputable def arrivalFrequency {n : ℕ} (orbit : Finset (State n)) (x : Fin n)
    (pair : Ports) : ℝ :=
  orbitAverage orbit fun s => if arrivals s.2.2.2 x = pair then 1 else 0

noncomputable def requestFrequency {n : ℕ} (orbit : Finset (State n)) (x : Fin n)
    (q : Requests) : ℝ :=
  orbitAverage orbit fun s => if s.2.1 x = q then 1 else 0

noncomputable def portPopulation {n : ℕ} (orbit : Finset (State n)) (p : Slot n)
    (population : Bool → ℝ) : ℝ :=
  orbitAverage orbit fun s => population (slotValue s.2.2.2 p)


/-! ## Pricing and selection -/

noncomputable def basisValue (b : Bool) : Fin 2 → ℂ :=
  Pi.single (if b then 1 else 0) 1

noncomputable def receiverFlag {n : ℕ} (either : Bool) (s : State n) (x : Fin n) : ℝ :=
  exchangeFlag (fun _ => exchange either (s.2.1 x)) (arrivals s.2.2.2 x) basisValue

/-- The certified exchange comparator, on two orthogonal unit values. -/
theorem receiver_flag_eq {n : ℕ} (either : Bool) (s : State n) (x : Fin n) :
    receiverFlag either s x =
      if exchange either (s.2.1 x) = true ∧
        (arrivals s.2.2.2 x).1 ≠ (arrivals s.2.2.2 x).2 then 1 else 0 := by
  unfold receiverFlag
  generalize arrivals s.2.2.2 x = p
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> cases h : exchange either (s.2.1 x) <;>
    norm_num [exchangeFlag, h, basisValue, LinkExpansion.nsq_eq, Fin.sum_univ_two,
      Pi.single_apply, Complex.normSq_apply]

/-- Expected receiver registrations per tick on an orbit. The sum may
    cover one receiver or all of them. -/
noncomputable def orbitToll {n : ℕ} (either : Bool) (receivers : Finset (Fin n))
    (orbit : Finset (State n)) : ℝ :=
  orbitAverage orbit fun s => ∑ x ∈ receivers, receiverFlag either s x

private theorem orbit_toll_nonneg {n : ℕ} (either : Bool) (receivers : Finset (Fin n))
    (orbit : Finset (State n)) : 0 ≤ orbitToll either receivers orbit := by
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro s _
  apply Finset.sum_nonneg
  intro x _
  rw [receiver_flag_eq]
  split <;> norm_num

private theorem equal_ports_fixed {n : ℕ} (either : Bool) (q : RequestsField n) (v : Bool) :
    portStep either q (fun _ => (v, v)) = (fun _ => (v, v)) := by
  funext x
  change applyGuard (fun _ => exchange either (q x)) (v, v) = (v, v)
  unfold applyGuard
  split <;> rfl

/-- A uniform occupied port field yields zero on both rules, including
    with mixed requests. Every other orbit has nonnegative Toll. -/
theorem minimum_orbit_toll (n bound : ℕ) (either : Bool) (receivers : Finset (Fin n)) :
    ∃ o ∈ enumerateOrbits n either bound, orbitToll either receivers o = 0 ∧
      ∀ p ∈ enumerateOrbits n either bound, 0 ≤ orbitToll either receivers p := by
  let fields : Fields n := (fun _ => (true, false), fun _ => false, fun _ => (false, false))
  let o := orbitWithin either bound (0, fields)
  have ho : o ∈ enumerateOrbits n either bound := by
    unfold enumerateOrbits
    exact Finset.mem_image.mpr ⟨fields, Finset.mem_univ _, rfl⟩
  refine ⟨o, ho, ?_, fun p _ => orbit_toll_nonneg either receivers p⟩
  unfold orbitToll orbitAverage
  have hsum : ∑ s ∈ o, ∑ x ∈ receivers, receiverFlag either s x = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    obtain ⟨k, _, hks⟩ := Finset.mem_image.mp hs
    rw [← hks]
    have hp : ((tick n either)^[k] (0, fields)).2.2.2 = (fun _ => (false, false)) := by
      rw [ports_iterate]
      exact (show Function.IsFixedPt (portStep either fields.1) fields.2.2 from
        equal_ports_fixed either fields.1 false).iterate k
    apply Finset.sum_eq_zero
    intro x _
    rw [receiver_flag_eq, hp]
    simp [arrivals, OpenReferenceFlow.streamShift]
  rw [hsum, zero_div]

/-- Each rule attains a minimum over the joint rule and orbit family.
    The common minimum is zero at any positive hazard. -/
theorem both_rules_attain_best_survival (n bound : ℕ) (either : Bool)
    (receivers : Finset (Fin n)) (β : ℝ) (hβ : 0 < β) :
    ∃ o ∈ enumerateOrbits n either bound, orbitToll either receivers o = 0 ∧
      ∀ other, ∀ p ∈ enumerateOrbits n other bound,
        PersistenceMechanics.Gibbs.weight β (orbitToll other receivers p) ≤
          PersistenceMechanics.Gibbs.weight β (orbitToll either receivers o) := by
  obtain ⟨o, ho, hz, _⟩ := minimum_orbit_toll n bound either receivers
  let family : Set (Bool × Finset (State n)) :=
    {i | i.2 ∈ enumerateOrbits n i.1 bound}
  let cost : Bool × Finset (State n) → ℝ := fun i => orbitToll i.1 receivers i.2
  have hbest := (PersistenceSelection.within_family_iff_cheapest β hβ cost family 0
    (either, o)).mpr ⟨ho, fun j _ => by
      change orbitToll either receivers o ≤ orbitToll j.1 receivers j.2
      rw [hz]
      exact orbit_toll_nonneg j.1 receivers j.2⟩
  refine ⟨o, ho, hz, ?_⟩
  intro other p hp
  simpa [PersistenceMechanics.Gibbs.weight, cost] using hbest.2 (other, p) hp

/-- Mean Toll among surviving orbits, conditional on equal orbit priors.
    This is a statistic of the supplied family at the given hazard. -/
noncomputable def gibbsOrbitMean {n : ℕ} (either : Bool) (receivers : Finset (Fin n))
    (family : Finset (Finset (State n))) (β : ℝ) : ℝ :=
  let cost : ↥family → ℝ := fun o => orbitToll either receivers o.val
  ∑ o : ↥family, PersistenceMechanics.Gibbs.probability β cost o * cost o

end PMTransport.RingReceiver
