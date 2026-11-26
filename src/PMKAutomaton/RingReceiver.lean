import PMKAutomaton.LocalController
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Closed two-stream receiver

A periodic identification closes the encoded root line. It supplies a
finite state space with internal arrivals. The retained requests still
belong to that state. The test keeps every initial request and port field.

## Interface, clock and admission notes

### AND and OR are different dynamics

`LocalController.complemented_guard` proves De Morgan duality.
On the same incoming pair, OR with both requests complemented gives
the AND output with its ports swapped (`complemented_output`).
`HandoffAdmittance.repair_receiver_after_exchange` realizes a swap at
the receiver as an extra maintenance operation. It links two
one-visit outputs.

Complementing requests and swapping each port pair defines a local
involution. It commutes with the bare phase advance and preserves
the sum of the two port populations at each site
(`receiver_dual_involutive`, `receiver_dual_local`,
`receiver_dual_bare_clock`, `receiver_dual_population`).
It fails to carry an AND tick to an OR tick
(`receiver_dual_not_conjugate`). The live and record streams go to
opposite neighbours. The maintenance swap changes which stream
carries the incoming value. See `OpenReferenceFlow.exchange_reflects`
and `bypass_transmits`.

The certified root probe also distinguishes the updates. At phase
zero the idle pair leaves the probe unchanged. Its complemented
pair fires the reflection even with equal receiver ports
(`receiver_dual_probe_counterexample`). More generally, no injective
relabeling that keeps the clock phase and complements both request
bits everywhere can carry one update to the other
(`no_request_complement_conjugacy`). From phase zero, every OR state
with both requests set everywhere returns after two periods. Under
AND with both requests clear, a localized live value shifts out of
its original site.

The mismatch flag registers on the exchange visit. On the same
arrivals `complemented_exchange_flags` puts the mismatch contribution
on exactly one of the two accounts. For an orthogonal pair of unit
basis values, the AND bypass accounts for zero receiver flags and the
complemented OR exchange accounts for one, even with the port values
swapped (`receiver_dual_flag_counterexample`). Equal arrivals hide
this difference.

The closed-ring test computes stationary traffic on three, four and five sites The receiver-flag minima tie and the
historical Gibbs comparison depends on the prior. With the boundary
account below the [open admission contract](TODO.md#admission-and-ports)
at the use of a mixed receiver output by an admitted downstream trace.
The electric reference choice still requires its writer trace
and prices. Choosing colour or lepton complements the electric
sector bit and keeps the position bit
(`ElectricHeavyRecord.reference_flags_from_orbit_bits`).
The receiver result gives no identification with this sector bit.

### Fan-out at a receiver

`Components.ring_observations_local` puts the two output values and
the comparison flag in the same read neighbourhood. Each depends
on the local requests and the two adjacent arrivals. The guard
determines outgoing stream identity at that event. Following a stream
to another node requires its next shift. Local determination provides
no clock slot or input port to an EP consumer. It does exclude
reconstructing arbitrary later arrivals from the same initial local
stencil (`OpenHandoff.neighbours_do_not_determine_second_visit`).

| Possible attachment at the visit | Locally determined datum | Downstream consequence if attached |
| --- | --- | --- |
| X → E | Routed value plus live/record destination. The destination on the next link follows the outgoing stream. | Producer of the writer's payload and therefore its input distribution and slot counts. The mixed witness can route to different ports. |
| F → E | Occupied retained record at a supplied local or arriving slot. A later export is a different visit. | Supplies the writer polarity, readiness or insertion guard when the physical encoding makes the record such an input. |
| D → E | Executed comparison and its mismatch result on that input. | May furnish a registration and the Toll in `exp(−T/2)`. A zero flag can accompany an executed exchange. |

All three are cases of W. The clock permits reasoning about when the
core values are available. The EP read event, its position relative
to that tick and its attachment still require W/T/U. No case follows
as the sole physical attachment.

### Least cost on certified traces

The [selection theorem](Interface.lean) minimizes the cost within
a supplied admitted family. Compare equal observation windows and
use the same rate units.

| Trace or booking | Certified differential | Consequence |
| --- | --- | --- |
| Tagged open trace with common reader and disposal | Same booked core comparisons and tagged exports. `tagged_trace_observable_eq` and `tagged_rule_exports`. In the all-erase account, each pays one per tick (`open_cycle_erase_all`). | **S** on the tagged read and erasure account. Equal remaining work is needed for equality of the complete Toll. |
| Retained ring without a comparison reader | No comparison registration and no exported erasure. `ring_cycle_erasure`. | The certified subtotal is zero for either guard and either bank placement. Distinguishable outputs still exist. A zero subtotal is a cost tie, not a machine symmetry. |
| Site zero on the occupied mixed ring with the same booked comparisons | `Values.mixedReceiverRate_and` gives zero for AND. `mixedReceiverRate_or` gives the booked fraction of the period for OR. Booking all 43 gives a unit difference per tick. | AND is cheaper in this comparison when its extra remaining rate is smaller than that fraction (`mixed_and_cheaper_iff`). With equal other work and a positive booked fraction it has greater survival. |
| Mixed export or paid FIFO and hold visits | The boundary charges its booked erased bits. The joint lift does not book a comparison, pick the exported port, or price a FIFO write. | The difference needs the existing W/D/B/K inputs. Arbitrary trace averaging also needs O/H. |

Least Toll does not select a physical member from these data.
The identity of the physical comparison and its remaining costs
come before the comparison. A common partial cost does not imply
that the packet, destination or flag factors through a quotient.
-/

namespace PMKAutomaton.RingReceiver

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
    (Equiv.prodCongr (finRotate PMSubstrate.E8Values.Delta) (Equiv.refl _))

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

theorem ring_five_neighbourhood :
    ∀ x : Fin 5, finRotate 5 x ≠ x ∧ (finRotate 5).symm x ≠ x ∧
      finRotate 5 x ≠ (finRotate 5).symm x := by
  decide +kernel

/-! ## Exact cyclic traffic -/

abbrev Slot (n : ℕ) := Fin n × Bool

/-- Source of an output slot. False is live and true is record. -/
def portSource {n : ℕ} (switches : Fin n → Bool) (p : Slot n) : Slot n :=
  let record := p.2 != switches p.1
  if record then (finRotate n p.1, true) else ((finRotate n).symm p.1, false)

/-- The retained switches permute the slots: the input direction first
determines the destination site, and the switch there recovers the output side. -/
theorem portSource_injective {n : ℕ} (switches : Fin n → Bool) :
    Function.Injective (portSource switches) := by
  let destination (p : Slot n) :=
    if p.2 then (finRotate n).symm p.1 else finRotate n p.1
  let forward (p : Slot n) : Slot n :=
    (destination p, p.2 != switches (destination p))
  have h : Function.LeftInverse forward (portSource switches) := by
    rintro ⟨x, bit⟩
    cases bit <;> cases hs : switches x <;> simp [forward, destination, portSource, hs, -finRotate_apply, -finRotate_symm_apply]
  exact h.injective

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

/-- A single output slot follows one backward path through the retained
exchange pattern, independent of the other slot values. -/
theorem port_iterate_source {n : ℕ} (either : Bool) (q : RequestsField n)
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

theorem slot_period_five :
    ∀ q : Fin 5 → Bool, ∀ p : Slot 5, (portSource q)^[120] p = p := by
  decide +kernel

private def probeClock (u : Phase × (Requests × Bool)) : Phase × (Requests × Bool) :=
  (finRotate PMSubstrate.E8Values.Delta u.1, advanceProbe u.1 u.2)

private theorem probe_return :
    ∀ c : Requests, ∀ b : Bool, (probeClock^[2 * PMSubstrate.E8Values.Delta]) (0, (c, b)) = (0, (c, b)) := by
  decide +kernel

/-- One phase-zero block flips the probe side exactly for mixed requests. -/
theorem probe_one_period :
    ∀ c : Requests, ∀ b : Bool, (probeClock^[PMSubstrate.E8Values.Delta]) (0, (c, b)) =
      (0, (c, if c.1 = c.2 then b else !b)) := by
  decide +kernel

theorem phase_iterate {n : ℕ} (either : Bool) (s : State n) (k : ℕ) :
    ((tick n either)^[k] s).1 = (finRotate PMSubstrate.E8Values.Delta)^[k] s.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact congrArg (finRotate PMSubstrate.E8Values.Delta) ih

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

/-- Complete a return of the port field on a multiple of the two-clock
probe period. The requests, phase and probe sides return as well. -/
theorem ring_return_of_ports {n t : ℕ} (either : Bool) (s : State n) (hs : s.1 = 0)
    (hp : (portStep either s.2.1)^[t] s.2.2.2 = s.2.2.2)
    (hc : 2 * PMSubstrate.E8Values.Delta ∣ t) : (tick n either)^[t] s = s := by
  let u := (tick n either)^[t] s
  have hphase : Function.IsPeriodicPt (finRotate PMSubstrate.E8Values.Delta) PMSubstrate.E8Values.Delta s.1 :=
    CarrierReferenceCycle.clock_closes s.1
  have hphase' := (hphase.trans_dvd (dvd_trans (dvd_mul_left PMSubstrate.E8Values.Delta 2) hc)).eq
  have hprobe (x : Fin n) :
      Function.IsPeriodicPt probeClock (2 * PMSubstrate.E8Values.Delta) (s.1, (s.2.1 x, s.2.2.1 x)) := by
    rw [hs]
    exact probe_return (s.2.1 x) (s.2.2.1 x)
  have hprobes (x : Fin n) : (u.1, (u.2.1 x, u.2.2.1 x)) =
      (s.1, (s.2.1 x, s.2.2.1 x)) :=
    (probe_iterate either s x t).trans ((hprobe x).trans_dvd hc).eq
  change u = s
  refine Prod.ext ((phase_iterate either s t).trans hphase') (Prod.ext (requests_iterate either s t) ?_)
  apply Prod.ext
  · funext x
    exact congrArg (fun p : Phase × (Requests × Bool) => p.2.2) (hprobes x)
  · exact (ports_iterate either s t).trans hp

/-- Combine any common slot period with the two-clock probe period. -/
theorem ring_return {n k t : ℕ} (either : Bool) (s : State n) (hs : s.1 = 0)
    (hslot : ∀ p : Slot n, (portSource (exchange either ∘ s.2.1))^[k] p = p)
    (hk : k ∣ t) (hc : 2 * PMSubstrate.E8Values.Delta ∣ t) : (tick n either)^[t] s = s := by
  apply ring_return_of_ports either s hs _ hc
  have hp (p : Slot n) : slotValue ((portStep either s.2.1)^[t] s.2.2.2) p =
      slotValue s.2.2.2 p := by
    have h : Function.IsPeriodicPt (portSource (exchange either ∘ s.2.1)) k p := hslot p
    rw [port_iterate_source, (h.trans_dvd hk).eq]
  funext x
  exact Prod.ext (hp (x, false)) (hp (x, true))

theorem ring_return_three (either : Bool) (s : State 3) (hs : s.1 = 0) :
    (tick 3 either)^[516] s = s :=
  ring_return either s hs (slot_period_three _) (by decide +kernel) (by decide +kernel)

theorem ring_return_four (either : Bool) (s : State 4) (hs : s.1 = 0) :
    (tick 4 either)^[1032] s = s :=
  ring_return either s hs (slot_period_four _) (by decide +kernel) (by decide +kernel)

theorem ring_return_five (either : Bool) (s : State 5) (hs : s.1 = 0) :
    (tick 5 either)^[5160] s = s :=
  ring_return either s hs (slot_period_five _) (by decide +kernel) (by decide +kernel)

/-- Starting the enumeration at phase zero loses no orbit. -/
theorem phase_zero_seed {n : ℕ} (either : Bool) (s : State n) :
    ∃ fields : Fields n, (tick n either)^[s.1.val] (0, fields) = s := by
  obtain ⟨u, hu⟩ := ((tick n either).surjective.iterate s.1.val) s
  have hp : (finRotate PMSubstrate.E8Values.Delta)^[s.1.val] u.1 = s.1 := by
    rw [← phase_iterate either u s.1.val, hu]
  have h0 := ((finRotate PMSubstrate.E8Values.Delta).injective.iterate s.1.val)
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

/-- A common ring input with mixed requests and unequal arrivals. -/
def mixedBasisRing : State 3 :=
  (0, (fun _ => (true, false), (fun _ => false, fun _ => (false, true))))

/-- On the same occupied input the AND receiver bypasses and OR runs
    the unit mismatch comparison. This is a flag account, separate from
    erasure at any boundary. -/
theorem mixed_ring_flags :
    receiverFlag false mixedBasisRing 0 = 0 ∧
      receiverFlag true mixedBasisRing 0 = 1 := by
  constructor <;> rw [receiver_flag_eq] <;>
    simp [mixedBasisRing, arrivals, OpenReferenceFlow.streamShift, exchange]

/-- The amplitude difference when that one paid receiver comparison
    supplies the entire specified Toll. -/
theorem mixed_ring_flag_amplitudes :
    PersistenceMechanics.EffectiveAction.attenuationWeight 1 (receiverFlag false mixedBasisRing 0) = 1 ∧
      PersistenceMechanics.EffectiveAction.attenuationWeight 1 (receiverFlag true mixedBasisRing 0) = Real.exp (-(1 : ℝ) / 2) := by
  rw [mixed_ring_flags.1, mixed_ring_flags.2]
  simp [PersistenceMechanics.EffectiveAction.attenuationWeight]

/-- Expected receiver registrations per tick on an orbit. The sum may
    cover one receiver or all of them. -/
noncomputable def orbitRegistrationRate {n : ℕ} (either : Bool) (receivers : Finset (Fin n))
    (orbit : Finset (State n)) : ℝ :=
  orbitAverage orbit fun s => ∑ x ∈ receivers, receiverFlag either s x

private theorem mixed_ports_remain_unequal (either : Bool) (n : ℕ) :
    ∃ p : Ports, p.1 ≠ p.2 ∧
      ((tick 3 either)^[n] mixedBasisRing).2.2.2 = (fun _ => p) := by
  induction n with
  | zero => exact ⟨(false, true), Bool.false_ne_true, rfl⟩
  | succ n ih =>
    obtain ⟨p, hneq, hp⟩ := ih
    let s := (tick 3 either)^[n] mixedBasisRing
    have hq : s.2.1 = (fun _ => (true, false)) := requests_iterate _ _ _
    refine ⟨if either then p.swap else p, ?_, ?_⟩
    · cases either
      · exact hneq
      · exact Ne.symm hneq
    · rw [Function.iterate_succ_apply']
      change (tick 3 either s).2.2.2 = _
      funext x
      rw [tick_ports, hq, show s.2.2.2 = (fun _ => p) from hp]
      cases either <;> rfl

theorem mixed_ring_iterate_flag (either : Bool) (n : ℕ) (x : Fin 3) :
    receiverFlag either ((tick 3 either)^[n] mixedBasisRing) x = if either then 1 else 0 := by
  obtain ⟨p, hneq, hp⟩ := mixed_ports_remain_unequal either n
  rw [receiver_flag_eq, requests_iterate, hp]
  cases either <;> simp [mixedBasisRing, arrivals, OpenReferenceFlow.streamShift, exchange, hneq]

theorem mixed_ring_registration_rate (either : Bool) :
    orbitRegistrationRate either {0} (orbitWithin either 516 mixedBasisRing) = if either then 1 else 0 := by
  let orbit := orbitWithin either 516 mixedBasisRing
  have hzero : mixedBasisRing ∈ orbit :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by decide +kernel), rfl⟩
  have hcard : (orbit.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨_, hzero⟩).ne'
  have hsum : (∑ s ∈ orbit, receiverFlag either s 0) = ∑ _s ∈ orbit, (if either then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro s hs
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hs
    exact mixed_ring_iterate_flag either n 0
  change ((∑ s ∈ orbit, ∑ x ∈ ({0} : Finset (Fin 3)), receiverFlag either s x) / orbit.card) = _
  simp only [Finset.sum_singleton]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hcard

private theorem orbit_registration_rate_nonneg {n : ℕ} (either : Bool) (receivers : Finset (Fin n))
    (orbit : Finset (State n)) : 0 ≤ orbitRegistrationRate either receivers orbit := by
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
theorem minimum_orbit_registration_rate (n bound : ℕ) (either : Bool) (receivers : Finset (Fin n)) :
    ∃ o ∈ enumerateOrbits n either bound, orbitRegistrationRate either receivers o = 0 ∧
      ∀ p ∈ enumerateOrbits n either bound, 0 ≤ orbitRegistrationRate either receivers p := by
  let fields : Fields n := (fun _ => (true, false), fun _ => false, fun _ => (false, false))
  let o := orbitWithin either bound (0, fields)
  have ho : o ∈ enumerateOrbits n either bound := by
    unfold enumerateOrbits
    exact Finset.mem_image.mpr ⟨fields, Finset.mem_univ _, rfl⟩
  refine ⟨o, ho, ?_, fun p _ => orbit_registration_rate_nonneg either receivers p⟩
  unfold orbitRegistrationRate orbitAverage
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
    ∃ o ∈ enumerateOrbits n either bound, orbitRegistrationRate either receivers o = 0 ∧
      ∀ other, ∀ p ∈ enumerateOrbits n other bound,
        PersistenceMechanics.Gibbs.weight β (orbitRegistrationRate other receivers p) ≤
          PersistenceMechanics.Gibbs.weight β (orbitRegistrationRate either receivers o) := by
  obtain ⟨o, ho, hz, _⟩ := minimum_orbit_registration_rate n bound either receivers
  let family : Set (Bool × Finset (State n)) :=
    {i | i.2 ∈ enumerateOrbits n i.1 bound}
  let cost : Bool × Finset (State n) → ℝ := fun i => orbitRegistrationRate i.1 receivers i.2
  have hbest := (PersistenceSelection.within_family_iff_cheapest β hβ cost family 0
    (either, o)).mpr ⟨ho, fun j _ => by
      change orbitRegistrationRate either receivers o ≤ orbitRegistrationRate j.1 receivers j.2
      rw [hz]
      exact orbit_registration_rate_nonneg j.1 receivers j.2⟩
  refine ⟨o, ho, hz, ?_⟩
  intro other p hp
  simpa [PersistenceMechanics.Gibbs.weight, cost] using hbest.2 (other, p) hp

/-- A rule represented by a subset of the joint ensemble has the sum
    of its survivors' shares. Its numerator is a sum of survival
    weights with the supplied priors. -/
theorem survivor_mass_of_subset {ι : Type*} [Fintype ι] (members : Finset ι)
    (prior : ι → ℝ) (β : ℝ) (action : ι → ℝ) :
    (∑ i ∈ members, PersistenceMechanics.Selection.survivor prior β action i) =
      (∑ i ∈ members, prior i * PersistenceMechanics.Gibbs.weight β (action i)) /
        (∑ i, prior i * PersistenceMechanics.Gibbs.weight β (action i)) := by
  simp only [PersistenceMechanics.Selection.survivor, PersistenceMechanics.Gibbs.weight,
    Finset.sum_div]

/-- Mean Toll among surviving orbits, conditional on equal orbit priors.
    This is a statistic of the supplied family at the given hazard. -/
noncomputable def gibbsOrbitMean {n : ℕ} (either : Bool) (receivers : Finset (Fin n))
    (family : Finset (Finset (State n))) (β : ℝ) : ℝ :=
  let cost : ↥family → ℝ := fun o => orbitRegistrationRate either receivers o.val
  ∑ o : ↥family, PersistenceMechanics.Gibbs.probability β cost o * cost o

end PMKAutomaton.RingReceiver
