import PMElementaryParticles.IsolatedExcitation
import PMElementaryParticles.WireSchedule
import PMKAutomaton.RingReceiver
import PMKAutomaton.Components

/-!
# Embedding the isolated excitation into the retained receiver

`IsolatedExcitation.occupiedInput` supplies one carrier label and one 16-slot
packet label.  This file records two embeddings.

* `uniformPorts` is the **uniform field (all sites, both streams)**.  It is not
  one excitation and is kept only as a control.  Its equal arrivals make the
  receiver flag zero for a reason built into the embedding, not a machine
  result.
* `localizedPorts x0 packet` is the one-excitation field: site `x0` has live
  `active packet` and record vacuum (`false`); every other site and both
  record/live values are vacuum (`false`).  This is the embedding to use for
  the localized trace.

The phase, retained requests and probe bits are not read out of the packet;
they are the open controller fields G/T and are named in `ReceiverFields`.
`wall` and `record` index the certified vacuum family from
`vacuum_nonunique`; both are carried, not selected.
-/

noncomputable section
namespace PMElementaryParticles.IsolatedExcitation

open PMConstants.PacketGaugeActions
open PMElementaryParticles.ProtocolInventory
open PMKAutomaton
open PMKAutomaton.RingReceiver
open PMAction
open scoped BigOperators

/-- Three sites is the smallest certified ring with two distinct incoming
neighbours (`RingReceiver.ring_neighbourhood`). -/
abbrev IsolatedSite := Fin 3

abbrev IsolatedRequests := LocalController.Requests
abbrev IsolatedPorts := LocalController.Ports

/-- Named open controller fields.  The phase, requests and probe are not read
out of the packet.  `wall` and `record` index the certified vacuum family from
`vacuum_nonunique`; both are carried, not selected. -/
structure ReceiverFields where
  phase : Fin PMSubstrate.E8Values.Delta
  requests : IsolatedSite → IsolatedRequests
  probe : IsolatedSite → Bool
  wall : Bool
  record : Bool

/-- Number of true port bits in one two-stream port pair. -/
def portBitCountPorts (p : IsolatedPorts) : ℕ :=
  (if p.1 then 1 else 0) + (if p.2 then 1 else 0)

/-- Number of true port bits in a three-site port field. -/
def portBitCount (ports : IsolatedSite → IsolatedPorts) : ℕ :=
  ∑ x, portBitCountPorts (ports x)

/-- Uniform field: every site has the same live/record value.  This is all
sites and both streams, not one excitation. -/
def uniformPorts (packet : PacketLabel) : IsolatedSite → IsolatedPorts :=
  fun _ => (active packet, active packet)

/-- The one-excitation port field: one live packet at `x0`, record vacuum
there, and vacuum everywhere else.  Here vacuum is the Boolean value `false`;
the physical reference vector is separately indexed by `ReceiverFields`. -/
def localizedPorts (x0 : IsolatedSite) (packet : PacketLabel) :
    IsolatedSite → IsolatedPorts :=
  fun x => if x = x0 then (active packet, false) else (false, false)

/-- Uniform embedding, retained only as a control field. -/
def embed (c : Fin 3) (_vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) : State 3 :=
  (fields.phase, (fields.requests, (fields.probe, uniformPorts packet)))

/-- Localized embedding of the one-excitation field. -/
def localizedEmbed (c : Fin 3) (_vacuum : VacuumLabel c) (packet : PacketLabel)
    (x0 : IsolatedSite) (fields : ReceiverFields) : State 3 :=
  (fields.phase, (fields.requests, (fields.probe, localizedPorts x0 packet)))

theorem embed_ports_uniform (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (x : IsolatedSite) :
    (embed c vacuum packet fields).2.2.2 x = (active packet, active packet) := rfl

theorem localizedEmbed_ports (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (x0 : IsolatedSite) (fields : ReceiverFields) (x : IsolatedSite) :
    (localizedEmbed c vacuum packet x0 fields).2.2.2 x =
      (if x = x0 then (active packet, false) else (false, false)) := rfl

theorem embed_occupied_packet (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (_fields : ReceiverFields) :
    occupiedInput c vacuum packet (.inr packet) = true :=
  occupiedInput_packet c vacuum packet

/-! ## Uniform control field: equal arrivals, zero by construction -/

/-- A uniform equal port field is fixed by the guarded receiver step. -/
theorem uniform_ports_tick (either : Bool) (s : State 3) (v : Bool)
    (h : ∀ x, s.2.2.2 x = (v, v)) (x : IsolatedSite) :
    (tick 3 either s).2.2.2 x = (v, v) := by
  rw [tick_ports]
  have ha : arrivals s.2.2.2 x = (v, v) := by
    simp [arrivals, OpenReferenceFlow.streamShift, h]
  rw [ha]
  change LocalController.applyGuard
    (fun _ => exchange either (s.2.1 x)) (v, v) = (v, v)
  unfold LocalController.applyGuard
  split <;> rfl

theorem uniform_ports_iterate (either : Bool) (s : State 3) (v : Bool)
    (h : ∀ x, s.2.2.2 x = (v, v)) (k : ℕ) (x : IsolatedSite) :
    ((tick 3 either)^[k] s).2.2.2 x = (v, v) := by
  induction k generalizing x with
  | zero => exact h x
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact uniform_ports_tick either _ v ih x

/-- On equal arrivals the receiver registers zero, under either rule. -/
theorem receiver_flag_zero_of_uniform (either : Bool) (s : State 3) (v : Bool)
    (h : ∀ x, s.2.2.2 x = (v, v)) (x : IsolatedSite) :
    receiverFlag either s x = 0 := by
  rw [receiver_flag_eq]
  have ha : arrivals s.2.2.2 x = (v, v) := by
    simp [arrivals, OpenReferenceFlow.streamShift, h]
  rw [ha]
  simp

/-- Uniform field, not one excitation: zero under AND. -/
theorem uniform_flag_zero_AND (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (k : ℕ) (x : IsolatedSite) :
    receiverFlag false ((tick 3 false)^[k] (embed c vacuum packet fields)) x = 0 := by
  apply receiver_flag_zero_of_uniform
  exact uniform_ports_iterate false _ _ (embed_ports_uniform c vacuum packet fields) k

/-- Uniform field, not one excitation: zero under OR. -/
theorem uniform_flag_zero_OR (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (k : ℕ) (x : IsolatedSite) :
    receiverFlag true ((tick 3 true)^[k] (embed c vacuum packet fields)) x = 0 := by
  apply receiver_flag_zero_of_uniform
  exact uniform_ports_iterate true _ _ (embed_ports_uniform c vacuum packet fields) k

/-- Uniform field, not one excitation: AND and OR both register zero. -/
theorem uniform_AND_OR_tie (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (k : ℕ) (x : IsolatedSite) :
    receiverFlag false ((tick 3 false)^[k] (embed c vacuum packet fields)) x =
      receiverFlag true ((tick 3 true)^[k] (embed c vacuum packet fields)) x := by
  rw [uniform_flag_zero_AND, uniform_flag_zero_OR]

/-- Uniform control field: its 43-tick receiver sum is zero. -/
theorem uniform_period_registrations_zero (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (fields : ReceiverFields) :
    (∑ t : Fin PMSubstrate.E8Values.Delta, ∑ x : IsolatedSite,
      receiverFlag either ((tick 3 either)^[t.val]
        (embed c vacuum packet fields)) x) = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro x _
  cases either
  · exact uniform_flag_zero_AND c vacuum packet fields t.val x
  · exact uniform_flag_zero_OR c vacuum packet fields t.val x

/-! ## Occupancy checks -/

theorem portBitCount_applyGuard (g : LocalController.Guard) (p : IsolatedPorts) :
    portBitCountPorts (LocalController.applyGuard g p) = portBitCountPorts p := by
  unfold LocalController.applyGuard portBitCountPorts
  split <;> simp [add_comm]

theorem portBitCount_arrivals (ports : IsolatedSite → IsolatedPorts) :
    portBitCount (arrivals ports) = portBitCount ports := by
  unfold portBitCount portBitCountPorts arrivals OpenReferenceFlow.streamShift
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · exact Equiv.sum_comp (finRotate 3).symm
      (fun x => if (ports x).1 then 1 else 0)
  · exact Equiv.sum_comp (finRotate 3)
      (fun x => if (ports x).2 then 1 else 0)

theorem portBitCount_tick (either : Bool) (s : State 3) :
    portBitCount ((tick 3 either s).2.2.2) = portBitCount s.2.2.2 := by
  unfold portBitCount
  calc
    (∑ x, portBitCountPorts ((tick 3 either s).2.2.2 x)) =
        ∑ x, portBitCountPorts (arrivals s.2.2.2 x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [tick_ports]
      exact portBitCount_applyGuard _ _
    _ = ∑ x, portBitCountPorts (s.2.2.2 x) := portBitCount_arrivals s.2.2.2

/-- Localized occupancy: one true live bit when the packet is active, zero
otherwise. -/
theorem localizedPorts_occupancy (x0 : IsolatedSite) (packet : PacketLabel) :
    portBitCount (localizedPorts x0 packet) = if active packet then 1 else 0 := by
  rw [portBitCount, Finset.sum_eq_single_of_mem x0 (Finset.mem_univ x0)]
  · by_cases h : active packet <;>
      simp [localizedPorts, portBitCountPorts, h]
  · intro b _ hb
    simp [localizedPorts, portBitCountPorts, hb]

/-- The localized one-excitation occupancy is preserved by `tick` under both
rules, at every tick. -/
theorem localized_occupancy_preserved (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (x0 : IsolatedSite)
    (fields : ReceiverFields) (k : ℕ) :
    portBitCount (((tick 3 either)^[k]
      (localizedEmbed c vacuum packet x0 fields)).2.2.2) =
      (if active packet then 1 else 0) := by
  induction k with
  | zero => simpa [localizedEmbed] using localizedPorts_occupancy x0 packet
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rw [portBitCount_tick, ih]

/-- The old uniform field fails the occupancy check: six true bits when the
packet is active.  It is not one excitation. -/
theorem uniformPorts_occupancy (packet : PacketLabel) :
    portBitCount (uniformPorts packet) = if active packet then 6 else 0 := by
  by_cases h : active packet <;>
    simp [portBitCount, uniformPorts, portBitCountPorts, h]

/-! ## Localized trace helpers

The active packet is a fixed 16-slot label with `active = true`; the request
field stays the named open controller input G.
-/

def activePacket : PacketLabel := Sum.inl ((0 : Fin 3), (0 : Fin 2))

theorem active_activePacket : active activePacket = true := rfl

/-- The request field is retained; this is `RingReceiver.requests_iterate`. -/
theorem localized_requests_retained (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (x0 : IsolatedSite)
    (fields : ReceiverFields) (k : ℕ) :
    ((tick 3 either)^[k] (localizedEmbed c vacuum packet x0 fields)).2.1 =
      fields.requests :=
  RingReceiver.requests_iterate either _ k

private theorem port_iterate_source_iso (either : Bool)
    (q : IsolatedSite → IsolatedRequests) (ports : IsolatedSite → IsolatedPorts)
    (p : RingReceiver.Slot 3) (k : ℕ) :
    RingReceiver.slotValue ((RingReceiver.portStep either q)^[k] ports) p =
      RingReceiver.slotValue ports
        ((RingReceiver.portSource (RingReceiver.exchange either ∘ q))^[k] p) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', RingReceiver.port_step_source, ih,
      Function.iterate_succ_apply]

/-- The port field of the localized state has period 12 under both rules and
every request field, by the certified three-site slot period. -/
theorem portStep_period_twelve (either : Bool) (r : IsolatedSite → IsolatedRequests)
    (ports : IsolatedSite → IsolatedPorts) :
    (RingReceiver.portStep either r)^[12] ports = ports := by
  funext x
  apply Prod.ext
  · have h := port_iterate_source_iso either r ports (x, false) 12
    simpa [RingReceiver.slotValue, RingReceiver.slot_period_three] using h
  · have h := port_iterate_source_iso either r ports (x, true) 12
    simpa [RingReceiver.slotValue, RingReceiver.slot_period_three] using h

theorem localized_ports_period_twelve (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (x0 : IsolatedSite)
    (fields : ReceiverFields) :
    ((tick 3 either)^[12] (localizedEmbed c vacuum packet x0 fields)).2.2.2 =
      (localizedEmbed c vacuum packet x0 fields).2.2.2 := by
  rw [RingReceiver.ports_iterate]
  exact portStep_period_twelve either fields.requests (localizedPorts x0 packet)

def mkFields (r : IsolatedSite → IsolatedRequests) : ReceiverFields :=
  ⟨0, r, fun _ => false, false, false⟩

def localizedPortsAt (either : Bool) (r : IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite) (k : ℕ) : IsolatedSite → IsolatedPorts :=
  (RingReceiver.portStep either r)^[k] (localizedPorts x0 activePacket)

/-- Computable receiver flag on the localized state. -/
def localizedFlagNat (either : Bool) (r : IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite) (k : ℕ) (x : IsolatedSite) : ℕ :=
  if RingReceiver.exchange either (r x) = true ∧
      (RingReceiver.arrivals (localizedPortsAt either r x0 k) x).1 ≠
      (RingReceiver.arrivals (localizedPortsAt either r x0 k) x).2
    then 1 else 0

/-- The computable flag is the actual `receiverFlag` on the iterated localized
embedding. -/
theorem localizedFlag_eq_nat (either : Bool) (r : IsolatedSite → IsolatedRequests)
    (vacuum : VacuumLabel 0) (x0 : IsolatedSite) (k : ℕ) (x : IsolatedSite) :
    receiverFlag either ((tick 3 either)^[k]
      (localizedEmbed 0 vacuum activePacket x0 (mkFields r))) x =
      (localizedFlagNat either r x0 k x : ℝ) := by
  have hq : ((tick 3 either)^[k]
      (localizedEmbed 0 vacuum activePacket x0 (mkFields r))).2.1 = r := by
    simpa [mkFields] using localized_requests_retained either 0
      vacuum activePacket x0 (mkFields r) k
  have hp : ((tick 3 either)^[k]
      (localizedEmbed 0 vacuum activePacket x0 (mkFields r))).2.2.2 =
      localizedPortsAt either r x0 k := by
    rw [RingReceiver.ports_iterate]
    rfl
  rw [receiver_flag_eq, hq, hp]
  unfold localizedFlagNat
  by_cases h : RingReceiver.exchange either (r x) = true ∧
      (RingReceiver.arrivals (localizedPortsAt either r x0 k) x).1 ≠
      (RingReceiver.arrivals (localizedPortsAt either r x0 k) x).2 <;>
    simp [h]

def localizedInner (either : Bool) (r : IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite) (k : ℕ) : ℕ :=
  ∑ x : IsolatedSite, localizedFlagNat either r x0 k x

def localizedSum (either : Bool) (r : IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, localizedInner either r x0 k

def localizedPeriodSum (either : Bool) (r : IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite) : ℕ :=
  localizedSum either r x0 12

def localizedSum43 (either : Bool) (r : IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite) : ℕ :=
  localizedSum either r x0 43

theorem localizedPortsAt_add_twelve (either : Bool)
    (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) (k : ℕ) :
    localizedPortsAt either r x0 (k + 12) = localizedPortsAt either r x0 k := by
  unfold localizedPortsAt
  rw [Function.iterate_add_apply, portStep_period_twelve]

theorem localizedInner_add_twelve (either : Bool)
    (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) (k : ℕ) :
    localizedInner either r x0 (k + 12) = localizedInner either r x0 k := by
  unfold localizedInner
  apply Finset.sum_congr rfl
  intro x _
  unfold localizedFlagNat
  rw [localizedPortsAt_add_twelve]

theorem localizedInner_add_mul_twelve (either : Bool)
    (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) (n k : ℕ) :
    localizedInner either r x0 (12 * n + k) = localizedInner either r x0 k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [show 12 * (n + 1) + k = 12 * n + (k + 12) by omega]
    rw [ih (k + 12), localizedInner_add_twelve]

theorem localizedSum36_eq (either : Bool)
    (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) :
    localizedSum either r x0 36 = 3 * localizedPeriodSum either r x0 := by
  unfold localizedSum localizedPeriodSum
  rw [show 36 = 12 + 24 by norm_num, Finset.sum_range_add]
  rw [show 24 = 12 + 12 by norm_num, Finset.sum_range_add]
  have h1 : (∑ k ∈ Finset.range 12,
      localizedInner either r x0 (12 + k)) =
      ∑ k ∈ Finset.range 12, localizedInner either r x0 k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show 12 + k = 12 * 1 + k by norm_num,
      localizedInner_add_mul_twelve]
  have h2 : (∑ k ∈ Finset.range 12,
      localizedInner either r x0 (12 + (12 + k))) =
      ∑ k ∈ Finset.range 12, localizedInner either r x0 k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show 12 + (12 + k) = 12 * 2 + k by omega,
      localizedInner_add_mul_twelve]
  rw [h1, h2]
  rw [show localizedSum either r x0 12 =
    ∑ k ∈ Finset.range 12, localizedInner either r x0 k by rfl]
  ring_nf

theorem localizedSum43_eq (either : Bool)
    (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) :
    localizedSum43 either r x0 =
      3 * localizedPeriodSum either r x0 + localizedSum either r x0 7 := by
  unfold localizedSum43
  unfold localizedSum
  rw [show 43 = 36 + 7 by norm_num, Finset.sum_range_add]
  change localizedSum either r x0 36 +
    ∑ k ∈ Finset.range 7, localizedInner either r x0 (36 + k) = _
  rw [localizedSum36_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [show 36 + k = 12 * 3 + k by omega,
    localizedInner_add_mul_twelve]

def localizedSum43Fast (either : Bool) (r : IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite) : ℕ :=
  3 * localizedPeriodSum either r x0 + localizedSum either r x0 7

theorem localizedSum43Fast_eq (either : Bool) (r : IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite) :
    localizedSum43Fast either r x0 = localizedSum43 either r x0 :=
  (localizedSum43_eq either r x0).symm

/-- The exchange pattern is the only part of the retained request field that
enters a receiver flag. -/
def firingPattern (either : Bool) (r : IsolatedSite → IsolatedRequests) :
    IsolatedSite → Bool :=
  fun x => RingReceiver.exchange either (r x)

def sameRequests (q : IsolatedSite → Bool) : IsolatedSite → IsolatedRequests :=
  fun x => (q x, q x)

def boolCode (b : Bool) : ℕ := if b then 1 else 0

def patternCode (q : IsolatedSite → Bool) : ℕ :=
  boolCode (q 0) + 2 * boolCode (q 1) + 4 * boolCode (q 2)

/-- Computed 43-tick sums by firing pattern and packet site.  The order is
`patternCode` 0…7, then `x0` 0,1,2. -/
def patternTable : List (List ℕ) :=
  [[0, 0, 0],
   [14, 14, 15],
   [15, 14, 14],
   [43, 21, 22],
   [14, 15, 14],
   [21, 22, 43],
   [22, 43, 21],
   [43, 43, 43]]

def patternSum (q : IsolatedSite → Bool) (x0 : IsolatedSite) : ℕ :=
  ((patternTable.getD (patternCode q) []).getD x0.val 0)

/-- Rotation of the retained request field. -/
def rotateRequest (d : IsolatedSite) (r : IsolatedSite → IsolatedRequests) :
    IsolatedSite → IsolatedRequests :=
  fun x => r (x - d)

def rotateSite (d x0 : IsolatedSite) : IsolatedSite := x0 + d

def rotatePattern (d : IsolatedSite) (q : IsolatedSite → Bool) :
    IsolatedSite → Bool :=
  fun x => q (x - d)

theorem patternSum_rotate (q : IsolatedSite → Bool) (x0 d : IsolatedSite) :
    patternSum (rotatePattern d q) (rotateSite d x0) = patternSum q x0 := by
  revert q x0 d
  decide +kernel

theorem localizedSum43Fast_eq_pattern :
    ∀ (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) (either : Bool),
      localizedSum43Fast either r x0 = patternSum (firingPattern either r) x0 := by
  decide +kernel

/-- Task B(c): the 43-tick localized sum is the table entry of the exchange
pattern.  The state is `(tick 3 either)^[k] (localizedEmbed ...)` with
`activePacket`. -/
theorem localizedSum43_eq_pattern (either : Bool)
    (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) :
    localizedSum43 either r x0 = patternSum (firingPattern either r) x0 := by
  rw [← localizedSum43Fast_eq]
  exact localizedSum43Fast_eq_pattern r x0 either

/-- Task B(b): rotating both the packet site and the retained request field
leaves the localized 43-tick sum unchanged. -/
theorem localizedSum43_rotate (either : Bool)
    (r : IsolatedSite → IsolatedRequests) (x0 d : IsolatedSite) :
    localizedSum43 either (rotateRequest d r) (rotateSite d x0) =
      localizedSum43 either r x0 := by
  rw [localizedSum43_eq_pattern, localizedSum43_eq_pattern]
  change patternSum (rotatePattern d (firingPattern either r)) (rotateSite d x0) =
    patternSum (firingPattern either r) x0
  exact patternSum_rotate (firingPattern either r) x0 d

/-- The localized sums do depend on `x0` for a fixed request field, so the
ring is only invariant under simultaneous rotation. -/
theorem localizedSum43_x0_depends :
    ∃ r : IsolatedSite → IsolatedRequests, ∃ x0 x1 : IsolatedSite,
      localizedSum43 true r x0 ≠ localizedSum43 true r x1 := by
  refine ⟨(fun x => if x = 2 then (true, true) else (false, false)), 0, 1, ?_⟩
  rw [localizedSum43_eq_pattern, localizedSum43_eq_pattern]
  decide +kernel

/-- Task B(a): AND and OR sums differ exactly when their exchange-pattern
table entries differ.  This is a decidable condition on the retained request
field. -/
def sumsDiffer (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) : Prop :=
  patternSum (firingPattern false r) x0 ≠
    patternSum (firingPattern true r) x0

theorem localized_and_or_differ_iff (r : IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite) :
    localizedSum43 false r x0 ≠ localizedSum43 true r x0 ↔ sumsDiffer r x0 := by
  rw [localizedSum43_eq_pattern false r x0,
    localizedSum43_eq_pattern true r x0]
  rfl

/-- The inactive packet has no live port; every receiver flag and every sum
is zero. -/
def inactivePacket : PacketLabel := Sum.inr (Sum.inr (Sum.inr ((0 : Fin 2))))

theorem active_inactivePacket : active inactivePacket = false := rfl

theorem localized_inactive_flag_zero (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (x0 : IsolatedSite) (fields : ReceiverFields)
    (k : ℕ) (x : IsolatedSite) :
    receiverFlag either ((tick 3 either)^[k]
      (localizedEmbed c vacuum inactivePacket x0 fields)) x = 0 := by
  apply receiver_flag_zero_of_uniform
  have h : ∀ y, (localizedEmbed c vacuum inactivePacket x0 fields).2.2.2 y =
      (false, false) := by
    intro y
    simp [localizedEmbed, localizedPorts, active_inactivePacket]
  exact uniform_ports_iterate either _ false h k

theorem localizedSum43_inactive_zero (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (x0 : IsolatedSite) (fields : ReceiverFields) :
    (∑ t : Fin PMSubstrate.E8Values.Delta, ∑ x : IsolatedSite,
      receiverFlag either ((tick 3 either)^[t.val]
        (localizedEmbed c vacuum inactivePacket x0 fields)) x) = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro x _
  exact localized_inactive_flag_zero either c vacuum x0 fields t.val x

/-- The actual 43-tick receiver sum on the localized embedded state equals the
computed localized sum.  State: `(tick 3 either)^[k] (localizedEmbed ...)` with
`activePacket`; requests `mkFields r`. -/
theorem localized_period_registrations_eq (either : Bool)
    (r : IsolatedSite → IsolatedRequests) (vacuum : VacuumLabel 0)
    (x0 : IsolatedSite) :
    (∑ t : Fin 43, ∑ x : IsolatedSite,
      receiverFlag either ((tick 3 either)^[t.val]
        (localizedEmbed 0 vacuum activePacket x0 (mkFields r))) x) =
      (localizedSum43 either r x0 : ℝ) := by
  let f : ℕ → ℝ := fun k => ∑ x : IsolatedSite,
    receiverFlag either ((tick 3 either)^[k]
      (localizedEmbed 0 vacuum activePacket x0 (mkFields r))) x
  change (∑ t : Fin 43, f t.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  unfold localizedSum43 localizedSum localizedInner
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.cast_sum]
  change f k = ∑ x : IsolatedSite, (localizedFlagNat either r x0 k x : ℝ)
  apply Finset.sum_congr rfl
  intro x _
  exact localizedFlag_eq_nat either r vacuum x0 k x

/-! ## Uniform request fields and ring-size generalization

The retained request field is not forced to be site-independent by any
certified KAutomaton result.  The following results are therefore conditional
on the named hypothesis of homogeneous requests; the four uniform values stay
enumerated.
-/

def HomogeneousRequests {n : ℕ} (r : Fin n → IsolatedRequests) : Prop :=
  ∃ c : IsolatedRequests, ∀ x, r x = c

theorem firingPattern_ne_iff_mixed :
    ∀ r : IsolatedSite → IsolatedRequests,
      firingPattern false r ≠ firingPattern true r ↔
        ∃ x : IsolatedSite, r x = (true, false) ∨ r x = (false, true) := by
  decide +kernel

theorem uniform_falsefalse_sums (x0 : IsolatedSite) :
    localizedSum43 false (fun _ => (false, false)) x0 = 0 ∧
      localizedSum43 true (fun _ => (false, false)) x0 = 0 := by
  constructor <;> rw [localizedSum43_eq_pattern] <;> fin_cases x0 <;> decide +kernel

theorem uniform_truetrue_sums (x0 : IsolatedSite) :
    localizedSum43 false (fun _ => (true, true)) x0 = 43 ∧
      localizedSum43 true (fun _ => (true, true)) x0 = 43 := by
  constructor <;> rw [localizedSum43_eq_pattern] <;> fin_cases x0 <;> decide +kernel

theorem uniform_truefalse_sums (x0 : IsolatedSite) :
    localizedSum43 false (fun _ => (true, false)) x0 = 0 ∧
      localizedSum43 true (fun _ => (true, false)) x0 = 43 := by
  constructor <;> rw [localizedSum43_eq_pattern] <;> fin_cases x0 <;> decide +kernel

theorem uniform_falsetrue_sums (x0 : IsolatedSite) :
    localizedSum43 false (fun _ => (false, true)) x0 = 0 ∧
      localizedSum43 true (fun _ => (false, true)) x0 = 43 := by
  constructor <;> rw [localizedSum43_eq_pattern] <;> fin_cases x0 <;> decide +kernel

/-! ## General ring size for uniform requests -/

structure ReceiverFieldsN (n : ℕ) where
  phase : ℕ
  requests : Fin n → IsolatedRequests
  probe : Fin n → Bool
  wall : Bool
  record : Bool

def portBitCountN (n : ℕ) (ports : Fin n → IsolatedPorts) : ℕ :=
  ∑ x, portBitCountPorts (ports x)

def localizedPortsN (n : ℕ) (x0 : Fin n) (packet : PacketLabel) :
    Fin n → IsolatedPorts :=
  fun x => if x = x0 then (active packet, false) else (false, false)

def localizedEmbedN (n : ℕ) (c : Fin 3) (_vacuum : VacuumLabel c)
    (packet : PacketLabel) (x0 : Fin n) (fields : ReceiverFieldsN n) :
    RingReceiver.State n :=
  (⟨fields.phase % 43, Nat.mod_lt _ (by norm_num)⟩,
    (fields.requests, (fields.probe, localizedPortsN n x0 packet)))

theorem localizedPortsN_occupancy (n : ℕ) (x0 : Fin n) (packet : PacketLabel) :
    portBitCountN n (localizedPortsN n x0 packet) =
      (if active packet then 1 else 0) := by
  rw [portBitCountN, Finset.sum_eq_single_of_mem x0 (Finset.mem_univ x0)]
  · by_cases h : active packet <;>
      simp [localizedPortsN, portBitCountPorts, h]
  · intro b _ hb
    simp [localizedPortsN, portBitCountPorts, hb]

theorem portBitCountN_applyGuard (_n : ℕ) (g : LocalController.Guard)
    (p : IsolatedPorts) :
    portBitCountPorts (LocalController.applyGuard g p) = portBitCountPorts p :=
  portBitCount_applyGuard g p

theorem portBitCountN_arrivals (n : ℕ) (ports : Fin n → IsolatedPorts) :
    portBitCountN n (RingReceiver.arrivals ports) = portBitCountN n ports := by
  unfold portBitCountN portBitCountPorts RingReceiver.arrivals
    OpenReferenceFlow.streamShift
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · exact Equiv.sum_comp (finRotate n).symm
      (fun x => if (ports x).1 then 1 else 0)
  · exact Equiv.sum_comp (finRotate n)
      (fun x => if (ports x).2 then 1 else 0)

theorem portBitCountN_tick (n : ℕ) (either : Bool) (s : RingReceiver.State n) :
    portBitCountN n ((RingReceiver.tick n either s).2.2.2) =
      portBitCountN n s.2.2.2 := by
  unfold portBitCountN
  calc
    (∑ x, portBitCountPorts ((RingReceiver.tick n either s).2.2.2 x)) =
        ∑ x, portBitCountPorts (RingReceiver.arrivals s.2.2.2 x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [RingReceiver.tick_ports]
      exact portBitCountN_applyGuard n _ _
    _ = ∑ x, portBitCountPorts (s.2.2.2 x) := portBitCountN_arrivals n s.2.2.2

theorem localized_occupancy_preservedN (n : ℕ) (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (x0 : Fin n)
    (fields : ReceiverFieldsN n) (k : ℕ) :
    portBitCountN n (((RingReceiver.tick n either)^[k]
      (localizedEmbedN n c vacuum packet x0 fields)).2.2.2) =
      (if active packet then 1 else 0) := by
  induction k with
  | zero => simpa [localizedEmbedN] using localizedPortsN_occupancy n x0 packet
  | succ k ih =>
    rw [Function.iterate_succ_apply', portBitCountN_tick, ih]

def fullRequestsN (n : ℕ) : Fin n → IsolatedRequests := fun _ => (true, true)

def emptyRequestsN (n : ℕ) : Fin n → IsolatedRequests := fun _ => (false, false)

def fullFieldsN (n : ℕ) : ReceiverFieldsN n :=
  ⟨0, fullRequestsN n, fun _ => false, false, false⟩

def emptyFieldsN (n : ℕ) : ReceiverFieldsN n :=
  ⟨0, emptyRequestsN n, fun _ => false, false, false⟩

def localizedFlagNatN (n : ℕ) (either : Bool) (r : Fin n → IsolatedRequests)
    (x0 : Fin n) (k : ℕ) (x : Fin n) : ℕ :=
  if RingReceiver.exchange either (r x) = true ∧
      (RingReceiver.arrivals
        ((RingReceiver.portStep either r)^[k] (localizedPortsN n x0 activePacket)) x).1 ≠
      (RingReceiver.arrivals
        ((RingReceiver.portStep either r)^[k] (localizedPortsN n x0 activePacket)) x).2
    then 1 else 0

def localizedSumN (n : ℕ) (either : Bool) (r : Fin n → IsolatedRequests)
    (x0 : Fin n) (T : ℕ) : ℕ :=
  ∑ k ∈ Finset.range T, ∑ x : Fin n, localizedFlagNatN n either r x0 k x

def mkFieldsN (n : ℕ) (r : Fin n → IsolatedRequests) : ReceiverFieldsN n :=
  ⟨0, r, fun _ => false, false, false⟩

theorem localizedFlagN_eq_nat (n : ℕ) (either : Bool)
    (r : Fin n → IsolatedRequests) (vacuum : VacuumLabel 0) (x0 : Fin n)
    (k : ℕ) (x : Fin n) :
    receiverFlag either ((RingReceiver.tick n either)^[k]
      (localizedEmbedN n 0 vacuum activePacket x0 (mkFieldsN n r))) x =
      (localizedFlagNatN n either r x0 k x : ℝ) := by
  have hq : ((RingReceiver.tick n either)^[k]
      (localizedEmbedN n 0 vacuum activePacket x0 (mkFieldsN n r))).2.1 = r := by
    simpa [mkFieldsN, localizedEmbedN] using RingReceiver.requests_iterate either
      (localizedEmbedN n 0 vacuum activePacket x0 (mkFieldsN n r)) k
  have hp : ((RingReceiver.tick n either)^[k]
      (localizedEmbedN n 0 vacuum activePacket x0 (mkFieldsN n r))).2.2.2 =
      (RingReceiver.portStep either r)^[k] (localizedPortsN n x0 activePacket) := by
    rw [RingReceiver.ports_iterate]
    rfl
  rw [receiver_flag_eq, hq, hp]
  unfold localizedFlagNatN
  by_cases h : RingReceiver.exchange either (r x) = true ∧
      (RingReceiver.arrivals
        ((RingReceiver.portStep either r)^[k] (localizedPortsN n x0 activePacket)) x).1 ≠
      (RingReceiver.arrivals
        ((RingReceiver.portStep either r)^[k] (localizedPortsN n x0 activePacket)) x).2 <;>
    simp [h]


/-- Empty uniform firing: no flag at any tick, any ring size and any T. -/
theorem empty_uniform_flags_zero (n T : ℕ) (either : Bool) (x0 : Fin n) :
    localizedSumN n either (emptyRequestsN n) x0 T = 0 := by
  unfold localizedSumN
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro x _
  unfold localizedFlagNatN emptyRequestsN
  simp [RingReceiver.exchange]

/-- Full uniform firing on a 3-ring: 43 flags in 43 ticks. -/
theorem full_uniform_sum43_three (x0 : Fin 3) :
    localizedSumN 3 true (fullRequestsN 3) x0 43 = 43 := by
  revert x0
  decide +kernel

theorem full_uniform_sum43_four (x0 : Fin 4) :
    localizedSumN 4 true (fullRequestsN 4) x0 43 = 43 := by
  revert x0
  decide +kernel

theorem full_uniform_sum43_five (x0 : Fin 5) :
    localizedSumN 5 true (fullRequestsN 5) x0 43 = 43 := by
  revert x0
  decide +kernel

theorem full_uniform_sum43_six (x0 : Fin 6) :
    localizedSumN 6 true (fullRequestsN 6) x0 43 = 43 := by
  revert x0
  decide +kernel

/-- Full uniform firing on a 3-ring: exactly one flag per tick in the 43-tick
window, at every site x0. -/
theorem full_uniform_flag_count_three (x0 : Fin 3) (k : Fin 43) :
    (∑ x : Fin 3, localizedFlagNatN 3 true (fullRequestsN 3) x0 k.val x) = 1 := by
  revert x0 k
  decide +kernel

theorem full_uniform_flag_count_four (x0 : Fin 4) (k : Fin 43) :
    (∑ x : Fin 4, localizedFlagNatN 4 true (fullRequestsN 4) x0 k.val x) = 1 := by
  revert x0 k
  decide +kernel

theorem full_uniform_flag_count_five (x0 : Fin 5) (k : Fin 43) :
    (∑ x : Fin 5, localizedFlagNatN 5 true (fullRequestsN 5) x0 k.val x) = 1 := by
  revert x0 k
  decide +kernel

theorem full_uniform_flag_count_six (x0 : Fin 6) (k : Fin 43) :
    (∑ x : Fin 6, localizedFlagNatN 6 true (fullRequestsN 6) x0 k.val x) = 1 := by
  revert x0 k
  decide +kernel

/-! ## Task F: unconstrained least Toll

The table `patternSum` has minimum zero exactly on the empty firing pattern.
-/

theorem localizedSum43Fast_zero_iff_empty :
    ∀ (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) (either : Bool),
      localizedSum43Fast either r x0 = 0 ↔
        ∀ x : IsolatedSite, firingPattern either r x = false := by
  decide +kernel

theorem localizedSum43_eq_zero_iff_empty (either : Bool)
    (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) :
    localizedSum43 either r x0 = 0 ↔
      ∀ x : IsolatedSite, firingPattern either r x = false := by
  rw [← localizedSum43Fast_eq]
  exact localizedSum43Fast_zero_iff_empty r x0 either

theorem localizedSum43Fast_nonempty_ge_fourteen :
    ∀ (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) (either : Bool),
      (∃ x : IsolatedSite, firingPattern either r x = true) →
        14 ≤ localizedSum43Fast either r x0 := by
  decide +kernel

theorem localizedSum43_nonempty_ge_fourteen (either : Bool)
    (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite)
    (h : ∃ x : IsolatedSite, firingPattern either r x = true) :
    14 ≤ localizedSum43 either r x0 := by
  rw [← localizedSum43Fast_eq]
  exact localizedSum43Fast_nonempty_ge_fourteen r x0 either h

theorem and_zero_iff_no_true_true_fast :
    ∀ (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite),
      localizedSum43Fast false r x0 = 0 ↔
        ∀ x : IsolatedSite, r x ≠ (true, true) := by
  decide +kernel

/-- AND least Toll: no site has `(true, true)`. -/
theorem and_zero_iff_no_true_true (r : IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite) :
    localizedSum43 false r x0 = 0 ↔ ∀ x : IsolatedSite, r x ≠ (true, true) := by
  rw [← localizedSum43Fast_eq]
  exact and_zero_iff_no_true_true_fast r x0

theorem or_zero_iff_all_false_fast :
    ∀ (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite),
      localizedSum43Fast true r x0 = 0 ↔
        ∀ x : IsolatedSite, r x = (false, false) := by
  decide +kernel

/-- OR least Toll: every site is `(false, false)`. -/
theorem or_zero_iff_all_false (r : IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite) :
    localizedSum43 true r x0 = 0 ↔ ∀ x : IsolatedSite, r x = (false, false) := by
  rw [← localizedSum43Fast_eq]
  exact or_zero_iff_all_false_fast r x0

theorem localizedSumN_zero_of_empty_firing (n T : ℕ) (either : Bool)
    (r : Fin n → IsolatedRequests) (x0 : Fin n)
    (h : ∀ x : Fin n, RingReceiver.exchange either (r x) = false) :
    localizedSumN n either r x0 T = 0 := by
  unfold localizedSumN
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro x _
  unfold localizedFlagNatN
  rw [h x]
  simp

theorem localizedSumN_eight_le_43 (n : ℕ) (either : Bool)
    (r : Fin n → IsolatedRequests) (x0 : Fin n) :
    localizedSumN n either r x0 8 ≤ localizedSumN n either r x0 43 := by
  unfold localizedSumN
  rw [show 43 = 8 + 35 by norm_num, Finset.sum_range_add]
  exact Nat.le_add_right _ _

theorem localizedSumN_four_zero8_iff_empty :
    ∀ (r : Fin 4 → IsolatedRequests) (x0 : Fin 4) (either : Bool),
      localizedSumN 4 either r x0 8 = 0 ↔
        ∀ x : Fin 4, RingReceiver.exchange either (r x) = false := by
  decide +kernel

/-- Task F Step 2: on the 4-ring, zero receiver sum is equivalent to an empty
firing pattern. -/
theorem localizedSumN_four_zero_iff_empty (either : Bool)
    (r : Fin 4 → IsolatedRequests) (x0 : Fin 4) :
    localizedSumN 4 either r x0 43 = 0 ↔
      ∀ x : Fin 4, RingReceiver.exchange either (r x) = false := by
  constructor
  · intro h43
    have h8 : localizedSumN 4 either r x0 8 = 0 := by
      have hle := localizedSumN_eight_le_43 4 either r x0
      omega
    exact (localizedSumN_four_zero8_iff_empty r x0 either).1 h8
  · intro h
    exact localizedSumN_zero_of_empty_firing 4 43 either r x0 h

/-! ## Task G: record bookkeeping and receiver flags -/

def bitInt (b : Bool) : ℤ := if b then 1 else 0

def recordOccInt {n : ℕ} (ports : Fin n → IsolatedPorts) : ℤ :=
  ∑ x, bitInt (ports x).2

def arrivalRecordOcc {n : ℕ} (ports : Fin n → IsolatedPorts) : ℤ :=
  ∑ x, bitInt (RingReceiver.arrivals ports x).2

theorem arrival_record_eq {n : ℕ} (ports : Fin n → IsolatedPorts) :
    arrivalRecordOcc ports = recordOccInt ports := by
  unfold arrivalRecordOcc recordOccInt
  simp only [RingReceiver.arrivals, OpenReferenceFlow.streamShift]
  exact Equiv.sum_comp (finRotate n)
    (fun x => bitInt (ports x).2)

def upTerm (g : Bool) (p : IsolatedPorts) : ℤ :=
  if g = true ∧ p = (true, false) then 1 else 0

def downTerm (g : Bool) (p : IsolatedPorts) : ℤ :=
  if g = true ∧ p = (false, true) then 1 else 0

def deltaTerm (g : Bool) (p : IsolatedPorts) : ℤ :=
  if g then bitInt p.1 - bitInt p.2 else 0

theorem deltaTerm_eq (g : Bool) (p : IsolatedPorts) :
    deltaTerm g p = upTerm g p - downTerm g p := by
  rcases p with ⟨a, b⟩
  cases g <;> cases a <;> cases b <;> norm_num [deltaTerm, upTerm, downTerm, bitInt]

theorem record_step_identity (n : ℕ) (either : Bool) (s : RingReceiver.State n) :
    recordOccInt ((RingReceiver.tick n either s).2.2.2) =
      recordOccInt s.2.2.2 +
        (∑ x, upTerm (RingReceiver.exchange either (s.2.1 x))
          (RingReceiver.arrivals s.2.2.2 x)) -
        (∑ x, downTerm (RingReceiver.exchange either (s.2.1 x))
          (RingReceiver.arrivals s.2.2.2 x)) := by
  have hguard (x : Fin n) :
      bitInt (LocalController.applyGuard
        (fun _ => RingReceiver.exchange either (s.2.1 x))
        (RingReceiver.arrivals s.2.2.2 x)).2 =
      bitInt (RingReceiver.arrivals s.2.2.2 x).2 +
        deltaTerm (RingReceiver.exchange either (s.2.1 x))
          (RingReceiver.arrivals s.2.2.2 x) := by
    rcases RingReceiver.arrivals s.2.2.2 x with ⟨a, b⟩
    cases h : RingReceiver.exchange either (s.2.1 x) <;>
      norm_num [LocalController.applyGuard, deltaTerm, bitInt, h]
  unfold recordOccInt
  simp only [RingReceiver.tick_ports]
  have h1 : (∑ x, bitInt (LocalController.applyGuard
        (fun _ => RingReceiver.exchange either (s.2.1 x))
        (RingReceiver.arrivals s.2.2.2 x)).2) =
      (∑ x, bitInt (RingReceiver.arrivals s.2.2.2 x).2) +
        ∑ x, deltaTerm (RingReceiver.exchange either (s.2.1 x))
          (RingReceiver.arrivals s.2.2.2 x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact hguard x
  rw [h1]
  have h2 : (∑ x, bitInt (RingReceiver.arrivals s.2.2.2 x).2) =
      ∑ x, bitInt (s.2.2.2 x).2 := by
    simpa [arrivalRecordOcc, recordOccInt] using arrival_record_eq s.2.2.2
  rw [h2]
  have h3 : (∑ x, deltaTerm (RingReceiver.exchange either (s.2.1 x))
        (RingReceiver.arrivals s.2.2.2 x)) =
      (∑ x, upTerm (RingReceiver.exchange either (s.2.1 x))
        (RingReceiver.arrivals s.2.2.2 x)) -
      (∑ x, downTerm (RingReceiver.exchange either (s.2.1 x))
        (RingReceiver.arrivals s.2.2.2 x)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact deltaTerm_eq _ _
  rw [h3]
  ring

def flagCountInt {n : ℕ} (either : Bool) (requests : Fin n → IsolatedRequests)
    (ports : Fin n → IsolatedPorts) : ℤ :=
  ∑ x, if RingReceiver.exchange either (requests x) = true ∧
      (RingReceiver.arrivals ports x).1 ≠ (RingReceiver.arrivals ports x).2
    then 1 else 0

theorem flagCountInt_eq (either : Bool) (requests : Fin n → IsolatedRequests)
    (ports : Fin n → IsolatedPorts) :
    flagCountInt either requests ports =
      (∑ x, upTerm (RingReceiver.exchange either (requests x))
        (RingReceiver.arrivals ports x)) +
      (∑ x, downTerm (RingReceiver.exchange either (requests x))
        (RingReceiver.arrivals ports x)) := by
  unfold flagCountInt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rcases RingReceiver.arrivals ports x with ⟨a, b⟩
  cases h : RingReceiver.exchange either (requests x) <;>
    cases a <;> cases b <;> norm_num [upTerm, downTerm, h]

def recordFlagStep {n : ℕ} (either : Bool) (s : RingReceiver.State n) : ℤ :=
  (∑ x, upTerm (RingReceiver.exchange either (s.2.1 x))
    (RingReceiver.arrivals s.2.2.2 x)) +
  (∑ x, downTerm (RingReceiver.exchange either (s.2.1 x))
    (RingReceiver.arrivals s.2.2.2 x))

theorem record_step_abs_le (n : ℕ) (either : Bool) (s : RingReceiver.State n) :
    |recordOccInt ((RingReceiver.tick n either s).2.2.2) -
      recordOccInt s.2.2.2| ≤ recordFlagStep either s := by
  rw [record_step_identity]
  unfold recordFlagStep
  have hu : 0 ≤ ∑ x, upTerm (RingReceiver.exchange either (s.2.1 x))
      (RingReceiver.arrivals s.2.2.2 x) := by
    apply Finset.sum_nonneg
    intro x _
    unfold upTerm
    split <;> norm_num
  have hd : 0 ≤ ∑ x, downTerm (RingReceiver.exchange either (s.2.1 x))
      (RingReceiver.arrivals s.2.2.2 x) := by
    apply Finset.sum_nonneg
    intro x _
    unfold downTerm
    split <;> norm_num
  rw [show recordOccInt s.2.2.2 +
      (∑ x, upTerm (RingReceiver.exchange either (s.2.1 x))
        (RingReceiver.arrivals s.2.2.2 x)) -
      (∑ x, downTerm (RingReceiver.exchange either (s.2.1 x))
        (RingReceiver.arrivals s.2.2.2 x)) - recordOccInt s.2.2.2 =
      (∑ x, upTerm (RingReceiver.exchange either (s.2.1 x))
        (RingReceiver.arrivals s.2.2.2 x)) -
      (∑ x, downTerm (RingReceiver.exchange either (s.2.1 x))
        (RingReceiver.arrivals s.2.2.2 x)) by ring]
  rw [abs_sub_le_iff]
  constructor <;> linarith

def recordFlagSum {n : ℕ} (either : Bool) (s : RingReceiver.State n) (T : ℕ) : ℤ :=
  ∑ k ∈ Finset.range T, recordFlagStep either ((RingReceiver.tick n either)^[k] s)

theorem record_net_le_flagSum (n : ℕ) (either : Bool) (s : RingReceiver.State n)
    (T : ℕ) :
    |recordOccInt (((RingReceiver.tick n either)^[T] s).2.2.2) -
      recordOccInt s.2.2.2| ≤ recordFlagSum either s T := by
  induction T with
  | zero => simp [recordFlagSum]
  | succ T ih =>
    rw [Function.iterate_succ_apply']
    have hstep := record_step_abs_le n either ((RingReceiver.tick n either)^[T] s)
    have htri := abs_sub_le
      (recordOccInt (((RingReceiver.tick n either)^[T] s).2.2.2))
      (recordOccInt s.2.2.2)
      (recordOccInt ((RingReceiver.tick n either
        ((RingReceiver.tick n either)^[T] s)).2.2.2))
    -- use htri in the form current - start ≤ current - previous + previous - start
    have hle : |recordOccInt ((RingReceiver.tick n either
        ((RingReceiver.tick n either)^[T] s)).2.2.2) - recordOccInt s.2.2.2| ≤
        |recordOccInt ((RingReceiver.tick n either
          ((RingReceiver.tick n either)^[T] s)).2.2.2) -
          recordOccInt (((RingReceiver.tick n either)^[T] s).2.2.2)| +
        |recordOccInt (((RingReceiver.tick n either)^[T] s).2.2.2) -
          recordOccInt s.2.2.2| := by
      simpa using (abs_sub_le
        (recordOccInt ((RingReceiver.tick n either
          ((RingReceiver.tick n either)^[T] s)).2.2.2))
        (recordOccInt (((RingReceiver.tick n either)^[T] s).2.2.2))
        (recordOccInt s.2.2.2))
    unfold recordFlagSum
    rw [Finset.sum_range_succ]
    have hsum : |recordOccInt ((RingReceiver.tick n either
        ((RingReceiver.tick n either)^[T] s)).2.2.2) -
        recordOccInt (((RingReceiver.tick n either)^[T] s).2.2.2)| +
        |recordOccInt (((RingReceiver.tick n either)^[T] s).2.2.2) -
          recordOccInt s.2.2.2| ≤
        recordFlagStep either ((RingReceiver.tick n either)^[T] s) +
          ∑ x ∈ Finset.range T, recordFlagStep either ((RingReceiver.tick n either)^[x] s) :=
      add_le_add hstep ih
    rw [add_comm (recordFlagStep either ((RingReceiver.tick n either)^[T] s))] at hsum
    exact le_trans hle hsum

/-! ## Separate ledger columns

The receiver registration count is measured in registrations per 43-tick
period.  The record Toll is measured in WireSchedule bit visits per label.
No certified result in this file puts those two units in one ledger, so they
are exposed as separate columns and are not added.
-/

/-- Uniform control-field receiver registrations per 43-tick period. -/
noncomputable def uniformReceiverColumn (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (fields : ReceiverFields) : ℝ :=
  ∑ t : Fin PMSubstrate.E8Values.Delta, ∑ x : IsolatedSite,
    receiverFlag either ((tick 3 either)^[t.val] (embed c vacuum packet fields)) x

theorem uniformReceiverColumn_eq_zero (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (fields : ReceiverFields) :
    uniformReceiverColumn either c vacuum packet fields = 0 := by
  unfold uniformReceiverColumn
  exact_mod_cast uniform_period_registrations_zero either c vacuum packet fields

/-- Record bit visits per label, a separate column with its own unit. -/
noncomputable def isolatedRecordColumn (reference : Bool) (label : Channels) : ℝ :=
  WireSchedule.writeFlagCount reference label

/-! ## The packet lifts

The certified lifts in `PMKAutomaton.Components` move the packet bank.  They do
not select receiver booking ticks.  `hold_cell_fixed` and `fifo_lift_differs`
identify the two lift actions; no tick set is derived from them.
-/

/-- Hold keeps the packet in cell zero. -/
theorem hold_cell_fixed (R : ℕ) (packet : PacketLabel) :
    (Equiv.refl (Components.PacketBank R)) (Pi.single ((0 : Fin (R + 1)), packet) 1) =
      Pi.single ((0 : Fin (R + 1)), packet) 1 := rfl

/-- The FIFO lift differs from the identity lift on the certified packet bank. -/
theorem fifo_lift_differs :
    Components.fifoEquiv 1 ≠ Equiv.refl (Components.PacketBank 1) := by
  obtain ⟨bank, h⟩ := Components.joint_two_fifo_placements_differ
    (I := Unit) (core := id) () ((Sum.inr (Sum.inr (Sum.inl 1))) : PacketLabel)
  intro he
  apply h
  simp [Components.jointTick, he]

end PMElementaryParticles.IsolatedExcitation
