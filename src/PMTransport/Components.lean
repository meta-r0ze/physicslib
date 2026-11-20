import PMTransport.Values
import PMTransport.BoundaryErasure
import PMTransport.Machine.CarrierReferenceCycle
import PMTransport.Machine.RecordTransport
import PMTransport.Machine.RootMaintenance
import PMTransport.Machine.SubstrateWeylRoots
import PMTransport.Machine.SliceHop
import PMConstants.PacketGaugeActions
import PMConstants.SharedReference

/-!
# Component contracts

The six fields follow the pillar inventory in `COMPONENTS.md`. Each
constructor uses existing certificates for the stated scope. A named
proposition parameter denotes an unresolved contract. Its statement
and witness must come from the user of the constructor. Global pillar
totals supply no per-component witness.

The contracts are separate. There is no default guard, initial state,
wiring, or disposal policy. The packet and the Boolean controller
remain distinct state spaces.
-/

namespace PMTransport.Components

open PMAction
open PMConstants
open scoped Matrix

/-- The phase cycle and quiet trial slots are certified. Timing and
scheduling refer to use of this clock by the physical operations. -/
structure Clock (frameMargin clockTariff physicalTiming : Prop) where
  capacity : Delta = 43
  margin : frameMargin
  map : ∀ t : Fin Delta, (finRotate Delta)^[Delta] t = t
  protocol : ∀ (requests : Bool × Bool) (z : SubstrateReflection.Lattice) (n : ℕ),
    2 ≤ n → n < Delta →
      ((ClockedRootTrials.tick^[n + 1]) (requests, (z, 0))).2.1 =
        ((ClockedRootTrials.tick^[n]) (requests, (z, 0))).2.1
  toll : clockTariff
  governor : physicalTiming

theorem clock {frameMargin clockTariff physicalTiming : Prop}
    (margin : frameMargin) (toll : clockTariff) (timing : physicalTiming) :
    Clock frameMargin clockTariff physicalTiming where
  capacity := Values.Delta_eq
  margin := margin
  map := CarrierReferenceCycle.clock_closes
  protocol requests z _ ha hb := ClockedRootTrials.quiet_trial_tick requests z ha hb
  toll := toll
  governor := timing

/-- The two-site port count and the generic two-bank occupation laws
concern their respective encodings. Accessible occupancies are open. -/
structure NodeRegisters (a b : Type*) [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (accessibleOccupancy registerTariff portEnabling : Prop) where
  capacity : Fintype.card (TwoSiteHandoff.Site × ActualRootRepair.Ports) = 8
  margin : accessibleOccupancy
  map : ∀ (e : Equiv.Perm (a × b)) (q : IndependentRegisters.Configuration a b),
    IndependentRegisters.occupied (RegisterControl.extend e q) = IndependentRegisters.occupied q
  protocol : ∀ p : a × b, IndependentRegisters.occupied (IndependentRegisters.encode p) = 2
  toll : registerTariff
  governor : portEnabling

theorem nodeRegisters (a b : Type*) [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {accessibleOccupancy registerTariff portEnabling : Prop}
    (occupancy : accessibleOccupancy) (toll : registerTariff) (enable : portEnabling) :
    NodeRegisters a b accessibleOccupancy registerTariff portEnabling where
  capacity := TwoSiteHandoff.port_count
  margin := occupancy
  map := RegisterControl.occupation_conserved
  protocol := IndependentRegisters.occupied_encode
  toll := toll
  governor := enable

open LocalController in
/-- The finite table concerns retained Boolean rows. Its count supplies
neither their starting support nor a physical guard. -/
structure Controller (requestSupport controlTariff jointGuard : Prop) where
  capacity : Fintype.card EnumeratedRule = 8 ^ (4 * 43)
  margin : requestSupport
  map : ∀ rule : Rule, Function.Bijective (rawTick rule) ↔
    ∀ phase requests, Compatible (rule phase requests)
  protocol : ∀ (rule : Rule) (phase : Phase) (s t : Registers) (x : ℤ),
    s.1 x = t.1 x → (s.2 (x - 1)).1 = (t.2 (x - 1)).1 →
      (s.2 (x + 1)).2 = (t.2 (x + 1)).2 →
      (rawStep rule phase s).1 x = (rawStep rule phase t).1 x ∧
        (rawStep rule phase s).2 x = (rawStep rule phase t).2 x
  toll : controlTariff
  governor : jointGuard

theorem controller {requestSupport controlTariff jointGuard : Prop}
    (support : requestSupport) (toll : controlTariff) (guard : jointGuard) :
    Controller requestSupport controlTariff jointGuard where
  capacity := LocalController.enumerated_rule_count
  margin := support
  map := LocalController.reversible_iff_rows
  protocol := LocalController.radius_one
  toll := toll
  governor := guard

/-- A root word has an exact unitary map and a comparison implementation.
The uniform primitive test leaves other prices and firing open. -/
structure RootPulses (n : Type*) [Fintype n] [DecidableEq n]
    (wordTariff pulseGuard : Prop) where
  capacity : ∀ c, (CarrierEvents.active c).card = 4
  margin : ∀ p : ℝ, 0 < p → p < 1 / 2 → 0 < RootTransferPhase.quarterTime p
  map : ∀ (e : Equiv.Perm n), Function.Involutive e → ∀ p t : ℝ,
    RootTransferPhase.phase e p t ∈ unitary (Matrix n n ℂ)
  protocol : ∀ U : Matrix n n ℂ,
    (BranchPulseContract.program.map (BranchPulseContract.decode U)).prod =
      CoherentComparisonRepair.compare U
  toll : (∀ c, PMSubstrate.NetCost.prob (CarrierEvents.active c) = 1 / 2) ∧ wordTariff
  governor : pulseGuard

theorem rootPulses (n : Type*) [Fintype n] [DecidableEq n] {wordTariff pulseGuard : Prop}
    (toll : wordTariff) (guard : pulseGuard) : RootPulses n wordTariff pulseGuard where
  capacity := CarrierEvents.active_card
  margin := RootTransferPhase.quarterTime_positive
  map := RootTransferPhase.phase_unitary
  protocol := BranchPulseContract.program_correct
  toll := ⟨CarrierEvents.uniform_activation, toll⟩
  governor := guard

/-- The closed-pair return and the mixed flag refer to different certified
tests. The flag tariff and receiver guard remain explicit inputs. -/
structure Receiver (acceptanceMargin bookedComparison receiverGuard : Prop) where
  capacity : Fintype.card (TwoSiteHandoff.Site × ActualRootRepair.Ports) = 8
  margin : acceptanceMargin
  map : ∀ s : TwoSiteHandoff.State Bool, (TwoSiteHandoff.step true)^[4] s = s
  protocol : ∀ (rule : LocalController.Rule) (phase : LocalController.Phase)
    (s : LocalController.Registers) (x : ℤ) (edge : TwoSiteHandoff.State Bool),
    edge 1 = OpenReferenceFlow.streamShift OpenReferenceFlow.line s.2 x →
    (LocalController.rawStep rule phase s).2 x =
      TwoSiteHandoff.step (rule phase (s.1 x).1 (edge 1)) edge 0
  toll : (RingReceiver.receiverFlag false RingReceiver.mixedBasisRing 0 = 0 ∧
    RingReceiver.receiverFlag true RingReceiver.mixedBasisRing 0 = 1) ∧ bookedComparison
  governor : receiverGuard

theorem receiver {acceptanceMargin bookedComparison receiverGuard : Prop}
    (margin : acceptanceMargin) (booked : bookedComparison) (guard : receiverGuard) :
    Receiver acceptanceMargin bookedComparison receiverGuard where
  capacity := TwoSiteHandoff.port_count
  margin := margin
  map := TwoSiteHandoff.exchange_four_returns
  protocol := LocalController.receiver_realisation
  toll := ⟨RingReceiver.mixed_ring_flags, booked⟩
  governor := guard

/-- A line step and a two-stream current law. Available physical edges,
successive crossing conditions and registration are supplied. -/
structure Links (linkCapacity successorMargin crossingTariff admittedCrossings : Prop) where
  capacity : linkCapacity
  margin : successorMargin
  map : ∀ j : ℤ,
    OpenHandoff.address (j + 1) - OpenHandoff.address j = AxisHop.vec OpenHandoff.direction
  protocol : ∀ s : OpenHandoff.State Bool,
    (OpenReferenceFlow.streamShift OpenReferenceFlow.line
      (OpenReferenceFlow.streamShift OpenReferenceFlow.line s) (-1)).2 = (s 1).2
  toll : (∀ w nL nR : ℝ, PMConstants.HandoffAdmittance.leftOutflow w nL nR - nL =
    w * (nR - nL)) ∧ crossingTariff
  governor : admittedCrossings

theorem links {linkCapacity successorMargin crossingTariff admittedCrossings : Prop}
    (capacity : linkCapacity) (margin : successorMargin) (toll : crossingTariff)
    (admission : admittedCrossings) :
    Links linkCapacity successorMargin crossingTariff admittedCrossings where
  capacity := capacity
  margin := margin
  map := OpenHandoff.address_step
  protocol := OpenReferenceFlow.bypass_transmits
  toll := ⟨PMConstants.HandoffAdmittance.node_current, toll⟩
  governor := admission

/-- Wall size, packet slots, reflection and address. The carrier background
and admitted operations are inputs. -/
structure Payload (occupiedPacket packetTariff wallAdmission : Prop) where
  capacity : (∀ c, Fintype.card (CarrierEvents.Carrier c) = 8) ∧
    Function.Bijective PacketGaugeActions.channelIndex
  margin : occupiedPacket
  map : ∀ c, Function.Involutive (CarrierEvents.reflect c)
  protocol : ∀ (g : Fin 3) (b : Bool), ∃! c : Fin 3, g ≠ c ∧ GenerationWalls.side g c = b
  toll : packetTariff
  governor : wallAdmission

theorem payload {occupiedPacket packetTariff wallAdmission : Prop}
    (occupancy : occupiedPacket) (toll : packetTariff) (admission : wallAdmission) :
    Payload occupiedPacket packetTariff wallAdmission where
  capacity := ⟨CarrierEvents.carrier_card, PacketGaugeActions.channel_index_bijective⟩
  margin := occupancy
  map := CarrierEvents.reflection_involutive
  protocol := GenerationWalls.one_class_per_wall
  toll := toll
  governor := admission

/-- The reserved-cell layout and the supplied open restoration trace.
Ready supply and preparation prices are open at the physical visits. -/
structure Reference (supplyMargin preparationTariff renewal : Prop) where
  capacity : ∀ R : Finset (Fin 172), R.Nonempty →
    (∀ S : Finset (Fin 172), S.Nonempty → (Finset.univ \ S).card ≤ (Finset.univ \ R).card) →
    R.card = 1
  margin : CommonResponse.nsq OddReferenceSource.oddReference = 1 ∧ supplyMargin
  map : ∀ L : SharedReference.ReferenceLayout, L.refOf 0 = L.refOf 1
  protocol : ∀ (s : OpenHandoff.State Bool) (accepts : Bool → Prop) (N : ℕ),
    (∀ j : Fin N, accepts (OpenHandoff.run s (j.val + 1) 0).1) ↔
      (∀ j : Fin N, accepts (s (j.val + 1 : ℤ)).2)
  toll : preparationTariff
  governor : renewal

theorem reference {supplyMargin preparationTariff renewal : Prop}
    (margin : supplyMargin) (toll : preparationTariff) (supply : renewal) :
    Reference supplyMargin preparationTariff renewal where
  capacity := SharedReference.reserved_single
  margin := ⟨OddReferenceSource.odd_reference_population, margin⟩
  map := SharedReference.shared
  protocol := OpenHandoff.acceptance_iff_supply
  toll := toll
  governor := supply

/-- The diagonal readout on a supplied state and comparison word.
The detector attachment and bookings remain explicit. -/
structure Readout (n : Type*) [Fintype n] [DecidableEq n]
    (detectorSupport flagBooking detectorWiring : Prop) where
  capacity : detectorSupport
  margin : ∀ x : ℝ, 0 ≤ DiagonalReadout.flag x ∧ DiagonalReadout.flag x ≤ 1
  map : ∀ {H : Matrix n n ℂ} (hH : H.IsHermitian) (q : n → ℝ),
    H = Matrix.diagonal (fun i => (q i : ℂ)) → ∀ (t : ℝ) (φ : n → ℂ),
    CommonResponse.stateFlag (LinkSpectralResponse.HermitianTransport.transport hH t) φ =
      ∑ c, Complex.normSq (φ c) * DiagonalReadout.flag (t * q c)
  protocol : ∀ U : Matrix n n ℂ,
    (BranchPulseContract.program.map (BranchPulseContract.decode U)).prod =
      CoherentComparisonRepair.compare U
  toll : (∀ T : ℝ, TollAmplitude.wireAmplitude T ^ 2 = TollAmplitude.wireWeight T) ∧
    flagBooking
  governor : detectorWiring

theorem readout (n : Type*) [Fintype n] [DecidableEq n]
    {detectorSupport flagBooking detectorWiring : Prop}
    (support : detectorSupport) (booked : flagBooking) (wiring : detectorWiring) :
    Readout n detectorSupport flagBooking detectorWiring where
  capacity := support
  margin := DiagonalReadout.flag_bounds
  map := DiagonalReadout.state_flag
  protocol := BranchPulseContract.program_correct
  toll := ⟨TollAmplitude.wireAmplitude_sq, booked⟩
  governor := wiring

/-- Retained memory and open export. The bound is for an injective
linear reset of the given window. -/
structure Records (n : Type*) [Fintype n] [DecidableEq n] (V A : Type*) [AddCommMonoid A]
    (readyRecords recordTariff consumerPort : Prop) where
  capacity : ∀ (N R : ℕ)
    (T : ((Fin N → n → ℂ) × (Fin R → n → ℂ)) →ₗ[ℂ]
      ((Fin N → n → ℂ) × (Fin R → n → ℂ))),
    Function.Injective T → (∀ inputs, (T (inputs, 0)).1 = 0) →
      N * Fintype.card n ≤ R * Fintype.card n
  margin : readyRecords
  map : ∀ inputs records : List V,
    (RecordTransport.run inputs records).1 ++ (RecordTransport.run inputs records).2 =
      records ++ inputs
  protocol : ∀ (s : OpenHandoff.State V) (N : ℕ) (measure : V → A),
    (∑ d : Fin N, measure (OpenHandoff.run s N (-(d.val : ℤ))).2) =
      ∑ j : Fin N, measure (s (-(j.val + 1 : ℤ))).1
  toll : recordTariff
  governor : consumerPort

theorem records (n : Type*) [Fintype n] [DecidableEq n] (V A : Type*) [AddCommMonoid A]
    {readyRecords recordTariff consumerPort : Prop}
    (ready : readyRecords) (toll : recordTariff) (port : consumerPort) :
    Records n V A readyRecords recordTariff consumerPort where
  capacity := RecordTransport.history_memory_bound
  margin := ready
  map := RecordTransport.stream_conserved
  protocol := OpenHandoff.sum_exported
  toll := toll
  governor := port

/-- Erasure merges exported bits while the retained identity remains
bijective. The boundary contract supplies the booked export, disposition
and return wiring. -/
structure Boundary (I : Type*) (boundaryCapacity exportDisposition : Prop) where
  capacity : Fintype.card BoundaryErasure.Disposition = 3
  margin : boundaryCapacity
  map : ∀ (update : Equiv.Perm I) (exported : I → Option Bool)
    (disposition : I → BoundaryErasure.Disposition),
    Function.Bijective (fun i => (BoundaryErasure.step update i (exported i) (disposition i)).1)
  protocol : ∀ a b : Bool, BoundaryErasure.deliver .erase a = BoundaryErasure.deliver .erase b
  toll : ∀ bit : Bool, BoundaryErasure.erasedBits .erase (some bit) = 1
  governor : exportDisposition

theorem boundary (I : Type*) {boundaryCapacity exportDisposition : Prop}
    (capacity : boundaryCapacity) (disposition : exportDisposition) :
    Boundary I boundaryCapacity exportDisposition where
  capacity := BoundaryErasure.disposition_count
  margin := capacity
  map := BoundaryErasure.identity_bijective
  protocol := BoundaryErasure.erased_bit_merges
  toll := BoundaryErasure.erasing_pays_one
  governor := disposition

/-- Root implementation and minimum cost for supplied jobs. The physical
job set, reserve, prices and arbitration are inputs. -/
structure Maintenance (R : Type*) [DecidableEq R]
    (jobCapacity jobReserve maintenanceTariff arbitration : Prop) where
  capacity : jobCapacity
  margin : jobReserve
  map : ∀ (c : Fin 3) (jr : R → Fin 4) (v : R → CarrierEvents.Carrier c),
    (∀ r, CarrierWeyl.simple c (jr r) (v r) ≠ v r) → ∀ r (s : ReferenceMaintenance.State R),
    RootMaintenance.encodeState c jr v (ReferenceMaintenance.event r s) =
      RootMaintenance.siteEvent c jr r (RootMaintenance.encodeState c jr v s)
  protocol : ∀ (w : R → ℝ), (∀ r, 0 ≤ w r) → ∀ req : Finset R,
    IsLeast {c | ∃ L, RefreshSchedule.admissible req L ∧ RefreshSchedule.cost w L = c}
      (∑ r ∈ req, w r)
  toll : maintenanceTariff
  governor : arbitration

theorem maintenance (R : Type*) [DecidableEq R]
    {jobCapacity jobReserve maintenanceTariff arbitration : Prop}
    (capacity : jobCapacity) (margin : jobReserve) (toll : maintenanceTariff) (arbiter : arbitration) :
    Maintenance R jobCapacity jobReserve maintenanceTariff arbitration where
  capacity := capacity
  margin := margin
  map := RootMaintenance.event_is_root
  protocol := RefreshSchedule.minimal_is_ledger
  toll := toll
  governor := arbiter

/-- Upstream contracts at the EP consumer boundary. The wiring premise
asks what the endpoint reads: routed value and destination, retained
record, or executed comparison with its booked flag. It supplies no
choice between them. -/
structure EPEndpoint (writerPopulation consumerWiring paidRemainder insertionAdmission : Prop) where
  capacity : Function.Bijective PacketGaugeActions.channelIndex
  margin : writerPopulation
  map : ∀ (g : Fin 3) (b : Bool), ∃! c : Fin 3, g ≠ c ∧ GenerationWalls.side g c = b
  protocol : consumerWiring
  toll : (∀ full probeVacancy : Bool,
    Values.outputFlagThreshold full probeVacancy =
      if full then (if probeVacancy then 1 / 2 else 9 / 16) else 3 / 5) ∧
    (∀ full probeVacancy : Bool,
      Values.balancedResetThreshold full probeVacancy =
        if full then (if probeVacancy then 3 / 4 else 27 / 32) else 9 / 10) ∧ paidRemainder
  governor : insertionAdmission

theorem epEndpoint {writerPopulation consumerWiring paidRemainder insertionAdmission : Prop}
    (population : writerPopulation) (wiring : consumerWiring)
    (toll : paidRemainder) (admission : insertionAdmission) :
    EPEndpoint writerPopulation consumerWiring paidRemainder insertionAdmission where
  capacity := PacketGaugeActions.channel_index_bijective
  margin := population
  map := GenerationWalls.one_class_per_wall
  protocol := wiring
  toll := ⟨Values.outputFlagThreshold_eq, Values.balancedResetThreshold_eq, toll⟩
  governor := admission

/-! ## Rates of the certified encodings

A load counts an enabled slot of one Boolean event. A bound on an
encoded slot or port is per instance. It is independent of how many
instances operate together and of the physical duration of a tick.
-/

def phaseLoad (fires : Fin Delta → Bool) : ℕ :=
  (Finset.univ.filter fun t => fires t = true).card

theorem phaseLoad_le_period (fires : Fin Delta → Bool) : phaseLoad fires ≤ 43 := by
  simpa [phaseLoad] using Finset.card_filter_le (s := (Finset.univ : Finset (Fin Delta)))
    (p := fun t => fires t = true)

theorem phaseLoad_full : phaseLoad (fun _ => true) = 43 := by
  simp [phaseLoad]

theorem trial_phaseLoad (requests : Bool × Bool) :
    phaseLoad (ClockedRootTrials.fire requests) = requests.1.toNat + requests.2.toNat := by
  rcases requests with ⟨a, b⟩
  cases a <;> cases b <;> decide +kernel

theorem trial_phaseLoad_le (requests : Bool × Bool) :
    phaseLoad (ClockedRootTrials.fire requests) ≤ 2 := by
  rcases requests with ⟨a, b⟩
  cases a <;> cases b <;> simp [trial_phaseLoad, Bool.toNat]

theorem line_receiver_phaseLoad_le (rule : LocalController.Rule)
    (s : Fin Delta → LocalController.Registers) (x : ℤ) :
    phaseLoad (fun t => rule t ((s t).1 x).1
      (OpenReferenceFlow.streamShift OpenReferenceFlow.line (s t).2 x)) ≤ 43 :=
  phaseLoad_le_period _

theorem ring_receiver_phaseLoad (either : Bool) (requests : LocalController.Requests) :
    phaseLoad (fun _ => RingReceiver.exchange either requests) =
      if RingReceiver.exchange either requests then 43 else 0 := by
  cases RingReceiver.exchange either requests <;> simp [phaseLoad]

theorem ring_source_neighbour {n : ℕ} (switches : Fin n → Bool) (p : RingReceiver.Slot n) :
    (RingReceiver.portSource switches p).1 = finRotate n p.1 ∨
      (RingReceiver.portSource switches p).1 = (finRotate n).symm p.1 := by
  cases a : p.2 <;> cases b : switches p.1 <;> simp [RingReceiver.portSource, a, b]

theorem fifo_tick_ports (R : ℕ) (input : PacketGaugeActions.Channels → ℂ)
    (records : Fin R → PacketGaugeActions.Channels → ℂ) :
    (∀ a, RecordTransport.tick R
      (fun p => (@Fin.cons R (fun _ => PacketGaugeActions.Channels → ℂ) input records p.1) p.2) (0, a) = (@Fin.snoc R (fun _ => PacketGaugeActions.Channels → ℂ) records input 0) a) ∧
    (∀ a, RecordTransport.tick R
      (fun p => (@Fin.cons R (fun _ => PacketGaugeActions.Channels → ℂ) input records p.1) p.2) (Fin.last R, a) = input a) := by
  exact ⟨RecordTransport.tick_fifo R input records 0,
    fun a => by simpa using RecordTransport.tick_fifo R input records (Fin.last R) a⟩

theorem ring_flag_le_one {n : ℕ} (either : Bool) (s : RingReceiver.State n) (x : Fin n) :
    RingReceiver.receiverFlag either s x ≤ 1 := by
  rw [RingReceiver.receiver_flag_eq]
  split <;> norm_num

theorem erased_bits_le_one (disposition : BoundaryErasure.Disposition) (exported : Option Bool) :
    BoundaryErasure.erasedBits disposition exported ≤ 1 := by
  unfold BoundaryErasure.erasedBits
  split <;> omega

theorem cycle_erased_le_period (disposition : Fin Delta → BoundaryErasure.Disposition)
    (exported : Fin Delta → Option Bool) :
    BoundaryErasure.cycleErased disposition exported ≤ 43 := by
  unfold BoundaryErasure.cycleErased
  calc
    _ ≤ ∑ _ : Fin Delta, (1 : ℕ) :=
      Finset.sum_le_sum (fun t _ => erased_bits_le_one (disposition t) (exported t))
    _ = 43 := by simp

/-! ## Headroom in matching units -/

/-- Empty slots of the isolated trial clock. The all-true requests attain
the worst-case load. These slots are not reserved for concurrent work. -/
theorem trial_slot_margin (requests : Bool × Bool) :
    41 ≤ 43 - phaseLoad (ClockedRootTrials.fire requests) := by
  have := trial_phaseLoad_le requests
  omega

theorem trial_slot_margin_attained :
    43 - phaseLoad (ClockedRootTrials.fire (true, true)) = 41 := by
  rw [trial_phaseLoad]
  rfl

/-- One receiver opportunity at every phase can be used, under either
guard, on the all-true request pair. -/
theorem ring_exchange_full_load (either : Bool) :
    43 - phaseLoad (fun _ => RingReceiver.exchange either (true, true)) = 0 := by
  rw [ring_receiver_phaseLoad]
  cases either <;> rfl

theorem ring_flag_margin_attained :
    1 - RingReceiver.receiverFlag true RingReceiver.mixedBasisRing 0 = 0 := by
  rw [RingReceiver.mixed_ring_flags.2]
  norm_num

/-- The binary port can exhaust its accounting capacity if every input
is booked for erasure. This is an attainable model load. -/
theorem erasure_margin_attained (bits : Fin Delta → Bool) :
    43 - BoundaryErasure.cycleErased (fun _ => .erase) (fun t => some (bits t)) = 0 := by
  rw [BoundaryErasure.erase_full_cycle, Delta_eq]
  rfl

/-! ## Reversible lifts of the retained controller

Cell zero holds the incoming 16-slot packet. The other cells hold the
retained FIFO packets. The fibre map is a supplied operation, with no
default timing or attachment to a receiver guard.
-/

abbrev PacketBank (R : ℕ) := Fin (R + 1) × PacketGaugeActions.Channels → ℂ

def fifoEquiv (R : ℕ) : Equiv.Perm (PacketBank R) where
  toFun f p := f (RecordTransport.shift R p)
  invFun f p := f ((RecordTransport.shift R).symm p)
  left_inv f := by ext p; simp
  right_inv f := by ext p; simp

theorem fifoEquiv_eq_tick (R : ℕ) (bank : PacketBank R) :
    fifoEquiv R bank = RecordTransport.tick R bank := by
  funext p
  rcases p with ⟨i, a⟩
  exact (RecordTransport.tick_apply R bank i a).symm

def jointTick {I : Type*} {R : ℕ} (core : I → I)
    (packet : I → Equiv.Perm (PacketBank R)) (s : I × PacketBank R) : I × PacketBank R :=
  (core s.1, packet s.1 s.2)

theorem joint_core_iterate {I : Type*} {R : ℕ} (core : I → I)
    (packet : I → Equiv.Perm (PacketBank R)) (s : I × PacketBank R) (n : ℕ) :
    ((jointTick core packet)^[n] s).1 = core^[n] s.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact congrArg core ih

theorem joint_bijective_iff {I : Type*} {R : ℕ} (core : I → I)
    (packet : I → Equiv.Perm (PacketBank R)) :
    Function.Bijective (jointTick core packet) ↔ Function.Bijective core := by
  constructor
  · intro hj
    constructor
    · intro x y h
      exact congrArg Prod.fst (hj.1 (a₁ := (x, (packet x).symm 0))
        (a₂ := (y, (packet y).symm 0)) (by simp [jointTick, h]))
    · intro y
      obtain ⟨s, hs⟩ := hj.2 (y, 0)
      exact ⟨s.1, congrArg Prod.fst hs⟩
  · intro h
    let e := Equiv.ofBijective core h
    exact ((Equiv.prodCongrRight packet).trans (e.prodCongr (Equiv.refl _))).bijective

/-- Every bijective step over a fixed reversible core has exactly one
packet-bank permutation at each core input. This is a classification
of the lifts, before adding any physical locality or firing contract. -/
theorem joint_lift_iff {I : Type*} {R : ℕ} (core : Equiv.Perm I)
    (tick : I × PacketBank R → I × PacketBank R)
    (hc : ∀ s, (tick s).1 = core s.1) :
    Function.Bijective tick ↔ ∃! packet, tick = jointTick core packet := by
  constructor
  · intro ht
    have hf (x : I) : Function.Bijective (fun bank => (tick (x, bank)).2) := by
      constructor
      · intro a b h
        exact congrArg Prod.snd (ht.1 (Prod.ext
          ((hc (x, a)).trans (hc (x, b)).symm) h))
      · intro out
        obtain ⟨⟨y, bank⟩, hy⟩ := ht.2 (core x, out)
        have hyx : y = x := core.injective ((hc (y, bank)).symm.trans (congrArg Prod.fst hy))
        subst y
        exact ⟨bank, congrArg Prod.snd hy⟩
    let packet (x : I) : Equiv.Perm (PacketBank R) := Equiv.ofBijective _ (hf x)
    have heq : tick = jointTick core packet :=
      funext fun s => Prod.ext (hc s) rfl
    refine ⟨packet, heq, ?_⟩
    intro other ho
    funext x
    apply Equiv.ext
    intro bank
    have h := congrFun (ho.symm.trans heq) (x, bank)
    exact congrArg Prod.snd h
  · rintro ⟨packet, rfl, _⟩
    exact (joint_bijective_iff _ _).2 core.bijective

theorem joint_line_bijective_iff {R : ℕ} (rule : LocalController.Rule)
    (packet : LocalController.State → Equiv.Perm (PacketBank R)) :
    Function.Bijective (jointTick (LocalController.rawTick rule) packet) ↔
      ∀ phase requests, LocalController.Compatible (rule phase requests) :=
  (joint_bijective_iff _ _).trans (LocalController.reversible_iff_rows rule)

theorem joint_ring_bijective {n R : ℕ} (either : Bool)
    (packet : RingReceiver.State n → Equiv.Perm (PacketBank R)) :
    Function.Bijective (jointTick (RingReceiver.tick n either) packet) :=
  (joint_bijective_iff _ _).mpr (RingReceiver.tick_bijective n either)

theorem joint_fifo_restriction {I : Type*} (R : ℕ) (core : I → I)
    (s : I × PacketBank R) :
    (jointTick core (fun _ => fifoEquiv R) s).2 = RecordTransport.tick R s.2 :=
  fifoEquiv_eq_tick R s.2

/-- Two stipulated factor projections would force the independent
product. The core projection alone implies no packet projection. -/
theorem joint_fixed_projections {I : Type*} {R : ℕ} (core : I → I)
    (packet : PacketBank R → PacketBank R)
    (tick : I × PacketBank R → I × PacketBank R)
    (hc : ∀ s, (tick s).1 = core s.1) (hp : ∀ s, (tick s).2 = packet s.2) :
    tick = Prod.map core packet := by
  funext s
  exact Prod.ext (hc s) (hp s)

theorem joint_two_fifo_placements_differ {I : Type*} (core : I → I)
    (x : I) (a : PacketGaugeActions.Channels) :
    ∃ bank : PacketBank 1,
      (jointTick core (fun _ => fifoEquiv 1) (x, bank)).2 (0, a) ≠
      (jointTick core (fun _ => Equiv.refl _) (x, bank)).2 (0, a) := by
  refine ⟨fun p => if p.1 = 0 then 0 else 1, ?_⟩
  change (if finRotate 2 (0 : Fin 2) = 0 then (0 : ℂ) else 1) ≠
    (if (0 : Fin 2) = 0 then (0 : ℂ) else 1)
  simp

theorem joint_boundary_identity {I : Type*} {R : ℕ} (core : Equiv.Perm I)
    (packet : I → Equiv.Perm (PacketBank R))
    (exported : I × PacketBank R → Option Bool)
    (disposition : I × PacketBank R → BoundaryErasure.Disposition) :
    Function.Bijective (fun s =>
      (BoundaryErasure.step
        ((Equiv.prodCongrRight packet).trans (core.prodCongr (Equiv.refl _)))
        s (exported s) (disposition s)).1) :=
  BoundaryErasure.identity_bijective _ exported disposition

/-! ## Local observations of a certified receiver -/

theorem ring_observations_local {n : ℕ} (either : Bool)
    (s t : RingReceiver.State n) (x : Fin n)
    (hq : s.2.1 x = t.2.1 x)
    (hl : (s.2.2.2 ((finRotate n).symm x)).1 = (t.2.2.2 ((finRotate n).symm x)).1)
    (hr : (s.2.2.2 (finRotate n x)).2 = (t.2.2.2 (finRotate n x)).2) :
    (RingReceiver.tick n either s).2.2.2 x = (RingReceiver.tick n either t).2.2.2 x ∧
      RingReceiver.receiverFlag either s x = RingReceiver.receiverFlag either t x := by
  have ha : RingReceiver.arrivals s.2.2.2 x = RingReceiver.arrivals t.2.2.2 x :=
    Prod.ext hl hr
  constructor
  · rw [RingReceiver.tick_ports, RingReceiver.tick_ports, hq, ha]
  · rw [RingReceiver.receiver_flag_eq, RingReceiver.receiver_flag_eq, hq, ha]

/-! ## Accounting for supplied registrations and exported erasures -/

/-- Partition the booked unit registrations by their supplied owner.
The erased bits are additional booked erasure events on this trace.
A read and a later erasure are separate operations. This equality
does not identify which visits physically register. -/
theorem booked_toll_sum {Ω C : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype C] [DecidableEq C] {k : ℕ} (owner : Fin k → C) (events : Fin k → Finset Ω)
    (disposition : Fin Delta → BoundaryErasure.Disposition) (exported : Fin Delta → Option Bool) :
    (∑ c : C, ∑ i ∈ Finset.univ.filter (fun i => owner i = c),
      PMSubstrate.NetCost.prob (events i)) +
      (BoundaryErasure.cycleErased disposition exported : ℝ) =
    PMSubstrate.NetCost.expectedCost 1 events +
      (BoundaryErasure.cycleErased disposition exported : ℝ) := by
  rw [PMSubstrate.NetCost.expected_count_linear, one_mul, Finset.sum_fiberwise]

/-- The tagged open symmetry lifts if the two rules use the same
packet-bank action on the common core trace. -/
theorem joint_tagged_ticks_equal {R : ℕ}
    (packet : LocalController.State → Equiv.Perm (PacketBank R))
    (s : LocalController.State × PacketBank R) (hs : LocalController.CentreTagged s.1)
    (n : ℕ) :
    ((jointTick (LocalController.rawTick LocalController.exchangeOnBoth) packet)^[n] s) =
      ((jointTick (LocalController.rawTick LocalController.exchangeOnEither) packet)^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · rw [joint_core_iterate, joint_core_iterate]
      exact LocalController.tagged_ticks_equal s.1 hs (n + 1)
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl

/-! ## Weyl stabilizers in a marked D₄ sector

The signed frame is recorded in lookup order. Its action is on integer
sector coordinates. The other sector and the scalar clock phase are
separate from the active edge. Reflections are the eight certified
embedded simple roots, four per sector.
-/

namespace NodeSymmetry

set_option maxRecDepth 16000

open Finset

abbrev Frame := (Fin 4 → Fin 4) × (Fin 4 → Bool)

def d4 (f : Frame) : Prop :=
  Function.Injective f.1 ∧ (univ.filter fun i => f.2 i = true).card % 2 = 0

instance (f : Frame) : Decidable (d4 f) := inferInstanceAs (Decidable (_ ∧ _))

def act (f : Frame) (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => if f.2 i then -v (f.1 i) else v (f.1 i)

def identity : Frame := (id, fun _ => false)

def comp (f g : Frame) : Frame :=
  (g.1 ∘ f.1, fun i => Bool.xor (f.2 i) (g.2 (f.1 i)))

theorem act_comp (f g : Frame) (v : Fin 4 → ℤ) :
    act (comp f g) v = act f (act g v) := by
  funext i
  unfold act comp
  cases hf : f.2 i <;> cases hg : g.2 (f.1 i) <;> simp [hf, hg]

def simpleFrame : Fin 4 → Frame := ![
  (Equiv.swap 0 1, fun _ => false),
  (Equiv.swap 1 2, fun _ => false),
  (Equiv.swap 2 3, fun _ => false),
  (Equiv.swap 2 3, fun i => i = 2 || i = 3)]

theorem simpleFrame_root (j : Fin 4) (v : Fin 4 → ℤ) :
    act (simpleFrame j) v =
      PMSubstrate.ChannelSymmetry.refl (PMSubstrate.ChannelSymmetry.simple j) v := by
  funext i
  fin_cases j <;> fin_cases i <;>
    norm_num [act, simpleFrame, PMSubstrate.ChannelSymmetry.refl,
      PMSubstrate.ChannelSymmetry.simple, PMSubstrate.ChannelSymmetry.dot4,
      Fin.sum_univ_four, Equiv.swap_apply_def]

theorem simpleFrame_carrier (c : Fin 3) (j : Fin 4) (v : CarrierEvents.Carrier c) :
    CarrierEvents.vector (CarrierWeyl.simple c j v) = act (simpleFrame j) (CarrierEvents.vector v) :=
  (CarrierWeyl.simple_is_root c j v).trans (simpleFrame_root _ _).symm

theorem simpleFrame_substrate (s t : Bool) (j : Fin 4) (w : SubstrateWeylRoots.Lattice) :
    SubstrateWeylRoots.sector t (SubstrateWeylRoots.coordinates s j w) =
      if t = s then act (simpleFrame j) (SubstrateWeylRoots.sector t w)
      else SubstrateWeylRoots.sector t w := by
  rw [simpleFrame_root]
  exact SubstrateWeylRoots.sector_intertwines s t j w

/-- The line fixes the positive root. The axis hop fixes the positive
axis. The slice also fixes the oriented clock normal. -/
inductive Link
  | sector
  | line
  | axis
  | slice

def preserves : Link → Frame → Prop
  | .sector, _ => True
  | .line, f => act f (AxisHop.vec OpenHandoff.direction) = AxisHop.vec OpenHandoff.direction
  | .axis, f => act f (AxisHop.axis 0) = AxisHop.axis 0
  | .slice, f => act f (AxisHop.axis 0) = AxisHop.axis 0 ∧ act f (AxisHop.axis 3) = AxisHop.axis 3

instance (l : Link) (f : Frame) : Decidable (preserves l f) := by
  cases l <;> unfold preserves <;> infer_instance

def stabilizer (l : Link) : Finset Frame :=
  univ.filter fun f => d4 f ∧ preserves l f

/-- Finite enumeration in the marked active D₄ factor. -/
theorem stabilizer_orders :
    (stabilizer .sector).card = 192 ∧ (stabilizer .line).card = 8 ∧
      (stabilizer .axis).card = 24 ∧ (stabilizer .slice).card = 4 := by
  decide +kernel

def wordFrame : List (Fin 4) → Frame
  | [] => identity
  | j :: w => comp (simpleFrame j) (wordFrame w)

def generatorWords : Link → List (List (Fin 4))
  | .sector => [[0], [1], [2], [3]]
  | .line => [[0], [2], [3]]
  | .axis => [[1], [2], [3]]
  | .slice => [[1], [2, 1, 2, 3, 1, 2]]

/-- Enumeration of products of the proposed generators up to a depth. -/
def products (gs : Finset Frame) : ℕ → Finset Frame
  | 0 => {identity}
  | n + 1 =>
    let reached := products gs n
    reached ∪ (gs ×ˢ reached).image (fun p => comp p.1 p.2)

theorem line_generators :
    products ((generatorWords .line).toFinset.image wordFrame) 3 = stabilizer .line := by
  decide +kernel

theorem axis_generators :
    products ((generatorWords .axis).toFinset.image wordFrame) 6 = stabilizer .axis := by
  decide +kernel

theorem slice_generators :
    products ((generatorWords .slice).toFinset.image wordFrame) 2 = stabilizer .slice := by
  decide +kernel

def unsignedFrames : Finset Frame :=
  (stabilizer .sector).filter fun f => f.2 = fun _ => false

def diagonalFrames : Finset Frame :=
  (stabilizer .sector).filter fun f => f.1 = id

theorem unsigned_generators :
    products (([[0], [1], [2]] : List (List (Fin 4))).toFinset.image wordFrame) 6 =
      unsignedFrames := by
  decide +kernel

theorem diagonal_generators :
    products (([[2, 3], [1, 2, 3, 1], [0, 1, 2, 3, 1, 0]] :
      List (List (Fin 4))).toFinset.image wordFrame) 3 = diagonalFrames := by
  decide +kernel

theorem sector_factor (f : Frame) (hf : f ∈ stabilizer .sector) :
    (f.1, fun _ => false) ∈ unsignedFrames ∧ (id, f.2) ∈ diagonalFrames ∧
      comp (id, f.2) (f.1, fun _ => false) = f := by
  have hd := (mem_filter.mp hf).2.1
  refine ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ⟨hd.1, by simp⟩, trivial⟩, rfl⟩,
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ⟨fun _ _ h => h, hd.2⟩, trivial⟩, rfl⟩, ?_⟩
  apply Prod.ext
  · rfl
  · funext i
    simp [comp]

/-- The line subgroup preserves the unoriented probe reflection root.
The sliced axis subgroup need not preserve it. -/
theorem line_preserves_probe :
    ∀ f ∈ stabilizer .line,
      act f (PMSubstrate.ChannelSymmetry.simple 0) = PMSubstrate.ChannelSymmetry.simple 0 ∨
      act f (PMSubstrate.ChannelSymmetry.simple 0) = -PMSubstrate.ChannelSymmetry.simple 0 := by
  have h : ∀ f, d4 f → preserves .line f →
      act f (PMSubstrate.ChannelSymmetry.simple 0) = PMSubstrate.ChannelSymmetry.simple 0 ∨
        act f (PMSubstrate.ChannelSymmetry.simple 0) = -PMSubstrate.ChannelSymmetry.simple 0 := by
    decide +kernel
  intro f hf
  exact h f (mem_filter.mp hf).2.1 (mem_filter.mp hf).2.2

theorem slice_can_move_probe :
    simpleFrame 1 ∈ stabilizer .slice ∧
      act (simpleFrame 1) (PMSubstrate.ChannelSymmetry.simple 0) ≠
        PMSubstrate.ChannelSymmetry.simple 0 ∧
      act (simpleFrame 1) (PMSubstrate.ChannelSymmetry.simple 0) ≠
        -PMSubstrate.ChannelSymmetry.simple 0 := by
  decide +kernel

/-- A uniform degree of freedom in the unmarked sector is independent
of the edge marking. Count pairs in the two embedded signed frames. -/
theorem paired_orders :
    ((stabilizer .line) ×ˢ (stabilizer .sector)).card = 1536 ∧
    ((stabilizer .axis) ×ˢ (stabilizer .sector)).card = 4608 ∧
    ((stabilizer .slice) ×ˢ (stabilizer .sector)).card = 768 := by
  obtain ⟨hs, hl, ha, hc⟩ := stabilizer_orders
  simp [card_product, hs, hl, ha, hc]

private theorem probe_fix_pair : ∀ f, d4 f → preserves .axis f →
    ((act f (PMSubstrate.ChannelSymmetry.simple 0) = PMSubstrate.ChannelSymmetry.simple 0 ∨
      act f (PMSubstrate.ChannelSymmetry.simple 0) = -PMSubstrate.ChannelSymmetry.simple 0) ↔
        act f (AxisHop.axis 1) = AxisHop.axis 1) := by
  decide +kernel

/-- With the same fixed probe as the line, the axis geometry further
restricts the covariance on the original trial encoding. -/
theorem fixed_probe_orders :
    ((stabilizer .axis).filter fun f => act f (AxisHop.axis 1) = AxisHop.axis 1).card = 4 ∧
    ((stabilizer .slice).filter fun f => act f (AxisHop.axis 1) = AxisHop.axis 1).card = 1 := by
  decide +kernel

theorem axis_fixed_probe_iff (f : Frame) (h : f ∈ stabilizer .axis) :
    (act f (PMSubstrate.ChannelSymmetry.simple 0) = PMSubstrate.ChannelSymmetry.simple 0 ∨
      act f (PMSubstrate.ChannelSymmetry.simple 0) = -PMSubstrate.ChannelSymmetry.simple 0) ↔
        act f (AxisHop.axis 1) = AxisHop.axis 1 :=
  probe_fix_pair f (mem_filter.mp h).2.1 (mem_filter.mp h).2.2

/-- Fixing the slice without marking a positive clock normal admits
normal reversal. The separate scalar phase is unchanged. -/
def slicePlane : Finset Frame :=
  (stabilizer .axis).filter fun f => act f (AxisHop.axis 3) = AxisHop.axis 3 ∨
    act f (AxisHop.axis 3) = -AxisHop.axis 3

theorem slice_plane_order : slicePlane.card = 8 := by decide +kernel

theorem slice_plane_generators :
    products (([[1], [2, 3]] : List (List (Fin 4))).toFinset.image wordFrame) 5 =
      slicePlane := by
  decide +kernel

theorem fixed_probe_generators :
    products (([[2], [3]] : List (List (Fin 4))).toFinset.image wordFrame) 2 =
      (stabilizer .axis).filter (fun f => act f (AxisHop.axis 1) = AxisHop.axis 1) ∧
    (stabilizer .slice).filter (fun f => act f (AxisHop.axis 1) = AxisHop.axis 1) =
      {identity} := by
  decide +kernel

theorem slice_plane_probe_order :
    (slicePlane.filter fun f => act f (AxisHop.axis 1) = AxisHop.axis 1).card = 2 := by
  decide +kernel

theorem slice_plane_probe_generators :
    products (([[2, 3]] : List (List (Fin 4))).toFinset.image wordFrame) 1 =
      slicePlane.filter (fun f => act f (AxisHop.axis 1) = AxisHop.axis 1) := by
  decide +kernel

/-- A bare line direction has more symmetries than the marked
sector model. This norm-two E8 reflection fixes the positive line
and sends an inactive-sector root out of its orthogonal sector. -/
theorem bare_line_mixing_root :
    let r : SubstrateWeylRoots.Lattice := Pi.single 0 1
    let pairing := PMSubstrate.Lattices.pairing
    let line := SubstrateWeylRoots.root false 0 + 2 • SubstrateWeylRoots.root false 1 +
      SubstrateWeylRoots.root false 2 + SubstrateWeylRoots.root false 3
    let inactive := SubstrateWeylRoots.root true 2
    let active := SubstrateWeylRoots.root false 0
    SubstrateWeylRoots.sector false ![1, 2, 1, 1, 0, 0, 0, 0] = AxisHop.vec OpenHandoff.direction ∧
      pairing r r = 2 ∧ line - pairing line r • r = line ∧ pairing inactive active = 0 ∧
      pairing (inactive - pairing inactive r • r) active ≠ 0 := by
  decide +kernel

/-! ### Bare root line

Use the integral simple-root coordinates of the E8 Gram matrix.
The marked positive edge is the second basis root. Conjugating the
standard highest-root stabilizer gives the seven reflections below.
-/

open PMSubstrate.Lattices

def coordinateRoot (i : Fin 8) : SubstrateWeylRoots.Lattice := Pi.single i 1

def bareReflect (r z : SubstrateWeylRoots.Lattice) : SubstrateWeylRoots.Lattice :=
  z - pairing z r • r

def highestRoot : SubstrateWeylRoots.Lattice := ![2, 3, 4, 6, 5, 4, 3, 2]

def toHighest : List (Fin 8) :=
  [3, 2, 0, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7]

def runRootWord (word : List (Fin 8)) (z : SubstrateWeylRoots.Lattice) :
    SubstrateWeylRoots.Lattice :=
  word.foldl (fun x i => bareReflect (coordinateRoot i) x) z

def bareGenerators : Fin 7 → SubstrateWeylRoots.Lattice :=
  ![coordinateRoot 7, coordinateRoot 4, coordinateRoot 6, coordinateRoot 5,
    ![0, 1, 1, 2, 1, 0, 0, 0], coordinateRoot 0, coordinateRoot 2]

theorem bare_line_coordinates :
    coordinateRoot 1 = SubstrateWeylRoots.root false 0 + 2 • SubstrateWeylRoots.root false 1 +
      SubstrateWeylRoots.root false 2 + SubstrateWeylRoots.root false 3 := by
  decide +kernel

theorem bare_conjugating_word :
    runRootWord toHighest (coordinateRoot 1) = highestRoot ∧
      (∀ i : Fin 7, pairing highestRoot (coordinateRoot i.castSucc) = 0 ∧
        runRootWord toHighest.reverse (coordinateRoot i.castSucc) = bareGenerators i) ∧
      pairing highestRoot (coordinateRoot 7) = 1 := by
  decide +kernel

theorem bare_generators_gram :
    (∀ i, pairing (bareGenerators i) (coordinateRoot 1) = 0) ∧
      ∀ i j, pairing (bareGenerators i) (bareGenerators j) = gram i.castSucc j.castSucc := by
  decide +kernel

theorem bare_generators_fix_direction (i : Fin 7) :
    bareReflect (bareGenerators i) (coordinateRoot 1) = coordinateRoot 1 := by
  fin_cases i <;> decide +kernel

theorem bare_reverse_direction :
    bareReflect (coordinateRoot 1) (coordinateRoot 1) = -coordinateRoot 1 := by
  decide +kernel

/-- Sector action on the actual spanning roots. The coefficient
table is computed in the integral substrate Gram matrix. -/
def bareSectorCoefficients (i : Fin 7) (sector : Bool) (j : Fin 4) : ℤ :=
  pairing (SubstrateWeylRoots.root sector j) (bareGenerators i)

theorem bare_generator_sector_action (i : Fin 7) (sector : Bool) (j : Fin 4) :
    bareReflect (bareGenerators i) (SubstrateWeylRoots.root sector j) =
      SubstrateWeylRoots.root sector j - bareSectorCoefficients i sector j • bareGenerators i := rfl

theorem bare_sector_coefficients :
    ∀ i : Fin 7,
      (fun j => bareSectorCoefficients i false j) =
        (![![0,0,0,0], ![0,1,-2,0], ![0,0,0,0], ![0,0,1,-1], ![0,-1,0,2], ![1,0,0,-1], ![-2,1,0,0]] : Fin 7 → Fin 4 → ℤ) i ∧
      (fun j => bareSectorCoefficients i true j) =
        (![![1,-2,1,1], ![0,0,0,0], ![-2,1,0,0], ![1,0,0,0], ![0,0,0,0], ![0,0,-1,0], ![0,0,0,0]] : Fin 7 → Fin 4 → ℤ) i := by
  decide +kernel

end NodeSymmetry

/-! ## Equivariance of factorwise actions -/

set_option maxRecDepth 16000 in
theorem line_probe_equivariant :
    ∀ f, NodeSymmetry.d4 f → NodeSymmetry.preserves .line f →
      Function.Commute (NodeSymmetry.act f) (NodeSymmetry.act (NodeSymmetry.simpleFrame 0)) := by
  have h : ∀ f, NodeSymmetry.d4 f → NodeSymmetry.preserves .line f →
      NodeSymmetry.comp f (NodeSymmetry.simpleFrame 0) =
        NodeSymmetry.comp (NodeSymmetry.simpleFrame 0) f := by
    decide +kernel
  intro f hf hl v
  rw [← NodeSymmetry.act_comp, h f hf hl, NodeSymmetry.act_comp]

theorem slice_probe_not_equivariant :
    ¬ Function.Commute (NodeSymmetry.act (NodeSymmetry.simpleFrame 1))
      (NodeSymmetry.act (NodeSymmetry.simpleFrame 0)) := by
  intro h
  have hn : NodeSymmetry.act (NodeSymmetry.simpleFrame 1)
      (NodeSymmetry.act (NodeSymmetry.simpleFrame 0) (AxisHop.axis 0)) ≠
      NodeSymmetry.act (NodeSymmetry.simpleFrame 0)
      (NodeSymmetry.act (NodeSymmetry.simpleFrame 1) (AxisHop.axis 0)) := by
    decide +kernel
  exact hn (h (AxisHop.axis 0))

/-- Apply the same channel matrix in every live and record cell. -/
def bankAction {R : ℕ} (A : PacketGaugeActions.M) (bank : PacketBank R) : PacketBank R :=
  fun p => (A *ᵥ (fun a => bank (p.1, a))) p.2

theorem fifo_commutes_bankAction (R : ℕ) (A : PacketGaugeActions.M) :
    Function.Commute (fifoEquiv R) (bankAction A) := by
  intro bank
  rfl

/-- For a factorwise relabelling, equivariance requires the corresponding
core commutation and one covariance equation on the bank fibre. -/
theorem joint_commutes_iff {I : Type*} {R : ℕ} (core : I → I)
    (packet : I → Equiv.Perm (PacketBank R)) (renameCore : I → I)
    (renameBank : PacketBank R → PacketBank R) :
    Function.Commute (jointTick core packet) (Prod.map renameCore renameBank) ↔
      Function.Commute core renameCore ∧
        ∀ i bank, packet (renameCore i) (renameBank bank) =
          renameBank (packet i bank) := by
  constructor
  · intro h
    exact ⟨fun i => congrArg Prod.fst (h (i, 0)),
      fun i bank => congrArg Prod.snd (h (i, bank))⟩
  · rintro ⟨hc, hp⟩ s
    exact Prod.ext (hc s.1) (hp s.1 s.2)

/-- Idle and FIFO commute with every cellwise channel matrix as soon as
the core relabelling itself commutes. This includes all certified packet
gauge matrices, even without using their unitarity. -/
theorem hold_fifo_equivariant {I : Type*} (R : ℕ) (core renameCore : I → I)
    (hc : Function.Commute core renameCore) (A : PacketGaugeActions.M) :
    Function.Commute (jointTick core (fun _ => Equiv.refl (PacketBank R)))
      (Prod.map renameCore (bankAction A)) ∧
    Function.Commute (jointTick core (fun _ => fifoEquiv R))
      (Prod.map renameCore (bankAction A)) :=
  ⟨(joint_commutes_iff _ _ _ _).2 ⟨hc, fun _ _ => rfl⟩,
    (joint_commutes_iff _ _ _ _).2 ⟨hc, fun _ => fifo_commutes_bankAction R A⟩⟩

/-! ## Conserved totals -/

theorem ring_stream_total {n : ℕ} (either : Bool) (s : RingReceiver.State n)
    {M : Type*} [AddCommMonoid M] (measure : Bool → M) :
    (∑ x, (measure ((RingReceiver.tick n either s).2.2.2 x).1 +
      measure ((RingReceiver.tick n either s).2.2.2 x).2)) =
      ∑ x, (measure (s.2.2.2 x).1 + measure (s.2.2.2 x).2) := by
  calc
    _ = ∑ x : Fin n, (measure (s.2.2.2 ((finRotate n).symm x)).1 +
        measure (s.2.2.2 (finRotate n x)).2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [RingReceiver.tick_ports]
      change (measure (LocalController.applyGuard
        (fun _ => RingReceiver.exchange either (s.2.1 x))
        ((s.2.2.2 ((finRotate n).symm x)).1, (s.2.2.2 (finRotate n x)).2)).1 + _) = _
      cases h : RingReceiver.exchange either (s.2.1 x) <;>
        simp [LocalController.applyGuard, RingReceiver.arrivals, OpenReferenceFlow.streamShift,
          add_comm]
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [Equiv.sum_comp (finRotate n).symm (fun x => measure (s.2.2.2 x).1),
        Equiv.sum_comp (finRotate n) (fun x => measure (s.2.2.2 x).2)]

/-- Every fixed per-channel total across the bank is preserved. For
population take `measure = Complex.normSq`. No per-cell assertion follows. -/
theorem fifo_channel_total (R : ℕ) (bank : PacketBank R) (a : PacketGaugeActions.Channels)
    {M : Type*} [AddCommMonoid M] (measure : ℂ → M) :
    (∑ i : Fin (R + 1), measure (fifoEquiv R bank (i, a))) =
      ∑ i : Fin (R + 1), measure (bank (i, a)) :=
  Equiv.sum_comp (finRotate (R + 1)) (fun i => measure (bank (i, a)))

/-- An algebraic counterexample to the implication from invertibility
and channel equivariance to conservation of population. -/
private noncomputable def doubleBank (R : ℕ) : Equiv.Perm (PacketBank R) where
  toFun f p := 2 * f p
  invFun f p := f p / 2
  left_inv f := by funext p; dsimp; ring
  right_inv f := by funext p; dsimp; ring

theorem equivariant_lift_can_change_population (a : PacketGaugeActions.Channels) :
    ∃ e : Equiv.Perm (PacketBank 0),
      (∀ A : PacketGaugeActions.M, Function.Commute e (bankAction A)) ∧
      (∑ i : Fin 1, Complex.normSq (e (fun _ => 1) (i, a))) ≠
        ∑ _i : Fin 1, Complex.normSq (1 : ℂ) := by
  refine ⟨doubleBank 0, ?_, ?_⟩
  · intro A bank
    funext p
    change 2 * (∑ i, A p.2 i * bank (p.1, i)) =
      ∑ i, A p.2 i * (2 * bank (p.1, i))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => mul_left_comm 2 (A p.2 i) (bank (p.1, i)))
  · norm_num [doubleBank, Complex.normSq_apply]

/-! ## A clock phase is not selected by the excursion account -/

theorem shifted_excursion_boundaries :
    CarrierReferenceCycle.boundaries (fun t => decide (t = (2 : Fin Delta))) = {1, 2} := by
  decide +kernel

theorem shifted_excursion_same_cost (c : Fin 3) (toll : ℝ) :
    PMSubstrate.NetCost.expectedCost toll
        (CarrierReferenceCycle.carrierEvents c (fun t => decide (t = (2 : Fin Delta)))) =
      PMSubstrate.NetCost.expectedCost toll
        (CarrierReferenceCycle.carrierEvents c CarrierReferenceCycle.excursionMask) := by
  rw [CarrierReferenceCycle.carrier_cost_for_mask, shifted_excursion_boundaries,
    CarrierReferenceCycle.carrier_cycle_cost]
  norm_num

end PMTransport.Components
