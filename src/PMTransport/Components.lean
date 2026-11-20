import PMTransport.Values
import PMTransport.BoundaryErasure
import PMTransport.Machine.CarrierReferenceCycle
import PMTransport.Machine.RecordTransport
import PMTransport.Machine.RootMaintenance
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

end PMTransport.Components
