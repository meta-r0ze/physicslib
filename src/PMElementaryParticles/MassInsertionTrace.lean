import PMElementaryParticles.ElectricCompanionBank
import PMElementaryParticles.ElectricCoordinateDecoder
import PMElementaryParticles.WireSchedule
import PMKAutomaton.LocalController

/-!
# Charged-lepton mass insertion readouts and serial timing

A supplied occupied seed runs the short electric writer and exposes the
charged-lepton companion guard at the decoded port. The open receiver
tracks a supplied live payload from the restoring exchange to its
downstream record arrival. A separate receiver test follows a marker
already on the record stream. The serial timing bounds use the existing
schedule with its supplied admission test.

## Charged-lepton insertion trace

| Route | Retained datum and consumer | What still needs admission |
| --- | --- | --- |
| Direct, address 0 | With the short electric writer, an occupied neutral coordinate seed is prepared, kicked at `3π/2` and `3π`, and decoded to port 2. The port reads `(true, true)` and supplies the companion guard (`charged_lepton_written_port`, `charged_lepton_port_fires`). The open receiver can feed the writer from a specified occupied live arrival through a downstream record slot (`occupied_arrival_writes`). | Select the occupied source, bank supply and the writer slots of this implementation. The transported port requires renewal. The inverse bank circuit rebalances it using the opposite-wall label (`charged_lepton_bank_uncompute`). Admit and time that return separately. |
| Restoring, addresses 1 and 2 | When the payload arrives live and the reference arrives on the record stream, exchange restores the live reference and passes the same payload through the downstream record stream (`restored_live_and_payload_iff`, `restoring_payload_trace`). At an adjacent exit, one further tick and another exchange deliver it live and retain the other arrival (`restoring_entry_exit`). The same ports are realized by two native ticks of an open-compatible controller with both requests set at entry and exit and idle requests at the intermediate live source (`restoring_native_two_ticks`). For a marker already arriving on the record stream, the mixed bypass witness carries it through (`mixed_throughArrival`). | Identify the incoming streams at each native visit on each address. Attach the coherent pulse, its phase and its duration to the selected ports and certify the exit consumer. |

The short writer is a concrete candidate with its own two kicks and
decoding word. With inverse-short bank preparation, the preparation
and decoder consume 27 and 25 root quarter-times, respectively. The kicks,
companion control, and independent bank return have additional scheduling inputs.

The schedule proves elapsed lower bounds for the supplied serial word
template. The direct route cannot fit a 43-tick period. A restoring route
within one period requires the short word at one tick per quarter-time,
with at most seven ticks for its two node visits combined. Tests, waiting
and other booked work can further reduce the available time.
`MassInsertionTrace.direct_elapsed` and `restoring_elapsed` give the
unrounded bounds for general horizons. The individual elapsed times of
the admitted pulses are the inputs to PMAction's rate conversion.

### Restoring class change and its clock cost

The two adjacent exchanges carry the gapped payload unchanged. Its glue
class differs from that of the required endpoint
(`RestoringWallShift.gapped_payload_ne_endpoint`). The four-reflection
`classShiftWord` advances both carrier factors in place. Composing it after
the gapped crossing and the open delivery gives the encoded endpoint
(`restoring_exit_then_class_shift`). For address 1 the class changes from
`2` to `0`; for address 2 it changes from `0` to `1`.

At two root quarter-times per reflection this word needs eight quarter-times.
Booking that work serially inside the two node visits exceeds their seven-tick
combined budget in a one-period restoring schedule
(`no_single_period_with_serial_class_shift`). An overlapping or integrated
implementation would need its own timing and admission proof. The unitary
two-port pulse candidate labels the transferred port with the shifted address
and preserves the signed index. Its weight and pulse duration still need a
native readout in crossing-clock units.

### Which weight belongs to the shifted pulse

The shifted port receives the cross-branch contribution from one input and
the stay-branch contribution from the other. `shiftedOutflow_eq` gives the
population law on those two incoherent inputs. If the resulting net current
equals the steady current of the two equal legs with a floating node, the
shifted weight is exactly `α/2`. A principal pulse then has area
`arcsin(√(α/2))`. Its rate relative to the direct pulse also uses both
durations (`steady_rate_ratio`).

For the isolated three-port coherent execution, entry-live to exit-live
goes through the intermediate record port. The exit amplitude is
`−sin(θ) sin(φ)` and the weight is the product of the two exchange weights.
If both local unexchanged through weights are `α`, the output of this
particular exchange-exchange route is `(1−α)² > α/2`. To establish the
steady calibration, identify the physical output with the balanced
floating-node readout and account for any extra histories and renewal
visits. To use an isolated pulse sequence, calibrate the weights, relative
phase and duration of that sequence on the admitted ports.

If fresh incoherent inputs visit right then left and the center is retained
between visits and across cycles, `AlternatingReferenceNode.fixed_current`
gives the current per complete cycle. The shifted port matches it at weight
`w/(2-w)`, where `w` is transfer to the center. The common-tick conversion
`alternating_crossing_rate_ratios` uses the complete cycle's tick count.
Selecting this regime requires a native source of repeated inputs and the
retained-center readout.

The native single-marker trace reduces the live exit to the joint entry
and exit guards at their actual phases (`LocalController.restoring_marker_live`).
A transfer weight for this event requires weights on joint histories. In the
steady-current model, `bookedNodeTicks` measures the node interval from
entry start through exit completion, including any wait. Under that event
identification, `mass_from_scheduled_steady_pulses` places the independently
timed restoring insertions in the two Schur rows.


### Direct writer renewal

Once the companion returns the occupied guard port to coordinate 2,
the decoder's inverse visit word restores the incoming kicked bank
and carries the same flag sum as the forward decoder on its actual path.
The opposite-wall label supplies both inverse electric phases. Under a
comparison per decoder pulse and per completed electric kick, the
writer and uncompute require three flags each. The shared-current word
books a swap in each direction, giving `13/2` flags in total. Starting
from a fresh clean occupied seed adds one flag. The decoder alone takes 25 root
quarter-times forward and 27 back, with another 27 for fresh
preparation. At one or more substrate ticks per root quarter-time that
requires more than one 43-tick frame. Place the companion return and
payload continuation in the full schedule and include their own claims.
-/

namespace PMElementaryParticles.MassInsertionTrace

open PMConstants.PacketGaugeActions
open ProtocolInventory HeavyFlipControl ControlledGluedRegister

private theorem charged_lepton_code :
    ∀ c : Channels, active c = false → baseProtocol c = some .electron →
      labelRecord c = (true, true) := by decide +kernel

/-- The clean writer and selected direct flip retain the occupied orbit
record. A static charged-lepton input on address zero has both bits set. -/
theorem charged_lepton_direct (c : Channels) (a : Fin 8) (hc : active c = false)
    (he : baseProtocol c = some .electron) :
    controlledFlip (true, true) (writeRecord ((0, c, a), (false, false))) =
      ((0, opposite c, a), (true, true)) := by
  rw [write_clean]
  simp [controlledFlip, direct_iff, charged_lepton_code c hc he]

section ElectricWriter

open Matrix PMAction CarrierParity ElectricCoordinateDecoder ElectricFourPortRecord

/-- The inverse short word prepares the occupied coordinate seed, the two
electric kicks encode its supplied label, and the forward short word
writes the retained port in the same carrier bank. -/
noncomputable def writeFromSeed (k : Fin 3) (p : ℝ) (c : Channels) :=
  let ready := (shortDecoder k p)ᴴ *ᵥ (embedding k *ᵥ Pi.single (0 : Fin 4) 1)
  shortDecoder k p *ᵥ (embedding k *ᵥ
    (kick true (phase (3 * Real.pi) c) *ᵥ
      (kick false (phase (3 * Real.pi / 2) c) *ᵥ ((embedding k)ᴴ *ᵥ ready))))

/-- The short word's occupied output is port 2 for a static charged
lepton. The reversed bit convention supplies the guard's exact record. -/
theorem charged_lepton_written_port (k : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2)
    (c : Channels) (hc : active c = false) (he : baseProtocol c = some .electron) :
    writeFromSeed k p c = embedding k *ᵥ Pi.single (2 : Fin 4) 1 ∧
      recordAtPort (2 : Fin 4) = labelRecord c := by
  have hcode := charged_lepton_code c hc he
  refine ⟨?_, ?_⟩
  · have hready :
        (embedding k)ᴴ *ᵥ ((shortDecoder k p)ᴴ *ᵥ (embedding k *ᵥ Pi.single (0 : Fin 4) 1)) =
          bank 1 1 := by
      rw [short_prepares k p hp hp', Matrix.mulVec_mulVec, CarrierParity.isometry, Matrix.one_mulVec]
    dsimp only [writeFromSeed]
    rw [hready, short_reads k p hp hp', hcode]
    have hport : shortPort (true, true) = 2 := by decide +kernel
    rw [hport]
  · rw [hcode]
    decide +kernel

/-- The written port supplies the companion guard on the static heavy
address. The same endpoint word transports each supporting carrier. -/
theorem charged_lepton_port_fires (c : Channels) (a : Fin 8)
    (hc : active c = false) (he : baseProtocol c = some .electron)
    (v : CarrierEvents.Carrier (wallClass 0 (!active c))) :
    CompanionHeavyFlip.run (true, true) (recordAtPort (2 : Fin 4)) (encode 0 c a, CarrierEvents.vector v) =
      (encode 0 (opposite c) a,
        CarrierEvents.vector (ElectricCompanionBank.companionTransport (active c) v)) := by
  have h := (ElectricCompanionBank.guarded_companion_transport c a v).2
  rw [charged_lepton_code c hc he] at h
  change CompanionHeavyFlip.run (true, true) (true, true)
    (encode 0 c a, CarrierEvents.vector v) = _ at h
  have hport : recordAtPort (2 : Fin 4) = (true, true) := by decide +kernel
  rwa [hport]

/-- The transported charged-lepton port needs a new preparation before
it can serve as the balanced bank for another writer visit. -/
theorem charged_lepton_port_needs_preparation (wall : Bool) :
    ElectricCompanionBank.advanceCoordinates wall (Pi.single (2 : Fin 4) 1) ≠ bank 1 1 := by
  intro h
  have hport := ((ElectricCompanionBank.written_port_ready_iff wall 2).mp h).2
  exact (by decide : (2 : Fin 4) ≠ 0) hport

private theorem reverse_companion_coordinates (wall : Bool) (ψ : Fin 4 → ℂ) :
    ElectricCompanionBank.advanceCoordinates (!wall)
      (ElectricCompanionBank.advanceCoordinates wall ψ) = ψ := by
  cases wall <;>
    simp only [ElectricCompanionBank.advanceCoordinates, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_true, ite_false]
  all_goals
    simp only [mulVec_mulVec, PMKAutomaton.CarrierTriality.triality_cube, one_mulVec]

private theorem reverse_kick (high : Bool) (t : ℝ) (c : Channels) (ψ : Fin 4 → ℂ) :
    kick high (phase (-t) c) *ᵥ (kick high (phase t c) *ᵥ ψ) = ψ := by
  have hphase : phase (-t) c * phase t c = 1 := by
    rw [phase, phase, ← Complex.exp_add]
    push_cast
    have h : ((-(t : ℂ)) * (ElectricHeavyRecord.q c : ℂ)) * Complex.I +
        (t : ℂ) * (ElectricHeavyRecord.q c : ℂ) * Complex.I = 0 := by ring
    rw [h, Complex.exp_zero]
  have hk : kick high (phase (-t) c) * kick high (phase t c) = 1 := by
    ext i j
    cases high <;> fin_cases i <;> fin_cases j <;>
      simp [kick, hphase]
  rw [mulVec_mulVec, hk, one_mulVec]

/-- After the guard has consumed the written port, reverse the companion
coordinate transport, undo decoding, and apply the inverse kicks. The
opposite-wall label supplies the same electric phases, and the bank is
balanced again. Physical admission and timing of these return operations
are part of the renewal schedule. -/
theorem charged_lepton_bank_uncompute (wall : Bool) (k : Fin 3) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1 / 2) (c : Channels)
    (hc : active c = false) (he : baseProtocol c = some .electron) :
    let written := ElectricCompanionBank.advanceCoordinates wall (Pi.single (2 : Fin 4) 1)
    let returned := ElectricCompanionBank.advanceCoordinates (!wall) written
    let kicked := (embedding k)ᴴ *ᵥ ((shortDecoder k p)ᴴ *ᵥ (embedding k *ᵥ returned))
    kick false (phase (-(3 * Real.pi / 2)) (opposite c)) *ᵥ
      (kick true (phase (-(3 * Real.pi)) (opposite c)) *ᵥ kicked) = bank 1 1 := by
  have h := short_reads k p hp hp' c
  have hport : shortPort (true, true) = (2 : Fin 4) := by decide +kernel
  rw [charged_lepton_code c hc he, hport] at h
  have hinv : (shortDecoder k p)ᴴ * shortDecoder k p = 1 :=
    Unitary.star_mul_self_of_mem (short_unitary k p)
  have hdecode := congrArg (fun v => (shortDecoder k p)ᴴ *ᵥ v) h
  rw [mulVec_mulVec, hinv, one_mulVec] at hdecode
  have hcoords :
      (embedding k)ᴴ *ᵥ ((shortDecoder k p)ᴴ *ᵥ (embedding k *ᵥ Pi.single (2 : Fin 4) 1)) =
        kick true (phase (3 * Real.pi) c) *ᵥ
          (kick false (phase (3 * Real.pi / 2) c) *ᵥ bank 1 1) := by
    rw [← hdecode, mulVec_mulVec, CarrierParity.isometry, one_mulVec]
  dsimp only
  rw [reverse_companion_coordinates, hcoords, phase_opposite, phase_opposite,
    reverse_kick, reverse_kick]

end ElectricWriter

/-- The routed value that the next site can read before applying its own
receiver operation. This chooses the downstream record arrival as the
candidate readout; its use by the restoring insertion is an attachment
to be proved on a physical trace. -/
def throughArrival (rule : PMKAutomaton.LocalController.Rule)
    (s : PMKAutomaton.LocalController.State) (site : ℤ) : Bool :=
  let after := PMKAutomaton.LocalController.rawTick rule s
  (PMAction.OpenReferenceFlow.streamShift PMAction.OpenReferenceFlow.line
    after.2.2 (site - 1)).2

open PMKAutomaton.LocalController in
/-- A marked record-stream input survives to the downstream arrival under
bypass. With the same mixed requests and arrivals the other reversible
guard reflects it, so the downstream read is unmarked. -/
theorem mixed_throughArrival (s : PMKAutomaton.LocalController.State) (site : ℤ)
    (hrequest : (s.2.1 site).1 = (true, false))
    (hlive : (s.2.2 (site - 1)).1 = false) (hrecord : (s.2.2 (site + 1)).2 = true) :
    throughArrival exchangeOnBoth s site = true ∧
      throughArrival exchangeOnEither s site = false := by
  have h := mixed_requests_different_destinations s site hrequest hlive hrecord
  have hx : PMAction.OpenReferenceFlow.line (site - 1) = site := by
    change site - 1 + 1 = site
    omega
  simp [throughArrival, PMAction.OpenReferenceFlow.streamShift, hx, h.1, h.2]

section RestoringRoute

open PMAction.OpenReferenceFlow

/-- With separate live payload and record reference arrivals, an exchange
restores the live register and releases that same payload to the next
record arrival. The two obligations jointly force exchange on unequal
arrivals in this single-visit model. -/
theorem restored_live_and_payload_iff {V : Type*} (s : State ℤ V)
    (payload reference : V) (hne : payload ≠ reference)
    (hlive : (s (-1)).1 = payload) (href : (s 1).2 = reference)
    (exchange : Bool) :
    let after := if exchange then evolution 0 line s else streamShift line s
    ((after 0).1 = reference ∧
        (streamShift line after (-1)).2 = payload) ↔ exchange = true := by
  have hnext : line (-1) = 0 := rfl
  have hleft : line⁻¹ 0 = -1 := rfl
  have hright : line 0 = 1 := rfl
  cases exchange <;>
    simp [streamShift, evolution_apply, hnext, hleft, hright, hlive, href, hne]

/-- In the adjacent-site candidate the entry exchange restores its live
reference. One tick later the exit receives the same payload on its record
input. Exit exchange delivers it live and retains the exit's other input
on the record stream. -/
theorem restoring_entry_exit {V : Type*} (s : State ℤ V)
    (payload entryReference exitReference : V)
    (hlive : (s (-1)).1 = payload) (hentry : (s 1).2 = entryReference)
    (hexit : (s (-3)).1 = exitReference) :
    let entered := evolution 0 line s
    entered 0 = (entryReference, payload) ∧
      streamShift line entered (-1) = (exitReference, payload) ∧
      evolution (-1) line entered (-1) = (payload, exitReference) := by
  have h₁ : evolution 0 line s 0 = (entryReference, payload) := by
    rw [evolution_apply]
    change ((s 1).2, (s (-1)).1) = _
    rw [hentry, hlive]
  have h₂ : (evolution 0 line s (-2)).1 = exitReference := by
    rw [evolution_apply]
    change (s (-3)).1 = _
    exact hexit
  have h₃ : streamShift line (evolution 0 line s) (-1) = (exitReference, payload) := by
    change ((evolution 0 line s (-2)).1, (evolution 0 line s 0).2) = _
    rw [h₂, h₁]
  have h₄ := congrArg Prod.swap h₃
  exact ⟨h₁, h₃, h₄⟩

open PMKAutomaton.LocalController in
/-- A fixed open-compatible controller realizes the adjacent exchange trace
from these retained requests. The exit uses the then-current record
arrival while the intervening live source stays on its stream. -/
theorem restoring_native_two_ticks (rule : Rule) (hrule : OpenCompatible rule)
    (s : PMKAutomaton.LocalController.State)
    (hentry : (s.2.1 0).1 = (true, true))
    (hexit : (s.2.1 (-1)).1 = (true, true))
    (hsource : (s.2.1 (-2)).1 = (false, false)) :
    let afterEntry := rawTick rule s
    let afterExit := rawTick rule afterEntry
    afterEntry.2.2 0 = ((s.2.2 1).2, (s.2.2 (-1)).1) ∧
      afterExit.2.2 (-1) = ((s.2.2 (-1)).1, (s.2.2 (-3)).1) := by
  intro afterEntry afterExit
  have h₁ : afterEntry.2.2 0 = ((s.2.2 1).2, (s.2.2 (-1)).1) := by
    change applyGuard (rule s.1 (s.2.1 0).1)
      ((s.2.2 (-1)).1, (s.2.2 1).2) = _
    rw [applyGuard, hentry, (hrule _ _).2]
    rfl
  have h₂ : (afterEntry.2.2 (-2)).1 = (s.2.2 (-3)).1 := by
    change (applyGuard (rule s.1 (s.2.1 (-2)).1)
      ((s.2.2 (-3)).1, (s.2.2 (-1)).2)).1 = _
    rw [applyGuard, hsource, (hrule _ _).1]
    rfl
  have h₃ : (afterEntry.2.1 (-1)).1 = (true, true) := hexit
  refine ⟨h₁, ?_⟩
  change applyGuard (rule afterEntry.1 (afterEntry.2.1 (-1)).1)
    ((afterEntry.2.2 (-2)).1, (afterEntry.2.2 0).2) = _
  rw [applyGuard, h₁, h₂, h₃, (hrule _ _).2]
  rfl

/-- A payload supplied for visit `t+1` reaches the downstream record
slot after `d` further ticks on the open exchange line. The live slot
at the release visit contains its independently supplied reference. -/
theorem restoring_payload_trace {V : Type*} (s : State ℤ V)
    (payload reference : V) (t d : ℕ)
    (hlive : (s (-((t : ℤ) + 1))).1 = payload)
    (href : (s ((t : ℤ) + 1)).2 = reference) :
    PMKAutomaton.OpenHandoff.run s (t + 1) 0 = (reference, payload) ∧
      (PMKAutomaton.OpenHandoff.run s (t + 1 + d) (-(d : ℤ))).2 = payload := by
  constructor
  · rw [PMKAutomaton.OpenHandoff.receiver_trace, href, hlive]
  · rw [PMKAutomaton.OpenHandoff.export_trace s (by omega : d < t + 1 + d)]
    rw [show (d : ℤ) - (↑(t + 1 + d) : ℤ) = -((t : ℤ) + 1) by push_cast; ring, hlive]

open Matrix in
/-- Attach the short writer to the displaced record stream of the open
receiver. The supplied occupied charged-lepton arrival is still present
at the selected downstream tick, and writes port 2 there. -/
theorem occupied_arrival_writes (s : State ℤ (Option Channels)) (reference : Option Channels)
    (t d : ℕ) (k : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2)
    (c : Channels) (hc : active c = false) (he : baseProtocol c = some .electron)
    (hlive : (s (-((t : ℤ) + 1))).1 = some c)
    (href : (s ((t : ℤ) + 1)).2 = reference) :
    PMKAutomaton.OpenHandoff.run s (t + 1) 0 = (reference, some c) ∧
      ((PMKAutomaton.OpenHandoff.run s (t + 1 + d) (-(d : ℤ))).2).map (writeFromSeed k p) =
        some (PMAction.CarrierParity.embedding k *ᵥ Pi.single (2 : Fin 4) 1) := by
  obtain ⟨hvisit, hrecord⟩ := restoring_payload_trace s (some c) reference t d hlive href
  exact ⟨hvisit, by rw [hrecord, Option.map_some, (charged_lepton_written_port k p hp hp' c hc he).1]⟩

end RestoringRoute

section Timing

open WireSchedule

/-- A direct reference flip uses the stored record, and the writer's
position and sector visits precede it in that order. -/
theorem direct_record_schedule {ticks : ℕ} {p : Premises ticks} {s : Schedule ticks}
    (hs : s ∈ family p) (ha : p.address = 0) :
    ∃ x, s.2 .referenceFlip = some x ∧ x.2.1 = .recorded ∧
      endsBefore p s .position .sector = true ∧
      endsBefore p s .sector .referenceFlip = true := by
  obtain ⟨x, hx, _, hb, hp⟩ := required_placement hs (e := .referenceFlip)
    (by simp [required, ha])
  obtain ⟨_, _, _, _, hw⟩ := required_placement hs (e := .sector)
    (by simp [required, ha])
  have hbranch : x.2.1 = .recorded := by
    cases hh : x.2.1 <;> simp [branchAllowed, hh] at hb ⊢
  exact ⟨x, hx, hbranch, hw _ (by simp [predecessors]), hp _ (by simp [predecessors])⟩

/-- Static flip, equal-class crossing and direct reference flip must all
fit inside the executed direct schedule. The writer and any extra visits
can increase its elapsed time. -/
theorem direct_elapsed {ticks : ℕ} {p : Premises ticks} {s : Schedule ticks}
    (hs : s ∈ family p) (ha : p.address = 0) :
    (if p.shortFlip then 60 else 76) * p.quarterTicks ≤ finishTick p s := by
  obtain ⟨x, hx, _, _, _⟩ := required_placement hs (e := .staticFlip) rfl
  obtain ⟨y, hy, _, _, hbefore⟩ := required_placement hs (e := .gappedCrossing) rfl
  obtain ⟨z, hz, _, _, hafter⟩ := required_placement hs (e := .referenceFlip)
    (by simp [required, ha])
  have h := serial_three_le_finish p s hx hy hz
    (hbefore _ (by simp [predecessors])) (hafter _ (by simp [predecessors]))
  cases hshort : p.shortFlip <;> simp only [duration, hshort, Bool.false_eq_true,
    ↓reduceIte] at h ⊢ <;> omega

/-- A restoring route books both node visits after the static flip and
equal-class crossing. The node durations enter the elapsed lower bound
explicitly because the certified root words do not fix them. -/
theorem restoring_elapsed {ticks : ℕ} {p : Premises ticks} {s : Schedule ticks}
    (hs : s ∈ family p) (ha : p.address ≠ 0) :
    (if p.shortFlip then 36 else 44) * p.quarterTicks +
      p.otherTicks .nodeEnter + p.otherTicks .nodeLeave ≤ finishTick p s := by
  obtain ⟨x, hx, _, _, _⟩ := required_placement hs (e := .staticFlip) rfl
  obtain ⟨y, hy, _, _, hcross⟩ := required_placement hs (e := .gappedCrossing) rfl
  obtain ⟨z, hz, _, _, henter⟩ := required_placement hs (e := .nodeEnter)
    (by simp [required, ha])
  obtain ⟨w, hw, _, _, hleave⟩ := required_placement hs (e := .nodeLeave)
    (by simp [required, ha])
  have hxy := hcross .staticFlip (by simp [predecessors])
  have hyz := henter .gappedCrossing (by simp [predecessors])
  have hzw := hleave .nodeEnter (by simp [predecessors])
  have hLast := placement_le_finish p s hw
  simp only [endsBefore, hx, hy, hz, hw, decide_eq_true_eq] at hxy hyz hzw
  cases hshort : p.shortFlip <;> simp only [duration, hshort, Bool.false_eq_true,
    ↓reduceIte] at hxy hyz hzw hLast ⊢ <;> omega

/-- A single clock period cannot contain the direct serial route. -/
theorem no_single_period_direct {ticks : ℕ} {p : Premises ticks} {s : Schedule ticks}
    (hs : s ∈ family p) (ha : p.address = 0)
    (horizon : ticks ≤ PMSubstrate.E8Values.Delta) : False := by
  have h := (mem_family p s).1 hs
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h
  have hq : 0 < p.quarterTicks := by tauto
  have htime := (direct_elapsed hs ha).trans ((finishTick_le_horizon p s hs).trans horizon)
  rw [PMSubstrate.E8Values.Delta_eq] at htime
  cases hb : p.shortFlip <;> simp [hb] at htime <;> omega

/-- A one-period restoring schedule must use the short word with one tick
per quarter-time. The two node visits then have at most seven ticks of
combined duration before accounting for any other scheduled work. -/
theorem restoring_in_one_period {ticks : ℕ} {p : Premises ticks} {s : Schedule ticks}
    (hs : s ∈ family p) (ha : p.address ≠ 0)
    (horizon : ticks ≤ PMSubstrate.E8Values.Delta) :
    p.shortFlip = true ∧ p.quarterTicks = 1 ∧
      p.otherTicks .nodeEnter + p.otherTicks .nodeLeave ≤ 7 := by
  have h := (mem_family p s).1 hs
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h
  have hq : 0 < p.quarterTicks := by tauto
  have htime := (restoring_elapsed hs ha).trans ((finishTick_le_horizon p s hs).trans horizon)
  rw [PMSubstrate.E8Values.Delta_eq] at htime
  cases hb : p.shortFlip <;> simp [hb] at htime ⊢ <;> omega

end Timing

end PMElementaryParticles.MassInsertionTrace
