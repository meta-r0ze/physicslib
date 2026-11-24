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
