import PMElementaryParticles.RestoringBankClock
import PMElementaryParticles.RestoringOccupiedHistory
import PMElementaryParticles.ProgramClasses

/-!
# Occupied charged-lepton banked restoring trace

The occupied receiver starts with the post-crossing active channel. The
typed lift retains its two carrier values until extraction. The output
bank follows the class word, and a separate fresh bank renews the input.
The booked operations, successful request history and prepared banks are
inputs to this trace.
-/

namespace PMElementaryParticles.OccupiedBankedRestoring

open PMAction PMKAutomaton IsolatedExcitation RingReceiver RestoringRingHistory
open RestoringExtraction RestoringWallShift GluedRegister ControlledGluedRegister
open GappedGluedCrossing ProtocolInventory PMConstants.PacketGaugeActions

/-- Static charged-lepton channel in the inventory's signed lepton slot. -/
def staticLepton : Channels := .inr (.inr (.inr 1))

theorem static_lepton_unique (c : Channels) :
    active c = false ∧ baseProtocol c = some .electron ↔ c = staticLepton := by
  have h : ∀ c : Channels, active c = false ∧ baseProtocol c = some .electron ↔
      c = staticLepton := by decide +kernel
  exact h c

theorem charged_channels :
    active (opposite staticLepton) = true ∧
      baseProtocol (opposite staticLepton) = some .electron ∧
      ProgramClasses.classOf staticLepton = 5 ∧
      ProgramClasses.classOf (opposite staticLepton) = 3 := by decide +kernel

/-- Carrier pair at the receiver input, following the equal-class crossing. -/
def restoringPayload (g : Fin 3) (a : Fin 4) (sign : Fin 2) : Wt × Wt :=
  runGappedCrossing g (encode g staticLepton (signedAxis a sign))

/-- The occupied receiver state uses the active channel of the carrier pair. -/
def chargedSeed (g : Fin 3) (vacuum : VacuumLabel (wallClass g false))
    (q : History) : RingReceiver.State Delta :=
  localizedEmbedN Delta (wallClass g false) vacuum (opposite staticLepton) 42
    (restoringFields q true false)

theorem charged_seed_eq (g : Fin 3) (vacuum : VacuumLabel (wallClass g false))
    (q : History) : chargedSeed g vacuum q = seed q :=
  localized_restoring_seed _ vacuum _ charged_channels.1 q true false

private theorem reference_wait (either : Bool) (requests : RequestsField Delta)
    (reference : Wt × Wt) (ticks : ℕ) :
    (valueStep either requests)^[ticks] (fun _ => (reference, reference)) =
      fun _ => (reference, reference) := by
  have hstep : valueStep either requests (fun _ => (reference, reference)) =
      fun _ => (reference, reference) := by
    funext x
    cases h : exchange either (requests x) <;>
      simp [valueStep, PMAction.OpenReferenceFlow.streamShift, h]
  induction ticks with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, hstep]

/-- Admission of the occupied input and the conditional typed route share
the same receiver seed. The class-shifted export is retained when a fresh
copy of the post-crossing payload reloads the reference-only receiver. -/
theorem occupied_bank_cycle (g : Fin 3) (vacuum : VacuumLabel (wallClass g false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History)
    (hLive : liveExit either q = true) (r₁ r₂ : Fin 8) :
    let receiver := chargedSeed g vacuum q
    let reference := (frame 0 r₁, frame 0 r₂)
    let ports := liftPorts reference (restoringPayload g a sign) receiver.2.2.2
    let atExit := (valueStep either receiver.2.1)^[2] ports
    let extracted := exchangeLive (42 : Fin Delta) (atExit, reference)
    let waited := (valueStep either receiver.2.1)^[2 * Delta - 2] extracted.1
    let reloaded := exchangeLive (42 : Fin Delta) (waited, restoringPayload g a sign)
    Admitted (occupiedInput (wallClass g false) vacuum (opposite staticLepton)) ∧
      extracted.1 = (fun _ => (reference, reference)) ∧
      extracted.2 = restoringPayload g a sign ∧
      runClassShift extracted.2 = encode g (opposite staticLepton) (signedAxis (a + 2) sign) ∧
      reloaded = (ports, reference) := by
  dsimp only
  rw [charged_seed_eq]
  have he := extract_values either q hLive (frame 0 r₁, frame 0 r₂)
    (restoringPayload g a sign)
  rw [he, reference_wait]
  exact ⟨occupiedInput_admitted _ _ _, rfl, rfl,
    cross_then_class_shift g staticLepton a sign rfl,
    reload_values q _ _⟩

/-- At address one the incoming class is 2, so the typed payload can
always be distinguished from the class-0 prepared reference. -/
theorem address_one_payload_ne_reference (a : Fin 4) (sign : Fin 2) (r₁ r₂ : Fin 8) :
    restoringPayload 1 a sign ≠ (frame 0 r₁, frame 0 r₂) := by
  unfold restoringPayload
  rw [runGappedCrossing_encode 1 staticLepton a sign rfl]
  intro h
  have hclass := frame_class_unique 2 0 1 r₁ (congrArg Prod.fst h)
  exact (by decide : (2 : Fin 3) ≠ 0) hclass

/-- At address two both values are in the vector class. The typed
comparison is silent precisely when both prepared lanes match. -/
theorem address_two_payload_eq_reference_iff (a : Fin 4) (sign : Fin 2) (r₁ r₂ : Fin 8) :
    restoringPayload 2 a sign = (frame 0 r₁, frame 0 r₂) ↔
      r₁ = 1 ∧ r₂ = signedAxis (a + 2) sign := by
  unfold restoringPayload
  rw [runGappedCrossing_encode 2 staticLepton a sign rfl]
  change (frame 0 1, frame 0 (signedAxis (a + 2) sign)) = (frame 0 r₁, frame 0 r₂) ↔ _
  constructor
  · intro h
    exact ⟨(frame_injective 0 _ _ (congrArg Prod.fst h)).symm,
      (frame_injective 0 _ _ (congrArg Prod.snd h)).symm⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A booked exchange changes its ordered arriving pair exactly when the
two values differ. There are two bank operations in the cycle. This
counts their typed comparisons before a readout on native doublets. -/
def bankChanges (payload reference : Wt × Wt) : ℕ :=
  [(payload, reference), (reference, payload)].countP fun v => decide (v.swap ≠ v)

theorem bank_changes (payload reference : Wt × Wt) :
    bankChanges payload reference = if payload = reference then 0 else 2 := by
  unfold bankChanges
  by_cases h : payload = reference
  · subst reference
    simp
  · have h₁ : (reference, payload) ≠ (payload, reference) := by
      intro he
      exact h (congrArg Prod.snd he)
    have h₂ : (payload, reference) ≠ (reference, payload) := Ne.symm h₁
    simp [h, h₁, h₂]

theorem address_one_bank_changes (a : Fin 4) (sign : Fin 2) (r₁ r₂ : Fin 8) :
    bankChanges (restoringPayload 1 a sign) (frame 0 r₁, frame 0 r₂) = 2 := by
  simp [bank_changes, address_one_payload_ne_reference]

theorem address_two_bank_changes (a : Fin 4) (sign : Fin 2) (r₁ r₂ : Fin 8) :
    bankChanges (restoringPayload 2 a sign) (frame 0 r₁, frame 0 r₂) =
      if r₁ = 1 ∧ r₂ = signedAxis (a + 2) sign then 0 else 2 := by
  simp [bank_changes, address_two_payload_eq_reference_iff]

/-- The four booked reflections are charged by their existing absolute
root-step ledger, evaluated on the carrier retained by the bank. -/
def classLedger (g : Fin 3) (a : Fin 4) (sign : Fin 2) : List ℕ :=
  HeavyCrossingCost.stepLedger classShiftWord (restoringPayload g a sign)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
/-- The first restoring address has two unit steps per signed axis.
At the second, axis 1 has three unit steps and every other axis has one.
The remaining entries are zero at both addresses. -/
theorem restoring_class_ledger : ∀ (a : Fin 4) (sign : Fin 2),
    (classLedger 1 a sign).count 1 = 2 ∧
    (classLedger 1 a sign).count 0 = 2 ∧
    (classLedger 2 a sign).count 1 = (if a = 1 then 3 else 1) ∧
    (classLedger 2 a sign).count 0 = (if a = 1 then 1 else 3) := by
  decide +kernel

/-- Replaying the two successful receiver guard decisions as the two
requests on one bank-root probe gives a returning trial. Extraction
and reload themselves take separate arriving pairs. -/
theorem restoring_guard_replay_returns (either : Bool) (q : History)
    (hLive : liveExit either q = true) (x : TwoSiteHandoff.Site × TwoSiteHandoff.Carrier) :
    let step := fun (request : Bool) y => if request then TwoSiteHandoff.receiverRoot y else y
    step (exchange either q.2) (step (exchange either q.1) x) = x := by
  rw [live_exit, Bool.and_eq_true] at hLive
  simp only [hLive.1, hLive.2, ite_true]
  exact TwoSiteHandoff.receiverRoot_involutive x

end PMElementaryParticles.OccupiedBankedRestoring
