import PMElementaryParticles.OccupiedBankedRestoring
import PMKAutomaton.ReceiverCapacity

/-!
# Capacity claims of occupied charged-lepton operations

The receiver uses the capacity of the actual carrier pair above the prepared
reference. Its registered visits are those of the native banked history.
The typed bank comparisons and the E8 root-word activity give additional
counts on their own bookings. Prices for those operations and the selection
of a complete persisting program are still inputs.
-/

noncomputable section

namespace PMElementaryParticles.ProgramCapacity

open PMAction PMKAutomaton RingReceiver RestoringRingHistory RestoringExtraction
open IsolatedExcitation OccupiedBankedRestoring GluedRegister ControlledGluedRegister
open GappedGluedCrossing

/-- The carried capacity relative to the reference in otherwise identical slots. -/
def excessCapacity (capacity : Wt × Wt → ℝ) (reference payload : Wt × Wt) : ℝ :=
  capacity payload - capacity reference

private theorem capacity_ports_lift {n : ℕ} (capacity : Wt × Wt → ℝ)
    (reference payload : Wt × Wt) (ports : PortField n) :
    ReceiverCapacity.capacityPorts (excessCapacity capacity reference)
      (liftPorts reference payload ports) =
        liftPorts 0 (excessCapacity capacity reference payload) ports := by
  funext x
  rcases h : ports x with ⟨live, record⟩
  cases live <;> cases record <;>
    simp [ReceiverCapacity.capacityPorts, liftPorts, excessCapacity, h]

/-- Register the excess capacity during the two occupied receiver visits
and the remaining receiver ticks after extraction. -/
def receiverClaim (g : Fin 3) (vacuum : VacuumLabel (wallClass g false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History)
    (reference : Wt × Wt) (capacity : Wt × Wt → ℝ) : ℝ :=
  let payload := restoringPayload g a sign
  let initial := chargedSeed g vacuum q
  let banked := (extract either q).1
  let ports := fun s : RingReceiver.State Delta =>
    ReceiverCapacity.capacityPorts (excessCapacity capacity reference)
      (liftPorts reference payload s.2.2.2)
  ReceiverCapacity.registeredTrace either initial (ports initial) 2 +
    ReceiverCapacity.registeredTrace either banked (ports banked) (2 * Delta - 2)

theorem receiver_claim (g : Fin 3) (vacuum : VacuumLabel (wallClass g false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History)
    (hLive : liveExit either q = true) (reference : Wt × Wt) (capacity : Wt × Wt → ℝ) :
    receiverClaim g vacuum a sign either q reference capacity =
      2 * excessCapacity capacity reference (restoringPayload g a sign) := by
  unfold receiverClaim
  rw [charged_seed_eq]
  simp only [capacity_ports_lift]
  exact (ReceiverCapacity.banked_restoring_receiver either q hLive
    (excessCapacity capacity reference (restoringPayload g a sign)) (2 * Delta - 2)).trans
      (mul_comm _ _)

/-- The bank comparison unit is billed for each change of the ordered
arriving pair. The arriving pairs come from the typed extraction and reload. -/
def bankClaim (payload reference : Wt × Wt) (unit : ℝ) : ℝ :=
  unit * (bankChanges payload reference : ℝ)

/-- Price the unit and double root displacements separately. -/
def rootClaim (ledger : List ℕ) (unit double : ℝ) : ℝ :=
  unit * (ledger.count 1 : ℝ) + double * (ledger.count 2 : ℝ)

/-- The four swap roots followed by the two pure parity roots, in the
existing gapped crossing's application order. -/
def gappedRoots (g : Fin 3) : List (Wt × Wt) :=
  ([0, 2, 4, 6] : List (Fin 8)).map (fun i => (carrier 0 i, -carrier 0 i)) ++
    [(0, parityRoot (wallClass g false) 0), (0, parityRoot (wallClass g false) 1)]

theorem gapped_roots_execute (g : Fin 3) (payload : Wt × Wt) :
    (gappedRoots g).foldl (fun w r => reflectPair r w) payload =
      runGappedCrossing g payload := rfl

private def rootSteps : List (Wt × Wt) → (Wt × Wt) → List ℕ
  | [], _ => []
  | r :: rs, w => (HeavyCrossingCost.coefficient r w).natAbs ::
      rootSteps rs (reflectPair r w)

/-- Actual successive step magnitudes of the gapped word on the occupied input. -/
def gappedLedger (g : Fin 3) (a : Fin 4) (sign : Fin 2) : List ℕ :=
  rootSteps (gappedRoots g) (encode g staticLepton (signedAxis a sign))

/-- Actual successive step magnitudes of the direct insertion word. -/
def directLedger (a : Fin 4) (sign : Fin 2) : List ℕ :=
  HeavyCrossingCost.stepLedger crossingWord (encode 0 staticLepton (signedAxis a sign))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem direct_ledger_counts : ∀ (a : Fin 4) (sign : Fin 2),
    (directLedger a sign).count 1 = (if a = 0 then 1 else 3) ∧
    (directLedger a sign).count 2 = (if a = 0 ∧ sign = 0 then 1 else 0) ∧
    (directLedger a sign).all (· ≤ 2) = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem gapped_ledger_counts : ∀ (g : Fin 3) (a : Fin 4) (sign : Fin 2),
    (gappedLedger g a sign).count 1 =
      (if a ≠ 0 then 3 else if sign = 1 ∨ g = 2 then 1 else 5) ∧
    (gappedLedger g a sign).count 2 = (if g = 2 ∧ a = 0 ∧ sign = 0 then 1 else 0) ∧
    (gappedLedger g a sign).all (· ≤ 2) = true := by decide +kernel

private theorem class_ledger_double : ∀ (a : Fin 4) (sign : Fin 2),
    (classLedger 1 a sign).count 2 = 0 ∧ (classLedger 2 a sign).count 2 = 0 := by
  decide +kernel

/-- The capacity subtotal covered by the banked receiver, the two booked
typed bank comparisons, and the class shift. Root and bank capacity units
are inputs to their respective bookings. -/
def restoringSubtotal (g : Fin 3) (vacuum : VacuumLabel (wallClass g false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History) (r₁ r₂ : Fin 8)
    (capacity : Wt × Wt → ℝ) (bankUnit rootUnit rootDouble : ℝ) : ℝ :=
  let reference := (frame 0 r₁, frame 0 r₂)
  receiverClaim g vacuum a sign either q reference capacity +
    bankClaim (restoringPayload g a sign) reference bankUnit +
    rootClaim (classLedger g a sign) rootUnit rootDouble

theorem address_one_subtotal (vacuum : VacuumLabel (wallClass 1 false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History) (hLive : liveExit either q = true)
    (r₁ r₂ : Fin 8) (capacity : Wt × Wt → ℝ) (bankUnit rootUnit rootDouble : ℝ) :
    restoringSubtotal 1 vacuum a sign either q r₁ r₂ capacity bankUnit rootUnit rootDouble =
      2 * excessCapacity capacity (frame 0 r₁, frame 0 r₂) (restoringPayload 1 a sign) +
        2 * bankUnit + 2 * rootUnit := by
  unfold restoringSubtotal bankClaim rootClaim
  simp only [receiver_claim 1 vacuum a sign either q hLive, address_one_bank_changes,
    (restoring_class_ledger a sign).1, (class_ledger_double a sign).1,
    Nat.cast_ofNat, Nat.cast_zero, mul_zero, add_zero]
  ring

theorem address_two_subtotal (vacuum : VacuumLabel (wallClass 2 false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History) (hLive : liveExit either q = true)
    (r₁ r₂ : Fin 8) (capacity : Wt × Wt → ℝ) (bankUnit rootUnit rootDouble : ℝ) :
    restoringSubtotal 2 vacuum a sign either q r₁ r₂ capacity bankUnit rootUnit rootDouble =
      2 * excessCapacity capacity (frame 0 r₁, frame 0 r₂) (restoringPayload 2 a sign) +
        (if r₁ = 1 ∧ r₂ = signedAxis (a + 2) sign then 0 else 2) * bankUnit +
        (if a = 1 then 3 else 1) * rootUnit := by
  unfold restoringSubtotal bankClaim rootClaim
  simp only [receiver_claim 2 vacuum a sign either q hLive, address_two_bank_changes,
    (restoring_class_ledger a sign).2.2.1, (class_ledger_double a sign).2,
    Nat.cast_ite, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero]
  ring

/-- When the prepared vector-class reference matches both coordinates,
any capacity readout on that typed pair gives zero excess. The separately
booked class word still contributes its axis-dependent claim. -/
theorem address_two_matched_subtotal (vacuum : VacuumLabel (wallClass 2 false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History) (hLive : liveExit either q = true)
    (capacity : Wt × Wt → ℝ) (bankUnit rootUnit rootDouble : ℝ) :
    restoringSubtotal 2 vacuum a sign either q 1 (signedAxis (a + 2) sign)
        capacity bankUnit rootUnit rootDouble =
      (if a = 1 then 3 else 1) * rootUnit := by
  have he := (address_two_payload_eq_reference_iff a sign 1 (signedAxis (a + 2) sign)).2
    ⟨rfl, rfl⟩
  rw [address_two_subtotal vacuum a sign either q hLive, he]
  simp [excessCapacity]

end PMElementaryParticles.ProgramCapacity
