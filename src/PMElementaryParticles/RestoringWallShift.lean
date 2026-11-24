import PMElementaryParticles.GappedGluedCrossing
import PMElementaryParticles.MassInsertionTrace
import PMKAutomaton.Machine.BranchPulseContract
import PMAction.CertainTransferRate

/-!
# Encoded class change after the equal-class crossing

The static-to-active gapped crossing keeps the class and lands at address
`g + 2`. The same-label restoring insertion then advances the class on
the active wall and returns to address `g`. The open receiver can carry
the encoded root pair unchanged. A four-reflection word supplies the
separate class change. Its serial timing assumes principal half-pulses
on the schedule's common root clock.
-/

namespace PMElementaryParticles.RestoringWallShift

open GluedRegister ControlledGluedRegister ProtocolInventory GappedGluedCrossing
open PMConstants.PacketGaugeActions

/-- Four glued roots for diagonal triality, in application order. -/
def classShiftWord : List HeavyCrossingCost.Instruction :=
  [(0, 6, 7), (0, 6, 6), (2, 6, 6), (2, 6, 1)]

def runClassShift (w : Wt × Wt) : Wt × Wt :=
  classShiftWord.foldl (fun v r => reflectPair (HeavyCrossingCost.rootPair r) v) w

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
/-- The two factors each advance by triality in place. -/
theorem class_shift_glued : ∀ (x : Fin 3) (a b : Fin 8),
    runClassShift (carrier x a, carrier x b) =
      (triality (carrier x a), triality (carrier x b)) := by
  decide +kernel

private theorem next_wall_class : ∀ (g : Fin 3) (b : Bool),
    wallClass (g + 1) b = wallClass g b + 1 := by decide

/-- Advance the generation address on its current wall, preserving the
protocol channel and the signed carrier index in the transported frame. -/
theorem class_shift_encode (g : Fin 3) (c : Channels) (a : Fin 8) :
    runClassShift (encode g c a) = encode (g + 1) c a := by
  obtain ⟨i, j, h⟩ := encode_glued g c a
  have hshift : runClassShift (encode g c a) =
      (triality (encode g c a).1, triality (encode g c a).2) := by
    rw [h, class_shift_glued]
  rw [hshift]
  cases hc : active c <;> simp [encode, place, hc, frame_succ, next_wall_class]

/-- The two restoring addresses have opposite incidence with the vector
class. The crossing keeps the first class, and the active-wall shift
goes from that class to the second. -/
theorem restoring_class_pairs :
    (wallClass 1 false, wallClass 1 true) = (2, 0) ∧
      (wallClass 2 false, wallClass 2 true) = (0, 1) := by decide

private theorem address_wrap : ∀ g : Fin 3, g + 2 + 1 = g := by decide

/-- Composing the gapped crossing with the same-wall class shift gives the
same-generation endpoint while retaining the crossing's parity action. -/
theorem cross_then_class_shift (g : Fin 3) (c : Channels) (i : Fin 4) (s : Fin 2)
    (hc : active c = false) :
    runClassShift (runGappedCrossing g (encode g c (signedAxis i s))) =
      encode g (opposite c) (signedAxis (i + 2) s) := by
  rw [runGappedCrossing_encode g c i s hc, class_shift_encode, address_wrap]

/-- Transporting the raw gapped output unchanged cannot realize the
same-generation endpoint. Its first carrier still has the incoming class. -/
theorem gapped_payload_ne_endpoint (g : Fin 3) (c : Channels) (i : Fin 4) (s : Fin 2)
    (hc : active c = false) :
    runGappedCrossing g (encode g c (signedAxis i s)) ≠
      encode g (opposite c) (signedAxis (i + 2) s) := by
  rw [runGappedCrossing_encode g c i s hc]
  have hactive : active (opposite c) = true := by rw [opposite_active, hc]; rfl
  intro he
  have h := congrArg Prod.fst he
  simp only [encode, place, hactive, ite_true] at h
  have hclass := frame_class_unique _ _ _ _ h
  exact (show ∀ j : Fin 3, wallClass (j + 2) true ≠ wallClass j true by decide) g hclass

open PMAction.OpenReferenceFlow

/-- Given the gapped wire payload at the entry's live source, the open
exchange trace restores the prepared vector-class reference and routes
that same payload to the live exit. The following explicit class word
then reaches the required encoded endpoint. -/
theorem restoring_exit_then_class_shift (g : Fin 3) (c : Channels) (i : Fin 4) (s : Fin 2)
    (hc : active c = false) (lineState : State ℤ (Wt × Wt))
    (referenceAmplitude referenceLabel : Fin 8) (exitInput : Wt × Wt)
    (hLive : (lineState (-1)).1 = runGappedCrossing g (encode g c (signedAxis i s)))
    (hRef : (lineState 1).2 = (frame 0 referenceAmplitude, frame 0 referenceLabel))
    (hExit : (lineState (-3)).1 = exitInput) :
    let entered := evolution 0 line lineState
    let exited := evolution (-1) line entered
    (entered 0).1 = (frame 0 referenceAmplitude, frame 0 referenceLabel) ∧
      runClassShift (exited (-1)).1 = encode g (opposite c) (signedAxis (i + 2) s) ∧
      (exited (-1)).2 = exitInput := by
  obtain ⟨h₁, _, h₂⟩ := MassInsertionTrace.restoring_entry_exit lineState _ _ _ hLive hRef hExit
  dsimp only
  rw [h₁, h₂]
  exact ⟨rfl, cross_then_class_shift g c i s hc, rfl⟩

/-- The four-reflection word uses eight root quarter-times when each
reflection is realized by a principal half-pulse. -/
theorem class_shift_quarter_times : 2 * classShiftWord.length = 8 := by decide

open WireSchedule in
/-- Booking this separate serial word inside the two node visits rules
out a one-period restoring schedule in the existing template. -/
theorem no_single_period_with_serial_class_shift {ticks : ℕ}
    {p : Premises ticks} {s : Schedule ticks}
    (hs : s ∈ family p) (haddress : p.address ≠ 0)
    (horizon : ticks ≤ PMSubstrate.E8Values.Delta)
    (hbooked : 2 * classShiftWord.length * p.quarterTicks ≤
      p.otherTicks .nodeEnter + p.otherTicks .nodeLeave) : False := by
  obtain ⟨_, hq, hnodes⟩ := MassInsertionTrace.restoring_in_one_period hs haddress horizon
  rw [class_shift_quarter_times, hq] at hbooked
  omega

section Pulse

open Matrix PMAction.BranchMixerSynthesis

/-- Label the second branch by the actual address at the output of the
same-wall class shift. The signed index stays fixed. -/
def pulsePorts : Equiv.Perm (Payload ⊕ Payload) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.addRight (1 : Fin 3)) (Equiv.refl _))

/-- The coherent two-port candidate pairs each incoming address with its
class-shifted address. This uses the supplied branch-rotation law. -/
noncomputable def classPulse (θ : ℝ) : Matrix (Payload ⊕ Payload) (Payload ⊕ Payload) ℂ :=
  (xPulse θ).submatrix pulsePorts.symm pulsePorts.symm

theorem classPulse_unitary (θ : ℝ) : classPulse θ ∈ unitary _ := by
  have hu := xPulse_unitary (n := Payload) θ
  rw [Unitary.mem_iff]
  simp only [classPulse, star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv]
  have h₁ : (xPulse (n := Payload) θ)ᴴ * xPulse θ = 1 := hu.1
  have h₂ : xPulse (n := Payload) θ * (xPulse θ)ᴴ = 1 := hu.2
  rw [h₁, h₂, submatrix_one_equiv]
  exact ⟨rfl, rfl⟩

/-- The coherent cross entry carries the exchange phase on the matching
signed lane and vanishes between different lanes. -/
theorem classPulse_entry (θ : ℝ) (g h : Fin 3) (a b : Fin 8) :
    classPulse θ (.inr (h + 1, b)) (.inl (g, a)) =
      if (h, b) = (g, a) then Complex.I * (Real.sin θ : ℂ) else 0 := by
  have hin : pulsePorts (.inl (g, a)) = .inl (g, a) := rfl
  have hout : pulsePorts (.inr (h, b)) = .inr (h + 1, b) := rfl
  unfold classPulse
  rw [Matrix.submatrix_apply, ← hin, ← hout, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simp [xPulse_blocks, Matrix.one_apply]

/-- The cross-branch weight belongs to the shifted live destination,
with the same signed carrier index. -/
theorem classPulse_weight (θ : ℝ) (g : Fin 3) (a : Fin 8) :
    Complex.normSq (classPulse θ (.inr (g + 1, a)) (.inl (g, a))) = Real.sin θ ^ 2 := by
  have hin : pulsePorts (.inl (g, a)) = .inl (g, a) := rfl
  have hout : pulsePorts (.inr (g, a)) = .inr (g + 1, a) := rfl
  unfold classPulse
  rw [Matrix.submatrix_apply, ← hin, ← hout, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact PMAction.BranchPulseContract.transfer_weight θ (g, a)

/-- Calibrate the class-shifted branch against a certain direct transfer
when the weights and durations of the two principal pulses are supplied. -/
theorem classPulse_rate_ratio (g : Fin 3) (a : Fin 8)
    {θ direct moveTime directTime weight : ℝ}
    (hθ : 0 ≤ θ) (hθp : θ ≤ Real.pi / 2)
    (hd : 0 ≤ direct) (hdp : direct ≤ Real.pi / 2)
    (hm : 0 < moveTime) (hdt : 0 < directTime)
    (hw : Complex.normSq (classPulse θ (.inr (g + 1, a)) (.inl (g, a))) = weight)
    (hcertain : Real.sin direct ^ 2 = 1) :
    (θ / moveTime) / (direct / directTime) =
      (2 * Real.arcsin (Real.sqrt weight) / Real.pi) * (directTime / moveTime) := by
  rw [classPulse_weight] at hw
  exact PMAction.CertainTransferRate.principal_transfer_rate_ratio
    hθ hθp hd hdp hm hdt hw hcertain

end Pulse

end PMElementaryParticles.RestoringWallShift
