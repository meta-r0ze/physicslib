import PMAction.ReferenceClassRecord
import PMAction.Machine.VectorEvenFrame
import PMAction.Machine.RegisterControl

/-!
# Class recording in an actual vector-carrier even sector

A separate record bank has eight actual vector-class carrier labels. It is
not a tensor factor extracted from the live carrier's unused modes. Its four
even pair modes supply a reference-axis blank and three orthonormal spatial
markers. Existing simple-root words write those markers.
The class-to-spatial-marker assignment is an encoding witness, not a selected
physical axis assignment. The full operation is class-controlled: this control,
the record bank and its blank preparation remain physical admission inputs. The
even markers are not odd matter/readout states; their physical storage role is
part of bank admission. Independent bank relabeling
alone does not supply the control. No event rate or price is selected.
-/
noncomputable section
namespace PMAction.ReferenceRootRecord
open Matrix VectorEvenFrame

/-- Three faithful class markers in the existing four-dimensional even sector. -/
def markers : Matrix C (Fin 3) ℂ := fun v c => embedding v c.succ

theorem markers_isometry : markersᴴ * markers = 1 := by
  ext c d
  have h := congrFun (congrFun isometry c.succ) d.succ
  simpa only [mul_apply, conjTranspose_apply, markers, one_apply, Fin.succ_inj] using h

/-- The clean marker is orthogonal to every written class marker. -/
theorem blank_orthogonal : markersᴴ *ᵥ marker 0 = 0 := by
  have hh : embeddingᴴ *ᵥ marker 0 = Pi.single 0 1 := by
    rw [marker, mulVec_mulVec, isometry, one_mulVec]
  ext c
  have h := congrFun hh c.succ
  simpa [markers, mulVec, dotProduct, conjTranspose_apply] using h

def controlled {L : Type*} (cls : L → Fin 3) : Equiv.Perm (L × C) where
  toFun p := (p.1, axisSwap (cls p.1).succ p.2)
  invFun p := (p.1, axisSwap (cls p.1).succ p.2)
  left_inv p := Prod.ext rfl (axis_swap_twice _ p.2)
  right_inv p := Prod.ext rfl (axis_swap_twice _ p.2)

theorem controlled_involutive {L : Type*} (cls : L → Fin 3) :
    Function.Involutive (controlled cls) := by
  intro p
  exact Prod.ext rfl (axis_swap_twice _ p.2)

/-- Repeating the same record operation unwrites it; no free reset or fresh
blank supply is inferred from the reversible circuit. -/
theorem twice_undoes {L : Type*} [Fintype L] [DecidableEq L]
    (cls : L → Fin 3) (Φ : L × C → ℂ) :
    (controlled cls).permMatrix ℂ *ᵥ ((controlled cls).permMatrix ℂ *ᵥ Φ) = Φ := by
  rw [mulVec_mulVec, RootTransferPhase.permutation_square _ (controlled_involutive cls), one_mulVec]

/-- A supplied record blank paired with any live carrier amplitude. -/
def prepared {L : Type*} (ψ : L → ℂ) : L × C → ℂ :=
  fun p => ψ p.1 * marker 0 p.2

theorem controlled_action {L : Type*} [Fintype L] [DecidableEq L]
    (cls : L → Fin 3) (ψ : L → ℂ) :
    (controlled cls).permMatrix ℂ *ᵥ prepared ψ =
      fun p => ψ p.1 * marker (cls p.1).succ p.2 := by
  rw [permMatrix_mulVec]
  funext p
  rcases p with ⟨l,v⟩
  change ψ l * marker 0 (axisSwap (cls l).succ v) = ψ l * marker (cls l).succ v
  have h := congrFun (write_marker (cls l).succ) v
  rw [permMatrix_mulVec] at h
  exact congrArg (fun z => ψ l * z) h

/-- Exact attachment to the previously proved class-record contract. -/
theorem class_record (ψ : ReferenceClassRecord.Profile) :
    (controlled (fun c : Fin 3 => c)).permMatrix ℂ *ᵥ prepared ψ =
      ReferenceClassRecord.recorded markers ψ := by
  rw [controlled_action]
  funext p
  simp [ReferenceClassRecord.recorded, markers, marker_apply, embedding]

/-- A class-definite pure reference is now characterized using this carrier record. -/
theorem nondisturbing_iff (ψ : ReferenceClassRecord.Profile) (hψ : ψ ≠ 0) :
    ReferenceClassRecord.reduced
      ((controlled (fun c : Fin 3 => c)).permMatrix ℂ *ᵥ prepared ψ) =
      ReferenceClassRecord.pureDensity ψ ↔ ReferenceClassRecord.SingleClass ψ := by
  rw [class_record]
  exact ReferenceClassRecord.nondisturbing_record_iff markers markers_isometry ψ hψ

/-- Actual minimal E8/D4 carrier labels in the three nontrivial glue classes. -/
abbrev Native := Σ c : Fin 3, CarrierEvents.Carrier c

/-- The selector reads the carrier's actual glue class. -/
theorem native_glue (n : Native) :
    PMSubstrate.Channels.glueClass (CarrierEvents.vector n.2) = CarrierEvents.classLabel n.1 :=
  (CarrierEvents.vector_properties n.2).1

def nativeGate : Equiv.Perm (Native × C) := controlled Sigma.fst

theorem carrier_unchanged (p : Native × C) : (nativeGate p).1 = p.1 := rfl

/-- Each branch is a certified word of actual simple-root carrier reflections. -/
theorem native_root_word (p : Native × C) :
    (nativeGate p).2 =
      ((word p.1.1.succ).map (CarrierWeyl.simple 0)).prod p.2 := by
  exact (root_word p.1.1.succ p.2).symm

/-- The root-word record works on every coherent live-carrier profile. -/
theorem native_record (ψ : Native → ℂ) :
    nativeGate.permMatrix ℂ *ᵥ prepared ψ =
      fun p => ψ p.1 * marker p.1.1.succ p.2 := controlled_action Sigma.fst ψ

lemma markers_apply (c : Fin 3) (v : C) : markers v c = marker c.succ v := by
  rw [marker_apply]; rfl

lemma marker_gram (c d : Fin 3) :
    (∑ v, marker c.succ v * star (marker d.succ v)) = if c = d then 1 else 0 := by
  calc
    _ = ∑ v, star (markers v d) * markers v c := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [markers_apply, markers_apply]
      ring
    _ = (1 : Matrix (Fin 3) (Fin 3) ℂ) d c := by
      simpa only [mul_apply, conjTranspose_apply] using congrFun (congrFun markers_isometry d) c
    _ = _ := by simp [Matrix.one_apply, eq_comm]

def reducedNative (Φ : Native × C → ℂ) : Matrix Native Native ℂ :=
  fun n m => ∑ v, Φ (n,v) * star (Φ (m,v))

/-- On actual carrier amplitudes the unread record removes precisely the
cross-class coherence, retaining every within-class carrier component. -/
theorem native_reduced (ψ : Native → ℂ) :
    reducedNative (nativeGate.permMatrix ℂ *ᵥ prepared ψ) =
      fun n m => if n.1 = m.1 then ψ n * star (ψ m) else 0 := by
  rw [native_record]
  ext n m
  unfold reducedNative
  calc
    _ = (ψ n * star (ψ m)) *
        (∑ v, marker n.1.succ v * star (marker m.1.succ v)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [star_mul]
      ring
    _ = _ := by rw [marker_gram]; split_ifs <;> simp

/-- No class-profile encoding or choice of spin state is needed: for any pure
native reference, nondisturbance is equivalent to support in one actual glue class. -/
theorem native_nondisturbing_iff (ψ : Native → ℂ) (hψ : ψ ≠ 0) :
    reducedNative (nativeGate.permMatrix ℂ *ᵥ prepared ψ) = vecMulVec ψ (star ψ) ↔
      ∃ c : Fin 3, ∀ n : Native, ψ n ≠ 0 → n.1 = c := by
  rw [native_reduced]
  constructor
  · intro h
    have hex : ∃ n, ψ n ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hψ (funext hn)
    obtain ⟨n,hn⟩ := hex
    refine ⟨n.1,?_⟩
    intro m hm
    by_contra hcls
    have hh := congrFun (congrFun h m) n
    have hp : ψ m * star (ψ n) ≠ 0 := mul_ne_zero hm (by simpa using hn)
    apply hp
    simpa [vecMulVec, hcls] using hh.symm
  · rintro ⟨c,hc⟩
    ext n m
    by_cases hcls : n.1 = m.1
    · simp [hcls, vecMulVec]
    · by_cases hn : ψ n = 0
      · simp [hcls, hn, vecMulVec]
      · by_cases hm : ψ m = 0
        · simp [hcls, hm, vecMulVec]
        · exact (hcls ((hc n hn).trans (hc m hm).symm)).elim

theorem native_unitary : nativeGate.permMatrix ℂ ∈ unitary (Matrix (Native × C) (Native × C) ℂ) :=
  CarrierResponse.perm_unitary _

/-- Existing occupied-bank machinery implements the complete supplied conditional
permutation, with exact readout on every configuration amplitude. -/
theorem configuration_observed :
    NativeObservation.Obs (IndependentRegisters.embedding (a := Native) (b := C))
      ((RegisterControl.extend nativeGate).permMatrix ℂ) (nativeGate.permMatrix ℂ) :=
  RegisterControl.observed nativeGate

theorem configuration_occupation (q : IndependentRegisters.Configuration Native C) :
    IndependentRegisters.occupied (RegisterControl.extend nativeGate q) =
      IndependentRegisters.occupied q := RegisterControl.occupation_conserved nativeGate q

/-- The new ingredient is genuinely a joint control; independent bank root
relabelings cannot by themselves implement this class record. -/
theorem not_independent_of_classes {L : Type*} (cls : L → Fin 3)
    (l₀ l₁ : L) (h₀ : cls l₀ = 0) (h₁ : cls l₁ = 1)
    (e : Equiv.Perm L) (f : Equiv.Perm C) :
    controlled cls ≠ Equiv.prodCongr e f := by
  intro h
  let v := ActualRootRepair.positive
  have h0 := congrArg (fun g : Equiv.Perm (L × C) => (g (l₀,v)).2) h
  have h1 := congrArg (fun g : Equiv.Perm (L × C) => (g (l₁,v)).2) h
  change axisSwap (cls l₀).succ v = f v at h0
  change axisSwap (cls l₁).succ v = f v at h1
  rw [h₀] at h0
  rw [h₁] at h1
  have hn : axisSwap 1 v ≠ axisSwap 2 v := by decide +kernel
  exact hn (h0.trans h1.symm)

theorem native_not_independent (e : Equiv.Perm Native) (f : Equiv.Perm C) :
    nativeGate ≠ Equiv.prodCongr e f := by
  have h0 : Nonempty (CarrierEvents.Carrier 0) := by
    rw [← Fintype.card_pos_iff, CarrierEvents.carrier_card]; norm_num
  have h1 : Nonempty (CarrierEvents.Carrier 1) := by
    rw [← Fintype.card_pos_iff, CarrierEvents.carrier_card]; norm_num
  obtain ⟨v0⟩ := h0
  obtain ⟨v1⟩ := h1
  exact not_independent_of_classes Sigma.fst ⟨0,v0⟩ ⟨1,v1⟩ rfl rfl e f

end PMAction.ReferenceRootRecord
