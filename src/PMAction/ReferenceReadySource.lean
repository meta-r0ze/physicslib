import PMAction.ReferenceMarkerSupply

/-!
# A ready incoming record source: shape from the admitted task

In the candidate even carrier bank, a ready local port has even antipodal
parity and zero overlap with each of the three written class markers.
Completeness of `VectorEvenFrame` then forces it into the one-dimensional
blank mode. This derives the profile from an explicit readiness contract;
it does not derive that contract or a physical source from persistence alone.

If that ready incoming field is stationary under the *unwritten transport*
`ReferenceMarkerExport.exportCycle`, its amplitude is constant on each blank
donor orbit. Together with open neighbour routing, this supplies the repeated
root-write protocol without assuming one specified uniform field on all sites.
Different donor orbits may carry different amplitudes.

Stationarity alone is insufficient: a uniform field of an already written
marker is also transport-stationary and fails readiness. The actual task,
even-bank admission, source accessibility/population and native event prices
and clock remain inputs. Nothing identifies this field with a normalized
one-particle state or proves that the full writing host is stationary.
-/
noncomputable section
namespace PMAction.ReferenceReadySource
open Matrix VectorEvenFrame ReferenceMarkerExport

/-- Readiness of this record-bank candidate, stated in its existing parity and tag readouts. -/
def Ready (ψ : C → ℂ) : Prop :=
  (CarrierParity.antipode 0).permMatrix ℂ *ᵥ ψ = ψ ∧
    ReferenceRootRecord.markersᴴ *ᵥ ψ = 0

/-- The even-frame coordinate of the blank channel. -/
def amplitude (ψ : C → ℂ) : ℂ := (VectorEvenFrame.embeddingᴴ *ᵥ ψ) 0

lemma marker_decode (i : Fin 4) :
    VectorEvenFrame.embeddingᴴ *ᵥ marker i = Pi.single i 1 := by
  rw [marker, mulVec_mulVec, VectorEvenFrame.isometry, one_mulVec]

lemma blank_decode (a : ℂ) :
    VectorEvenFrame.embeddingᴴ *ᵥ (a • marker 0) = Pi.single 0 a := by
  rw [mulVec_smul, marker_decode]
  ext i
  by_cases h : i = 0 <;> simp [h]

/-- No even modes remain unaccounted for: zero tag readout leaves precisely the blank. -/
theorem ready_shape (ψ : C → ℂ) (h : Ready ψ) : ψ = amplitude ψ • marker 0 := by
  obtain ⟨x,hx⟩ := (range_iff_even ψ).mpr h.1
  have hd : VectorEvenFrame.embeddingᴴ *ᵥ ψ = x := by
    rw [← hx, mulVec_mulVec, VectorEvenFrame.isometry, one_mulVec]
  have hz (c : Fin 3) : x c.succ = 0 := by
    have ht := congrFun h.2 c
    have hc := congrFun hd c.succ
    change (∑ v, star (VectorEvenFrame.embedding v c.succ) * ψ v) = 0 at ht
    change (∑ v, star (VectorEvenFrame.embedding v c.succ) * ψ v) = x c.succ at hc
    exact hc.symm.trans ht
  have hs : x = Pi.single 0 (x 0) := by
    ext i
    fin_cases i
    · simp
    · simpa using hz 0
    · simpa using hz 1
    · simpa using hz 2
  have ha : amplitude ψ = x 0 := congrFun hd 0
  rw [ha, ← hx, hs]
  rw [marker, ← mulVec_smul]
  congr 1
  ext i
  by_cases h : i = 0 <;> simp [h]

/-- Every scaled blank meets the same readiness readouts. -/
theorem blank_ready (a : ℂ) : Ready (a • marker 0) := by
  constructor
  · rw [mulVec_smul, marker]
    rw [VectorEvenFrame.even_image]
  · rw [mulVec_smul, ReferenceRootRecord.blank_orthogonal, smul_zero]

theorem ready_iff_blank (ψ : C → ℂ) : Ready ψ ↔ ∃ a : ℂ, ψ = a • marker 0 := by
  constructor
  · intro h
    exact ⟨amplitude ψ, ready_shape ψ h⟩
  · rintro ⟨a,rfl⟩
    exact blank_ready a

/-- The blank amplitude is a readout, not a fitted choice. -/
theorem amplitude_blank (a : ℂ) : amplitude (a • marker 0) = a := by
  unfold amplitude
  rw [blank_decode]
  simp

/-- If a local profile is normalized, readiness fixes its magnitude; its common phase remains free. -/
theorem ready_normalized_iff (ψ : C → ℂ) :
    (Ready ψ ∧ CommonResponse.nsq ψ = 1) ↔
      ∃ a : ℂ, Complex.normSq a = 1 ∧ ψ = a • marker 0 := by
  constructor
  · rintro ⟨hr,hn⟩
    obtain ⟨a,rfl⟩ := (ready_iff_blank ψ).mp hr
    refine ⟨a, ?_, rfl⟩
    simpa [ControllerHamiltonian.nsq_smul, ReferenceMarkerSupply.blank_norm] using hn
  · rintro ⟨a,ha,rfl⟩
    exact ⟨blank_ready a, by simp [ControllerHamiltonian.nsq_smul,
      ReferenceMarkerSupply.blank_norm, ha]⟩

section Field
variable {X : Type*}

/-- Stationarity of the incoming reservoir under transport only, with no writing interaction. -/
def TransportFixed (e : Equiv.Perm X) (ψ : X × C → ℂ) : Prop :=
  ∀ p, ψ (exportCycle e p) = ψ p

/-- The amplitude shape at each site follows from its readiness readouts. -/
theorem field_shape (ψ : X × C → ℂ) (hr : ∀ x, Ready (fun v => ψ (x,v))) (x : X) (v : C) :
    ψ (x,v) = amplitude (fun w => ψ (x,w)) * marker 0 v := by
  exact congrFun (ready_shape _ (hr x)) v

/-- On the blank mode the physical export lookup is exactly its three-step donor route. -/
theorem blank_pullback (e : Equiv.Perm X) (a : X → ℂ) (x : X) (v : C) :
    a (exportCycle e (x,v)).1 * marker 0 (exportCycle e (x,v)).2 =
      a ((e ^ (-3 : ℤ)) x) * marker 0 v := by
  rw [export_eq]
  by_cases hv : indicator v 0 = 0
  · simp [routed, marker_apply, hv]
  · simp [routed, blank_lane v hv]

/-- Stationarity fixes the blank amplitude along the donor route, without relating other orbits. -/
theorem donor_stationary (e : Equiv.Perm X) (ψ : X × C → ℂ)
    (hr : ∀ x, Ready (fun v => ψ (x,v))) (hf : TransportFixed e ψ) (x : X) :
    amplitude (fun v => ψ (((e ^ (-3 : ℤ)) x),v)) = amplitude (fun v => ψ (x,v)) := by
  have he : amplitude (fun v => ψ (((e ^ (-3 : ℤ)) x),v)) • marker 0 =
      amplitude (fun v => ψ (x,v)) • marker 0 := by
    funext v
    change _ * marker 0 v = _ * marker 0 v
    calc
      _ = ψ (exportCycle e (x,v)) := by
        rw [field_shape ψ hr]
        exact (blank_pullback e (fun y => amplitude (fun w => ψ (y,w))) x v).symm
      _ = ψ (x,v) := hf (x,v)
      _ = _ := field_shape ψ hr x v
  have hh := congrArg amplitude he
  simpa only [amplitude_blank] using hh

/-- All future blank donors on the local orbit carry the same ready amplitude. -/
theorem donor_orbit (e : Equiv.Perm X) (ψ : X × C → ℂ)
    (hr : ∀ x, Ready (fun v => ψ (x,v))) (hf : TransportFixed e ψ) (o : X) (m : ℕ) :
    amplitude (fun v => ψ ((((e ^ (-3 : ℤ))^m) o),v)) =
      amplitude (fun v => ψ (o,v)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, donor_stationary e ψ hr hf]
    exact ih

/-- Only the readiness and stationary incoming-background contracts are needed
for the initial-mode condition used by the finite-horizon supply theorem. -/
theorem incoming_modes (e : Equiv.Perm X) (ψ : X × C → ℂ)
    (hr : ∀ x, Ready (fun v => ψ (x,v))) (hf : TransportFixed e ψ)
    (o : X) (v : C) (m : ℕ) :
    ψ (((ReferenceMarkerSupply.route e v)^m) o,v) =
      amplitude (fun w => ψ (o,w)) * marker 0 v := by
  rw [field_shape ψ hr]
  by_cases hv : indicator v 0 = 0
  · simp [marker_apply, hv]
  · have he : ReferenceMarkerSupply.route e v = e ^ (-3 : ℤ) := by
      unfold ReferenceMarkerSupply.route
      rw [blank_lane v hv]
    rw [he, donor_orbit e ψ hr hf o m]

end Field

section Supply
variable {X : Type*} [DecidableEq X]

/-- Repeated native writes receive clean ports from a ready stationary reservoir
and open routing. A globally specified uniform field is no longer required. -/
theorem ready_stationary_supply (o : X) (e : Equiv.Perm X)
    (hopen : ReferenceMarkerSupply.NoReturn e o) (classes : ℕ → Fin 3)
    (ψ : X × C → ℂ) (hr : ∀ x, Ready (fun v => ψ (x,v))) (hf : TransportFixed e ψ)
    (t : ℕ) (v : C) :
    ReferenceMarkerSupply.run o e classes t ψ (o,v) =
      amplitude (fun w => ψ (o,w)) * marker 0 v :=
  ReferenceMarkerSupply.finite_supply o e classes t ψ _
    (fun v m _ => incoming_modes e ψ hr hf o v m)
    (fun v m hm _ => ReferenceMarkerSupply.lane_open e o hopen v m (by omega)) t le_rfl v

/-- Population on distinct initial blank donors depends only on the local source
amplitude; no common amplitude on unrelated donor orbits is required. -/
theorem ready_population (o : X) (e : Equiv.Perm X) (ψ : X × C → ℂ)
    (hr : ∀ x, Ready (fun v => ψ (x,v))) (hf : TransportFixed e ψ) (T : ℕ)
    (hclear : ∀ m, 1 ≤ m → m ≤ T → ((e ^ (-3 : ℤ))^m) o ≠ o) :
    ReferenceMarkerSupply.incomingPopulation e o ψ T =
      (T+1) * Complex.normSq (amplitude (fun v => ψ (o,v))) := by
  let a := amplitude (fun v => ψ (o,v))
  have he : ReferenceMarkerSupply.incomingPopulation e o ψ T =
      ReferenceMarkerSupply.incomingPopulation e o (fun p => a * marker 0 p.2) T := by
    unfold ReferenceMarkerSupply.incomingPopulation
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    have hrow : (fun v => ψ ((((e ^ (-3 : ℤ))^n.val) o),v)) = a • marker 0 := by
      funext v
      rw [field_shape ψ hr, donor_orbit e ψ hr hf o n.val]
      rfl
    rw [hrow]
    rfl
  rw [he]
  exact ReferenceMarkerSupply.source_population e o _ a (fun _ _ => rfl) T hclear

end Supply

/-! ## Readiness is a task condition, not a consequence of stationarity alone -/

theorem tag_not_ready : ¬Ready (marker 1) := by
  intro h
  have hh := congrArg (fun ψ => (VectorEvenFrame.embeddingᴴ *ᵥ ψ) (1 : Fin 4))
    (ready_shape _ h)
  rw [marker_decode, blank_decode] at hh
  norm_num [Pi.single_apply] at hh

/-- An already-written uniform tag is stationary under unwritten transport too. -/
theorem tag_transport_fixed {X : Type*} (e : Equiv.Perm X) :
    TransportFixed e (fun p => marker 1 p.2) := by
  intro p
  rw [export_eq]
  rfl

end PMAction.ReferenceReadySource
