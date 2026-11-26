import PMKAutomaton.ClockSymmetry

/-!
# Normal form of the full aligned clock-root stabilizer

The clock-adapted chart puts the two projections of cu on axis zero
in their own factors. A D4 root at pairing one with that axis is e0 plus
or minus one transverse axis. This finite root fact forces any full
stabilizer element to permute and sign the three spatial axes in each
factor. The two signs on the clock axes agree.
-/
noncomputable section
namespace PMKAutomaton.ClockSymmetry
open Matrix PMSubstrate.Lattices PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment

private theorem pair_symmetry (x y : V) : pairing x y = pairing y x := by
  simpa only [pairing, PMSubstrate.Lattices.gram_symmetric] using
    Matrix.dotProduct_transpose_mulVec PMSubstrate.Lattices.gram x y

private theorem pair_add_right (x y z : V) : pairing x (y+z) = pairing x y + pairing x z := by
  simp [pairing, Matrix.mulVec_add, dotProduct_add]

private theorem pair_neg_right (x y : V) : pairing x (-y) = -pairing x y := by
  simp [pairing, Matrix.mulVec_neg, dotProduct_neg]

theorem weyl_pair (w : Weyl) (x y : V) : pairing (w.val x) (w.val y) = pairing x y := by
  have h := weyl_norm w (x+y)
  rw [map_add] at h
  simp only [pair_add_left, pair_add_right, weyl_norm w,
    pair_symmetry (w.val y) (w.val x), pair_symmetry y x] at h
  omega

def timeIndex (internal : Bool) : Fin 8 := if internal then 4 else 0

def spatialIndex (internal : Bool) (i : Fin 3) : Fin 8 :=
  ⟨i.val + (if internal then 5 else 1), by split_ifs <;> omega⟩

def signed (negative : Bool) (z : V) : V := if negative then -z else z

def clockRoot (internal : Bool) (i : Fin 3) : V := fun j =>
  (axis (timeIndex internal) j + axis (spatialIndex internal i) j) / 2

theorem clockRoot_certificate : ∀ (b : Bool) (i : Fin 3),
    (2 : ℤ) • clockRoot b i = axis (timeIndex b) + axis (spatialIndex b i) ∧
    clockRoot b i ∈ (if b then internalRoots else spacetimeRoots) ∧
    pairing (clockRoot b i) PMSubstrate.ClockPlane.cu = 1 := by decide +kernel

/-- Exhaustive root certificate: the whole factor, not a selected reflection subgroup. -/
theorem clock_root_axes : ∀ (b t : Bool), ∀ r ∈ (if b then internalRoots else spacetimeRoots),
    pairing r PMSubstrate.ClockPlane.cu = (if t then -1 else 1) →
      ∃ (j : Fin 3) (negative : Bool),
        (2 : ℤ) • r - signed t (axis (timeIndex b)) = signed negative (axis (spatialIndex b j)) := by
  decide +kernel

theorem time_axes {reverse : Bool} (w : fullGroup reverse) (t : Bool)
    (ht : w.val.val PMSubstrate.ClockPlane.cu = signed t PMSubstrate.ClockPlane.cu) :
    ∀ b, w.val.val (axis (timeIndex b)) = signed t (axis (timeIndex b)) := by
  have h0 : w.val.val (axis 0) = signed t (axis 0) := by
    rw [← clock_chart.2.1, w.property.1, ht]
    cases t <;> simp [signed, sectorProjection, Matrix.mulVec_neg]
  intro b
  cases b
  · exact h0
  · change w.val.val (axis 4) = signed t (axis 4)
    rw [← clock_chart.2.2, map_sub, map_smul, ht, h0]
    cases t <;> simp only [signed, Bool.false_eq_true, ite_false, ite_true, smul_neg] <;> abel

theorem spatial_axis_image {reverse : Bool} (w : fullGroup reverse) (t : Bool)
    (ht : w.val.val PMSubstrate.ClockPlane.cu = signed t PMSubstrate.ClockPlane.cu)
    (b : Bool) (i : Fin 3) :
    ∃ (j : Fin 3) (negative : Bool),
      w.val.val (axis (spatialIndex b i)) = signed negative (axis (spatialIndex b j)) := by
  have hc := clockRoot_certificate b i
  have hm : w.val.val (clockRoot b i) ∈ (if b then internalRoots else spacetimeRoots) := by
    cases b
    · exact maps_spacetime w.val w.property.1 _ hc.2.1
    · exact maps_internal w.val w.property.1 _ hc.2.1
  have hp := weyl_pair w.val (clockRoot b i) PMSubstrate.ClockPlane.cu
  rw [hc.2.2, ht] at hp
  have hr : pairing (w.val.val (clockRoot b i)) PMSubstrate.ClockPlane.cu =
      (if t then -1 else 1) := by
    cases t <;> simp only [signed, Bool.false_eq_true, ite_false, ite_true, pair_neg_right] at hp ⊢ <;> omega
  obtain ⟨j, n, hj⟩ := clock_root_axes b t _ hm hr
  refine ⟨j, n, ?_⟩
  have he := congrArg w.val.val hc.1
  rw [map_smul, map_add, time_axes w t ht b] at he
  rw [← hj, he]
  abel

/-! ## The finite signed-frame normal form -/

abbrev SpatialFrame := (Fin 3 → Fin 3) × (Fin 3 → Bool)

def ValidFrame (f : SpatialFrame) : Prop := Function.Injective f.1

instance (f : SpatialFrame) : Decidable (ValidFrame f) := by unfold ValidFrame; infer_instance

def frameAxis (b : Bool) (f : SpatialFrame) (i : Fin 3) : V :=
  signed (f.2 i) (axis (spatialIndex b (f.1 i)))

theorem spatial_axes_gram : ∀ (b : Bool) (i j : Fin 3),
    pairing (axis (spatialIndex b i)) (axis (spatialIndex b j)) = if i=j then 4 else 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem frame_injective_from_pairing : ∀ (b : Bool) (p : Fin 3 → Fin 3) (n : Fin 3 → Bool),
    (∀ i j, pairing (frameAxis b (p,n) i) (frameAxis b (p,n) j) = if i=j then 4 else 0) →
      Function.Injective p := by decide +kernel

theorem spatial_frames {reverse : Bool} (w : fullGroup reverse) (t : Bool)
    (ht : w.val.val PMSubstrate.ClockPlane.cu = signed t PMSubstrate.ClockPlane.cu) :
    ∃ fS fI : SpatialFrame, ValidFrame fS ∧ ValidFrame fI ∧
      ∀ (b : Bool) (i : Fin 3),
        w.val.val (axis (spatialIndex b i)) = frameAxis b (if b then fI else fS) i := by
  choose j n hj using (fun (b : Bool) (i : Fin 3) => spatial_axis_image w t ht b i)
  have hf (b : Bool) : ValidFrame (j b, n b) := by
    apply frame_injective_from_pairing b (j b) (n b)
    intro i k
    change pairing (signed (n b i) (axis (spatialIndex b (j b i))))
      (signed (n b k) (axis (spatialIndex b (j b k)))) = _
    rw [← hj b i, ← hj b k, weyl_pair, spatial_axes_gram]
  exact ⟨(j false,n false), (j true,n true), hf false, hf true,
    fun b i => by cases b <;> exact hj _ i⟩

def frameAxes (t : Bool) (fS fI : SpatialFrame) (i : Fin 8) : V :=
  if h0 : i.val = 0 then signed t (axis 0)
  else if h4 : i.val = 4 then signed t (axis 4)
  else if hs : i.val < 4 then frameAxis false fS ⟨i.val-1, by omega⟩
  else frameAxis true fI ⟨i.val-5, by omega⟩

theorem axes_normal_form {reverse : Bool} (w : fullGroup reverse) (t : Bool)
    (ht : w.val.val PMSubstrate.ClockPlane.cu = signed t PMSubstrate.ClockPlane.cu)
    (fS fI : SpatialFrame)
    (hf : ∀ (b : Bool) (i : Fin 3),
      w.val.val (axis (spatialIndex b i)) = frameAxis b (if b then fI else fS) i) :
    ∀ i, w.val.val (axis i) = frameAxes t fS fI i := by
  intro i
  fin_cases i
  · simpa [frameAxes, timeIndex] using time_axes w t ht false
  · simpa [frameAxes, spatialIndex] using hf false 0
  · simpa [frameAxes, spatialIndex] using hf false 1
  · simpa [frameAxes, spatialIndex] using hf false 2
  · simpa [frameAxes, timeIndex] using time_axes w t ht true
  · simpa [frameAxes, spatialIndex] using hf true 0
  · simpa [frameAxes, spatialIndex] using hf true 1
  · simpa [frameAxes, spatialIndex] using hf true 2

/-- Four times every lattice vector expands in the eight doubled axes. -/
theorem axes_expand (z : V) : ∑ i, chart z i • axis i = (4 : ℤ) • z := by
  have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℤ => M *ᵥ z) chart_inverse.1
  rw [← Matrix.mulVec_mulVec] at h
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at h
  ext i
  have hi := congrFun h i
  simpa [chart, axis, mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm] using hi

theorem linear_ext_axes {f g : V →ₗ[ℤ] V}
    (h : ∀ i, f (axis i) = g (axis i)) : f = g := by
  apply LinearMap.ext
  intro z
  have he : (4 : ℤ) • f z = (4 : ℤ) • g z := by
    rw [← map_smul, ← map_smul, ← axes_expand, map_sum, map_sum]
    simp only [map_smul, h]
  ext i
  have hi := congrFun he i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  omega

def frameMatrix (t : Bool) (fS fI : SpatialFrame) : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => frameAxes t fS fI j i

/-- Integrality of the E8 action constrains the two discriminant signs together. -/
theorem normal_form_integral {reverse : Bool} (w : fullGroup reverse) (t : Bool)
    (fS fI : SpatialFrame) (hf : ∀ i, w.val.val (axis i) = frameAxes t fS fI i) :
    ∀ i j, (frameMatrix t fS fI * chartMatrix) i j % 4 = 0 := by
  intro i j
  have h := congrArg w.val.val (axes_expand (basis j))
  rw [map_sum, map_smul] at h
  simp only [map_smul, hf] at h
  have hi := congrFun h i
  have he : (frameMatrix t fS fI * chartMatrix) i j = 4 * w.val.val (basis j) i := by
    simpa [frameMatrix, chart, basis, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hi
  rw [he]
  omega

end PMKAutomaton.ClockSymmetry
