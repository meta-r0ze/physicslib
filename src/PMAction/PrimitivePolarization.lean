import PMAction.D4MomentumMeasure
import PMAction.FinitePolarizationTensor

/-! A finite polarization sum on N periods of each physical D₄ site generator.
Root integrality certifies wrapping in the derived reciprocal basis. The
Fourier weight is the proved inverse physical torus volume. -/
noncomputable section
namespace PMAction.PrimitivePolarization
open Matrix Real D4Gauge LeadingLog FiniteVertex PolarizationContact
open FinitePolarization D4MomentumMeasure LatticeSiteAction

def rootCoordinates (r : Fin 4 → Fin 3) : Fin 4 → ℤ :=
  let h := (∑ i, vec r i) / 2
  ![vec r 0, vec r 0 + vec r 1, h - vec r 3, h]

/-- Every hopping root has integral coordinates in the existing D₄ basis. -/
theorem root_coordinates : ∀ r ∈ roots, vec r = basisZ *ᵥ rootCoordinates r := by
  decide +kernel

lemma real_root_coordinates (r : Fin 4 → Fin 3) (hr : r ∈ roots) :
    (fun i => (vec r i : ℝ)) = basisR *ᵥ (fun i => (rootCoordinates r i : ℝ)) := by
  have h := root_coordinates r hr
  ext i
  have hi := congrFun h i
  fin_cases i <;> norm_num [basisZ, basisR, mulVec, dotProduct, Fin.sum_univ_four] at hi ⊢ <;> exact_mod_cast hi

lemma root_projection (N : ℕ) (a : ℝ) (k : Grid N)
    (r : Fin 4 → Fin 3) (hr : r ∈ roots) :
    rk r (primitiveMomentum N a k) =
      (2 * Real.pi / a) * ∑ i, (rootCoordinates r i : ℝ) * ((k i).val / (N : ℝ)) := by
  change (fun i => (vec r i : ℝ)) ⬝ᵥ
    (((2 * Real.pi / a) • basisInv.transpose) *ᵥ _) = _
  rw [real_root_coordinates r hr, Matrix.smul_mulVec, dotProduct_smul,
    Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, inv_mul_basis, one_mulVec]
  rw [dotProduct_comm]
  rfl

def rootWinding (N : ℕ) (k q : Grid N) (r : Fin 4 → Fin 3) : ℤ :=
  ∑ i, rootCoordinates r i * winding N k q i

lemma primitive_coordinate_wrap (N : ℕ) [NeZero N] (k q : Grid N) (i : Fin 4) :
    (k i).val / (N : ℝ) + (q i).val / (N : ℝ) =
      ((k+q) i).val / (N : ℝ) + (winding N k q i : ℝ) := by
  have h := coordinate_wrap N (2 * Real.pi) k q i
  simpa [momentum, Real.pi_ne_zero] using h

lemma phase_wrap (N : ℕ) [NeZero N] {a : ℝ} (ha : a ≠ 0)
    (k q : Grid N) (r : Fin 4 → Fin 3) (hr : r ∈ roots) :
    a * rk r (primitiveMomentum N a k + primitiveMomentum N a q) =
      a * rk r (primitiveMomentum N a (k+q)) +
        (rootWinding N k q r : ℝ) * (2 * Real.pi) := by
  rw [rk_add, root_projection N a k r hr, root_projection N a q r hr,
    root_projection N a (k+q) r hr]
  simp only [rootWinding, Int.cast_sum, Int.cast_mul]
  rw [← mul_add, ← Finset.sum_add_distrib]
  simp_rw [← mul_add, primitive_coordinate_wrap N k q]
  simp only [mul_add, Finset.sum_add_distrib]
  field_simp

theorem symbol_wrap (N : ℕ) [NeZero N] {a : ℝ} (ha : a ≠ 0) (k q : Grid N) :
    symbol a (primitiveMomentum N a k + primitiveMomentum N a q) =
      symbol a (primitiveMomentum N a (k+q)) := by
  unfold symbol
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [phase_wrap N ha k q r hr, Real.cos_add_int_mul_two_pi]

theorem leg_wrap (N : ℕ) [NeZero N] {a : ℝ} (ha : a ≠ 0)
    (k q : Grid N) (v : Momentum) :
    leg a (primitiveMomentum N a k + primitiveMomentum N a q) (primitiveMomentum N a q) v (-1) =
      leg a (primitiveMomentum N a (k+q)) (primitiveMomentum N a q) v (-1) := by
  unfold leg
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [phase_wrap N ha k q r hr]
  have he : a * rk r (primitiveMomentum N a (k+q)) +
      (rootWinding N k q r : ℝ) * (2 * Real.pi) + -1 * (a * rk r (primitiveMomentum N a q) / 2) =
      (a * rk r (primitiveMomentum N a (k+q)) + -1 * (a * rk r (primitiveMomentum N a q) / 2)) +
        (rootWinding N k q r : ℝ) * (2 * Real.pi) := by ring
  rw [he, Real.sin_add_int_mul_two_pi]

namespace OnGrid
open FinitePolarizationTensor (basis leg_expand contact_expand)
variable {ι : Type*} [Fintype ι]

def response (kmap : ι → Momentum) (a m : ℝ) (q : Momentum) (u v : Momentum) : ℝ :=
  ∑ k : ι,
    (leg a (kmap k) q u 1 *
      leg a (kmap k) q v 1 /
      (denominator m a (kmap k) *
        denominator m a (kmap k + q)) -
      contact a (kmap k) q u v /
        denominator m a (kmap k))

theorem response_symmetric (kmap : ι → Momentum) (a m : ℝ) (q : Momentum) (u v : Momentum) :
    response kmap a m q u v = response kmap a m q v u := by
  unfold response
  apply Finset.sum_congr rfl
  intro k _
  have hc : contact a (kmap k) q u v =
      contact a (kmap k) q v u := by
    unfold contact
    apply congrArg (fun x : ℝ => x / 6)
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hc]
  ring

theorem response_expand (kmap : ι → Momentum) (a m : ℝ) (q : Momentum) (u v : Momentum) :
    response kmap a m q u v = ∑ i, u i * response kmap a m q (basis i) v := by
  unfold response
  simp_rw [leg_expand a _ _ u, contact_expand a _ _ u]
  simp only [Finset.sum_mul, Finset.sum_div, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_sub, mul_div_assoc, mul_assoc]
  congr 1 <;> apply Finset.sum_comm

def tensor (kmap : ι → Momentum) (a m : ℝ) (q : Momentum) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => response kmap a m q (basis i) (basis j)

/-- The matrix entries reconstruct the supplied response for every pair
of probe directions. -/
theorem response_tensor (kmap : ι → Momentum) (a m : ℝ) (q : Momentum) (u v : Momentum) :
    response kmap a m q u v = u ⬝ᵥ (tensor kmap a m q *ᵥ v) := by
  rw [response_expand]
  change (∑ i, u i * response kmap a m q (basis i) v) =
    ∑ i, u i * (∑ j, tensor kmap a m q i j * v j)
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [response_symmetric, response_expand]
  unfold tensor
  apply Finset.sum_congr rfl
  intro j _
  rw [response_symmetric]
  ring

theorem tensor_symmetric (kmap : ι → Momentum) (a m : ℝ) (q : Momentum) :
    (tensor kmap a m q).transpose = tensor kmap a m q := by
  ext i j
  exact response_symmetric kmap a m q _ _

theorem cancel (kmap : ι → Momentum) (shift : Equiv.Perm ι) {a m : ℝ}
    (ha : a ≠ 0) (hm : 0 < m) (q v : Momentum)
    (hs : ∀ k, symbol a (kmap k + q) = symbol a (kmap (shift k)))
    (hl : ∀ k, leg a (kmap k + q) q v (-1) = leg a (kmap (shift k)) q v (-1)) :
    response kmap a m q q v = 0 := by
  have hd (k) : denominator m a (kmap k + q) = denominator m a (kmap (shift k)) := by
    simp only [denominator, hs]
  have hn (k) := (denominator_pos hm a (kmap k)).ne'
  have ht (k) := regulated_routing ha (kmap k) q v (hn k) (by rw [hd]; exact hn _)
  unfold response
  simp_rw [ht]
  rw [Finset.sum_sub_distrib]
  simp_rw [← leg_reroute, hl, hd]
  exact sub_eq_zero.mpr (Equiv.sum_comp shift
    (fun k => leg a (kmap k) q v (-1) / denominator m a (kmap k))).symm

theorem left_transverse (kmap : ι → Momentum) (shift : Equiv.Perm ι) {a m : ℝ}
    (ha : a ≠ 0) (hm : 0 < m) (q : Momentum)
    (hs : ∀ k, symbol a (kmap k + q) = symbol a (kmap (shift k)))
    (hl : ∀ k v, leg a (kmap k + q) q v (-1) = leg a (kmap (shift k)) q v (-1)) :
    q ᵥ* tensor kmap a m q = 0 := by
  ext j
  change (∑ i, q i * response kmap a m q (basis i) (basis j)) = 0
  rw [← response_expand]
  exact cancel kmap shift ha hm q (basis j) hs (fun k => hl k _)

theorem right_transverse (kmap : ι → Momentum) (shift : Equiv.Perm ι) {a m : ℝ}
    (ha : a ≠ 0) (hm : 0 < m) (q : Momentum)
    (hs : ∀ k, symbol a (kmap k + q) = symbol a (kmap (shift k)))
    (hl : ∀ k v, leg a (kmap k + q) q v (-1) = leg a (kmap (shift k)) q v (-1)) :
    tensor kmap a m q *ᵥ q = 0 := by
  ext i
  change (∑ j, response kmap a m q (basis i) (basis j) * q j) = 0
  simp_rw [response_symmetric kmap a m q (basis i), mul_comm]
  exact congrFun (left_transverse kmap shift ha hm q hs hl) i
end OnGrid

/-- The response tensor on primitive D₄ periods with its geometric Fourier weight. -/
def tensor (N : ℕ) [NeZero N] (a m : ℝ) (q : Grid N) :=
  sampleWeight N a • OnGrid.tensor (primitiveMomentum N a) a m (primitiveMomentum N a q)

/-- Physical Fourier weighting and the tensor give the same response. -/
theorem weighted_response (N : ℕ) [NeZero N] (a m : ℝ) (q : Grid N) (u v : Momentum) :
    sampleWeight N a * OnGrid.response (primitiveMomentum N a) a m
      (primitiveMomentum N a q) u v = u ⬝ᵥ (tensor N a m q *ᵥ v) := by
  rw [OnGrid.response_tensor]
  simp [tensor, Matrix.smul_mulVec, dotProduct_smul]

theorem tensor_symmetric (N : ℕ) [NeZero N] (a m : ℝ) (q : Grid N) :
    (tensor N a m q).transpose = tensor N a m q := by
  simp [tensor, OnGrid.tensor_symmetric]

theorem left_transverse (N : ℕ) [NeZero N] {a m : ℝ} (ha : a ≠ 0) (hm : 0 < m)
    (q : Grid N) : primitiveMomentum N a q ᵥ* tensor N a m q = 0 := by
  have h := OnGrid.left_transverse (primitiveMomentum N a) (Equiv.addRight q)
    ha hm (primitiveMomentum N a q) (symbol_wrap N ha · q) (leg_wrap N ha · q)
  simp only [tensor, Matrix.vecMul_smul, h, smul_zero]

theorem right_transverse (N : ℕ) [NeZero N] {a m : ℝ} (ha : a ≠ 0) (hm : 0 < m)
    (q : Grid N) : tensor N a m q *ᵥ primitiveMomentum N a q = 0 := by
  have h := OnGrid.right_transverse (primitiveMomentum N a) (Equiv.addRight q)
    ha hm (primitiveMomentum N a q) (symbol_wrap N ha · q) (leg_wrap N ha · q)
  simp only [tensor, Matrix.smul_mulVec, h, smul_zero]

end PMAction.PrimitivePolarization
