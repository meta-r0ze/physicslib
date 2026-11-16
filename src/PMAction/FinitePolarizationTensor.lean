import PMAction.FinitePolarization

/-! The finite periodic D₄ scalar-link response as a symmetric transverse tensor.
The tensor retains the same line-averaged vertex, contact and regulator.
Its overall physical normalization and transverse continuum coefficient
remain inputs to the comparison with the continuum shell. -/
noncomputable section
namespace PMAction.FinitePolarizationTensor
open Matrix Real D4Gauge LeadingLog PolarizationContact FinitePolarization

def basis (i : Fin 4) : Momentum := Pi.single i 1

lemma rk_basis (r : Fin 4 → Fin 3) (i : Fin 4) : rk r (basis i) = (vec r i : ℝ) := by
  simp [rk, basis, Pi.single_apply]

lemma leg_expand (a : ℝ) (k q u : Momentum) (side : ℝ) :
    leg a k q u side = ∑ i, u i * leg a k q (basis i) side := by
  unfold leg
  simp only [← mul_div_assoc, ← Finset.sum_div, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [rk_basis]
  have hu : rk r u = ∑ i, (vec r i : ℝ) * u i := rfl
  rw [hu]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma contact_expand (a : ℝ) (k q u v : Momentum) :
    contact a k q u v = ∑ i, u i * contact a k q (basis i) v := by
  unfold contact
  simp only [← mul_div_assoc, ← Finset.sum_div, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [rk_basis]
  have hu : rk r u = ∑ i, (vec r i : ℝ) * u i := rfl
  rw [hu]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def response (N : ℕ) [NeZero N] (a m : ℝ) (q : Grid N) (u v : Momentum) : ℝ :=
  ∑ k : Grid N,
    (leg a (momentum N a k) (momentum N a q) u 1 *
      leg a (momentum N a k) (momentum N a q) v 1 /
      (denominator m a (momentum N a k) *
        denominator m a (momentum N a k + momentum N a q)) -
      contact a (momentum N a k) (momentum N a q) u v /
        denominator m a (momentum N a k))

theorem response_symmetric (N : ℕ) [NeZero N] (a m : ℝ) (q : Grid N) (u v : Momentum) :
    response N a m q u v = response N a m q v u := by
  unfold response
  apply Finset.sum_congr rfl
  intro k _
  have hc : contact a (momentum N a k) (momentum N a q) u v =
      contact a (momentum N a k) (momentum N a q) v u := by
    unfold contact
    apply congrArg (fun x : ℝ => x / 6)
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hc]
  ring

theorem response_expand (N : ℕ) [NeZero N] (a m : ℝ) (q : Grid N) (u v : Momentum) :
    response N a m q u v = ∑ i, u i * response N a m q (basis i) v := by
  unfold response
  simp_rw [leg_expand a _ _ u, contact_expand a _ _ u]
  simp only [Finset.sum_mul, Finset.sum_div, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_sub, mul_div_assoc, mul_assoc]
  congr 1 <;> apply Finset.sum_comm

def tensor (N : ℕ) [NeZero N] (a m : ℝ) (q : Grid N) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => response N a m q (basis i) (basis j)

/-- The matrix entries reconstruct the supplied response for every pair
of probe directions. -/
theorem response_tensor (N : ℕ) [NeZero N] (a m : ℝ) (q : Grid N) (u v : Momentum) :
    response N a m q u v = u ⬝ᵥ (tensor N a m q *ᵥ v) := by
  rw [response_expand]
  change (∑ i, u i * response N a m q (basis i) v) =
    ∑ i, u i * (∑ j, tensor N a m q i j * v j)
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [response_symmetric, response_expand]
  unfold tensor
  apply Finset.sum_congr rfl
  intro j _
  rw [response_symmetric]
  ring

theorem tensor_symmetric (N : ℕ) [NeZero N] (a m : ℝ) (q : Grid N) :
    (tensor N a m q).transpose = tensor N a m q := by
  ext i j
  exact response_symmetric N a m q _ _

theorem left_transverse (N : ℕ) [NeZero N] {a m : ℝ} (ha : a ≠ 0) (hm : 0 < m)
    (q : Grid N) : momentum N a q ᵥ* tensor N a m q = 0 := by
  ext j
  change (∑ i, momentum N a q i * response N a m q (basis i) (basis j)) = 0
  rw [← response_expand]
  exact finite_cancel N ha hm q (basis j)

theorem right_transverse (N : ℕ) [NeZero N] {a m : ℝ} (ha : a ≠ 0) (hm : 0 < m)
    (q : Grid N) : tensor N a m q *ᵥ momentum N a q = 0 := by
  ext i
  change (∑ j, response N a m q (basis i) (basis j) * momentum N a q j) = 0
  simp_rw [response_symmetric N a m q (basis i), mul_comm]
  exact congrFun (left_transverse N ha hm q) i

end PMAction.FinitePolarizationTensor
