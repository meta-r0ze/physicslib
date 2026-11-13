import PMAction.ParallelTransport
import PMAction.ConnectionRegularity

/-!
# Compactly supported C² connections satisfy the continuum premises

Several limits (`Machine.ReferenceSampling.ref_limit`, `Machine.SummedReference.sum_limit`,
`ScalarTransport.scalar_limit`, `PMConstants.GaugeGroupFactor`, `PMConstants.ReferenceStiffness`)
take as premises a `C^{1,1}` connection (derivative globally Lipschitz) and links cubically
consistent with it. This module derives both for the parallel transports of a C² connection with
compact support.

* `c2_compact_data`: a C² map with compact support has a globally Lipschitz derivative, and the map
  and its derivative are bounded.
* `compact_transport_premises`: for such a skew connection `A`, its unitary transports `T` are
  `CubicConsistent T A x K` at every `x`, with one constant `K`, and `fderiv A` is `L`-Lipschitz
  (`ParallelTransport.transport_consistent` with global bounds).

So the premise "`C^{1,1}` and cubic link consistency" becomes "the links are the transports of a
compactly supported C² connection".
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.CompactTransport
open Matrix

local notation "V" => (Fin 4 → ℝ)
open scoped Matrix.Norms.L2Operator

/-- **A compactly supported C² map: Lipschitz derivative and bounds.** -/
theorem c2_compact_data {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    (∀ x, HasFDerivAt f (fderiv ℝ f x) x) ∧
      (∃ L : ℝ, 0 ≤ L ∧ ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) ∧ (∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ D) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hcd : HasCompactSupport (fderiv ℝ f) := hc.fderiv ℝ
  refine ⟨fun x => (hf.differentiable (by norm_num) x).hasFDerivAt, ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcd hd one_ne_zero
    refine ⟨C, C.2, fun x y => ?_⟩
    simpa only [dist_eq_norm] using hC.dist_le_mul x y
  · obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hc
    exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩
  · obtain ⟨D, hD⟩ := hd.continuous.bounded_above_of_compact_support hcd
    exact ⟨D, (norm_nonneg _).trans (hD 0), hD⟩

lemma K_nonneg {MA D L : ℝ} (hMA : 0 ≤ MA) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    0 ≤ ParallelTransport.K MA D L := by
  unfold ParallelTransport.K
  have h1 : 0 ≤ D + 8 * L := by linarith
  have h2 : 0 ≤ 2 * MA + (2 * MA) ^ 2 / 2 + (2 * MA) ^ 3 * Real.exp (2 * MA) :=
    add_nonneg (add_nonneg (by linarith) (by positivity))
      (mul_nonneg (pow_nonneg (by linarith) 3) (Real.exp_pos _).le)
  exact add_nonneg (add_nonneg (mul_nonneg (by linarith) h1) (mul_nonneg h1 h2)) (by linarith)

/-- **Transports of a compactly supported C² connection meet the continuum premises.** -/
theorem compact_transport_premises {N : ℕ} {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    (hA : ContDiff ℝ 2 A) (hc : HasCompactSupport A) (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s)
    (hTu : ∀ y v s, T y v s ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) :
    ∃ L K : ℝ, 0 ≤ L ∧ 0 ≤ K ∧ (∀ y, HasFDerivAt A (fderiv ℝ A y) y) ∧
      (∀ x y, ‖fderiv ℝ A y - fderiv ℝ A x‖ ≤ L * ‖y - x‖) ∧
      ∀ x, LinkConsistency.CubicConsistent T A x K := by
  obtain ⟨hd, ⟨L, hL0, hL⟩, ⟨MA, hMA, hMAb⟩, ⟨D, hD0, hDb⟩⟩ := c2_compact_data hA hc
  refine ⟨L, ParallelTransport.K MA (4 * D) L, hL0, K_nonneg hMA (by linarith) hL0, hd,
    fun x y => hL y x, fun x => ?_⟩
  refine ParallelTransport.transport_consistent hd hL0 hskew x (fun z₁ z₂ _ _ => hL z₁ z₂) hMA
    (by linarith) (fun z _ => hMAb z) (fun z _ v hv => ?_) T hT0 hTd hTu
  calc ‖fderiv ℝ A z v v‖ ≤ ‖fderiv ℝ A z v‖ * ‖v‖ := (fderiv ℝ A z v).le_opNorm v
    _ ≤ ‖fderiv ℝ A z‖ * ‖v‖ * ‖v‖ := by
        gcongr; exact (fderiv ℝ A z).le_opNorm v
    _ ≤ D * 2 * 2 := by gcongr; exact hDb z
    _ = 4 * D := by ring

end PMAction.CompactTransport
