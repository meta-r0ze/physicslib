import PMAction.CrossingScale
import PMAction.ExactZeroMode
import PMAction.LightLeakage
import PMAction.WallGapCalibration
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# From full rest energies to the zero-energy wall mass

For a common cyclic crossing rate the gapped block is Hermitian and its
square is scalar. Apply the Schur residual estimate to the full two-wall
Hamiltonian in Euclidean norm. The result bounds the distance from a full
light energy to some reduced energy. Mode counting and matching are
additional steps when reduced-energy intervals overlap.
-/

noncomputable section
namespace PMAction.WallSeesawAccuracy

open Matrix PMAction.WallSeesaw PMAction.CompositeMass PMAction.WallGapCalibration
open scoped InnerProductSpace

/-- For a common nonzero cyclic crossing the inverse of the gapped block
equals the block divided by the squared gap. -/
theorem inverse_eq_scaled (g : ℝ) (hg : g ≠ 0) :
    Ginv (cyclicLink g) = ((g ^ 2 : ℝ) : ℂ)⁻¹ • G (cyclicLink g) := by
  have hY : IsUnit (cyclicLink g).det := by
    simp [cyclicLink, CyclicSeesaw.det_cyc, hg]
  have hInv := (gapped_inverse (cyclicLink g) hY).2
  have hs : ((g ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hg
  calc
    _ = Ginv (cyclicLink g) * (((g ^ 2 : ℝ) : ℂ)⁻¹ •
        (G (cyclicLink g) * G (cyclicLink g))) := by
      rw [cyclic_gap_square, smul_smul, inv_mul_cancel₀ hs, one_smul, mul_one]
    _ = _ := by rw [mul_smul_comm, ← mul_assoc, hInv, one_mul]

/-- An in-gap eigenvalue of the full rest Hamiltonian lies within the
stated relative error of the chiral Schur mass operator's spectrum. -/
theorem full_energy_near_schur (g E : ℝ) (hE : |E| < |g|)
    (D₁ D₂ : Matrix (Fin 3) (Fin 3) ℂ)
    (state : ((Fin 3 ⊕ Fin 3) ⊕ (Fin 3 ⊕ Fin 3)) → ℂ) (hne : state ≠ 0)
    (hFull : ExactZeroMode.H (cyclicLink g) D₁ D₂ *ᵥ state = (E : ℂ) • state)
    (v w : ℝ) (hv0 : 0 ≤ v) (hw0 : 0 ≤ w)
    (hv : ∀ u, ‖(V2 D₁ D₂).toEuclideanLin u‖ ≤ v * ‖u‖)
    (hw : ∀ u, ‖(V2 D₁ D₂)ᴴ.toEuclideanLin u‖ ≤ w * ‖u‖) :
    ∃ e : ℝ, (e : ℂ) ∈ spectrum ℂ
        (-(V2 D₁ D₂ * Ginv (cyclicLink g) * (V2 D₁ D₂)ᴴ)) ∧
      |e - E| ≤ (v * w / (|g| * (|g| - |E|))) * |E| := by
  let x : EuclideanSpace ℂ (Fin 3 ⊕ Fin 3) := WithLp.toLp 2 (state ∘ Sum.inl)
  let z : EuclideanSpace ℂ (Fin 3 ⊕ Fin 3) := WithLp.toLp 2 (state ∘ Sum.inr)
  let gap := G (cyclicLink g)
  let coupling := V2 D₁ D₂
  have hSym : gap.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (CrossingScale.gapped_hermitian _)
  have hSq (u : EuclideanSpace ℂ (Fin 3 ⊕ Fin 3)) :
      gap.toEuclideanLin (gap.toEuclideanLin u) = ((g ^ 2 : ℝ) : ℂ) • u := by
    change (gap.toEuclideanLin ∘ₗ gap.toEuclideanLin) u = _
    rw [← Matrix.toLpLin_mul_same, show gap * gap = ((g ^ 2 : ℝ) : ℂ) • 1 from
      cyclic_gap_square g]
    simp
  have hLight : coupling.toEuclideanLin z = (E : ℂ) • x := by
    apply WithLp.ofLp_injective
    funext i
    have hi := congrFun hFull (Sum.inl i)
    simpa [ExactZeroMode.H, fromBlocks_mulVec, x, z, coupling] using hi
  have hGap : gap.toEuclideanLin z - (E : ℂ) • z = -couplingᴴ.toEuclideanLin x := by
    apply WithLp.ofLp_injective
    funext i
    have hi := congrFun hFull (Sum.inr i)
    simp only [ExactZeroMode.H, fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, Pi.smul_apply] at hi
    change (gap *ᵥ (state ∘ Sum.inr)) i - (E : ℂ) * state (.inr i) =
      -(couplingᴴ *ᵥ (state ∘ Sum.inl)) i
    linear_combination hi
  have hx : x ≠ 0 := by
    intro hx
    have hzBound := LightLeakage.coercive gap.toEuclideanLin hSym g hSq E z
    rw [hGap, hx, map_zero, neg_zero, norm_zero] at hzBound
    have hz : z = 0 := norm_eq_zero.mp (le_antisymm
      (nonpos_of_mul_nonpos_right hzBound (sub_pos.mpr hE)) (norm_nonneg _))
    apply hne
    funext i
    cases i with
    | inl i => exact congrFun (congrArg WithLp.ofLp hx) i
    | inr i => exact congrFun (congrArg WithLp.ofLp hz) i
  have hAdj u t :
      ⟪coupling.toEuclideanLin u, t⟫_ℂ = ⟪u, couplingᴴ.toEuclideanLin t⟫_ℂ := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
  obtain ⟨hS, i, hi⟩ := LightLeakage.schur_eigenvalue_near rfl
    gap.toEuclideanLin hSym g hSq coupling.toEuclideanLin couplingᴴ.toEuclideanLin hAdj
    v w hv0 hw0 hv hw E hE x z hx hLight hGap
  refine ⟨hS.eigenvalues rfl i, ?_, hi⟩
  have hg : g ≠ 0 := abs_pos.mp ((abs_nonneg E).trans_lt hE)
  have hMem := (hS.hasEigenvalue_eigenvalues rfl i).mem_spectrum
  rw [← AlgEquiv.spectrum_eq (Matrix.toLpLinAlgEquiv 2)
    (-(coupling * Ginv (cyclicLink g) * couplingᴴ))]
  convert hMem using 2
  change (-(coupling * Ginv (cyclicLink g) * couplingᴴ)).toEuclideanLin =
    (-((g ^ 2 : ℝ) : ℂ)⁻¹) •
      (coupling.toEuclideanLin ∘ₗ gap.toEuclideanLin ∘ₗ couplingᴴ.toEuclideanLin)
  rw [inverse_eq_scaled g hg, mul_smul_comm, smul_mul_assoc, Matrix.mul_assoc]
  simp [gap]

/-- Exact scalar-shift identity for the common cyclic gap. -/
private theorem gap_shift_product (g E : ℝ) :
    ((E : ℂ) • 1 - G (cyclicLink g)) * ((E : ℂ) • 1 + G (cyclicLink g)) =
      ((E ^ 2 - g ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 3 ⊕ Fin 3) _ ℂ) := by
  rw [sub_mul, mul_add, mul_add, cyclic_gap_square]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul,
    Complex.ofReal_sub, sub_smul, pow_two, Complex.ofReal_mul]
  abel

/-- Exact spectral test within the gap. The small matrix retains the energy
dependence of the Schur complement and its denominator is nonzero. -/
theorem full_energy_iff (g E : ℝ) (hE : |E| < |g|)
    (D₁ D₂ : Matrix (Fin 3) (Fin 3) ℂ) :
    let V := V2 D₁ D₂
    let gap := G (cyclicLink g)
    (E : ℂ) ∈ spectrum ℂ (ExactZeroMode.H (cyclicLink g) D₁ D₂) ↔
      ((E : ℂ) • 1 - ((E ^ 2 - g ^ 2 : ℝ) : ℂ)⁻¹ •
        (V * ((E : ℂ) • 1 + gap) * Vᴴ)).det = 0 := by
  intro V gap
  let A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ := (E : ℂ) • 1
  let D := A - gap
  let c := ((E ^ 2 - g ^ 2 : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    have hs := (sq_lt_sq₀ (abs_nonneg E) (abs_nonneg g)).mpr hE
    rw [sq_abs, sq_abs] at hs
    change ((E ^ 2 - g ^ 2 : ℝ) : ℂ) ≠ 0
    exact_mod_cast (sub_ne_zero.mpr hs.ne : E ^ 2 - g ^ 2 ≠ 0)
  have hRight : D * (c⁻¹ • (A + gap)) = 1 := by
    rw [mul_smul_comm, show D * (A + gap) = c • 1 from gap_shift_product g E,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hInv := Matrix.inv_eq_right_inv hRight
  have hdet : D.det ≠ 0 := by
    have hd := congrArg Matrix.det hRight
    rw [det_mul, det_one] at hd
    intro hz
    simp [hz] at hd
  let : Invertible D := ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)).invertible
  have hBlocks :
      (algebraMap ℂ (Matrix ((Fin 3 ⊕ Fin 3) ⊕ (Fin 3 ⊕ Fin 3)) _ ℂ) E -
        ExactZeroMode.H (cyclicLink g) D₁ D₂) = fromBlocks A (-V) (-Vᴴ) D := by
    ext (i | i) (j | j) <;> simp [Matrix.algebraMap_eq_diagonal, ExactZeroMode.H, A, V, D,
      gap, Matrix.smul_apply, Matrix.one_apply, diagonal_apply]
  rw [spectrum.mem_iff, hBlocks, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    det_fromBlocks₂₂, invOf_eq_nonsing_inv, hInv, mul_eq_zero]
  simp only [hdet, false_or, neg_mul, mul_neg, neg_neg]
  rw [mul_smul_comm, smul_mul_assoc]

end PMAction.WallSeesawAccuracy
