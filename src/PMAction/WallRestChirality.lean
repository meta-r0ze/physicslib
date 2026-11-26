import PMAction.ExactZeroMode
import PMAction.ChiralityConvention

/-!
# Rest chirality in the full two-wall Hamiltonian

In the native wall basis `(a, d, b, c)`, the negative-chirality density retains
`(d, b)`. Each rest Hamiltonian link couples opposite chiralities, pairing
opposite energies and balancing the chiral weights at nonzero energy.
-/

noncomputable section
namespace PMAction.WallRestChirality
open Matrix

/-- Squared norm in the finite wall or daughter basis. -/
def weight {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

private theorem dot_weight {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    star x ⬝ᵥ x = (weight x : ℂ) := by
  rw [weight, Complex.ofReal_sum, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.normSq_eq_conj_mul_self.symm

private theorem adjoint_pairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (x : ι → ℂ) (y : κ → ℂ) :
    star (Aᴴ *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (A *ᵥ y) := by
  rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]

private theorem opposite_weights {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B : Matrix ι κ ℂ} {u : ι → ℂ} {v : κ → ℂ} {E : ℝ}
    (hE : E ≠ 0) (hu : B *ᵥ v = (E : ℂ) • u) (hv : Bᴴ *ᵥ u = (E : ℂ) • v) :
    weight u = weight v := by
  have h := adjoint_pairing B u v
  rw [hu, hv] at h
  simp only [star_smul, Complex.star_def, Complex.conj_ofReal, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dot_weight] at h
  exact_mod_cast mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hE) h.symm

variable {n : Type*} [Fintype n]

/-- The chiral split of the native `(a, d, b, c)` ordering. -/
abbrev WallMode (n : Type*) := ((n ⊕ n) ⊕ (n ⊕ n)) → ℂ

def positivePart (ψ : WallMode n) : n ⊕ n → ℂ :=
  Sum.elim (fun i => ψ (.inl (.inl i))) (fun i => ψ (.inr (.inr i)))

/-- Retained coordinates of the native negative-chirality density projector. -/
def chargedPart (ψ : WallMode n) : n ⊕ n → ℂ :=
  Sum.elim (fun i => ψ (.inl (.inr i))) (fun i => ψ (.inr (.inl i)))

/-- The native spinor density, in the order of the positive and negative chirality sectors. -/
theorem chargedPart_is_native_density (w : PMAction.ConcreteFermion.Sites → ℂ) :
    let parts (v : PMAction.ConcreteFermion.Sites → ℂ) : WallMode (Fin 2) :=
      Sum.elim
        (Sum.elim (fun i => v (.inl (PMAction.WallSeesaw.ix 0 i)))
          (fun i => v (.inr (PMAction.WallSeesaw.ix 0 i))))
        (Sum.elim (fun i => v (.inr (PMAction.WallSeesaw.ix 1 i)))
          (fun i => v (.inl (PMAction.WallSeesaw.ix 1 i))))
    parts (PMAction.WallChiralCurrent.projector *ᵥ w) =
      Sum.elim (0 : Fin 2 ⊕ Fin 2 → ℂ) (parts w ∘ Sum.inr) := by
  dsimp only
  rw [PMAction.ChiralityConvention.projector_eq_fromBlocks_PL, fromBlocks_mulVec]
  funext i
  rcases i with (i | i) | (i | i) <;> fin_cases i <;>
    norm_num [PMAction.WallSeesaw.ix, PMAction.WeakVertex.PL_eq,
      PMAction.ConcreteFermion.gamma, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply]

private theorem chiral_equations_iff {Y D₁ D₂ : Matrix n n ℂ} {ψ : WallMode n} {z : ℂ} :
    let B := fromBlocks (0 : Matrix n n ℂ) D₁ D₂ᴴ (-Yᴴ)
    PMAction.ExactZeroMode.H Y D₁ D₂ *ᵥ ψ = z • ψ ↔
      B *ᵥ chargedPart ψ = z • positivePart ψ ∧
        Bᴴ *ᵥ positivePart ψ = z • chargedPart ψ := by
  simp only [PMAction.ExactZeroMode.H, PMAction.CompositeSchur.V2, PMAction.WallSeesaw.G,
    fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_mulVec, zero_mulVec, zero_add]
  constructor
  · intro h
    constructor <;> (funext i; rcases i with i | i)
    · simpa [positivePart, chargedPart, Function.comp_def] using congrFun h (.inl (.inl i))
    · simpa [positivePart, chargedPart, Function.comp_def, add_comm] using congrFun h (.inr (.inr i))
    · simpa [positivePart, chargedPart, Function.comp_def] using congrFun h (.inl (.inr i))
    · simpa [positivePart, chargedPart, Function.comp_def, add_comm] using congrFun h (.inr (.inl i))
  · rintro ⟨hp, hm⟩
    funext i
    rcases i with (i | i) | (i | i)
    · simpa [positivePart, chargedPart, Function.comp_def] using congrFun hp (.inl i)
    · simpa [positivePart, chargedPart, Function.comp_def] using congrFun hm (.inl i)
    · simpa [positivePart, chargedPart, Function.comp_def, add_comm] using congrFun hm (.inr i)
    · simpa [positivePart, chargedPart, Function.comp_def, add_comm] using congrFun hp (.inr i)

/-- Reverse the negative-chirality coordinates in the native `(a, d, b, c)` order. -/
def chiralityFlip (ψ : WallMode n) : WallMode n :=
  Sum.elim
    (Sum.elim (fun i => ψ (.inl (.inl i))) (fun i => -ψ (.inl (.inr i))))
    (Sum.elim (fun i => -ψ (.inr (.inl i))) (fun i => ψ (.inr (.inr i))))

omit [Fintype n] in
@[simp] theorem positivePart_chiralityFlip (ψ : WallMode n) :
    positivePart (chiralityFlip ψ) = positivePart ψ := by
  funext i
  cases i <;> rfl

omit [Fintype n] in
@[simp] theorem chargedPart_chiralityFlip (ψ : WallMode n) :
    chargedPart (chiralityFlip ψ) = -chargedPart ψ := by
  funext i
  cases i <;> rfl

/-- The rest Hamiltonian pairs the energy `z` with `-z` by chirality. -/
theorem opposite_energy {Y D₁ D₂ : Matrix n n ℂ} {ψ : WallMode n} {z : ℂ}
    (h : PMAction.ExactZeroMode.H Y D₁ D₂ *ᵥ ψ = z • ψ) :
    PMAction.ExactZeroMode.H Y D₁ D₂ *ᵥ chiralityFlip ψ = (-z) • chiralityFlip ψ := by
  apply chiral_equations_iff.mpr
  have he := chiral_equations_iff.mp h
  simpa [mulVec_neg, neg_smul, smul_neg] using he

/-- The charged fraction of every unit-normalized nonzero rest eigenmode is one half. -/
theorem charged_weight_half {Y D₁ D₂ : Matrix n n ℂ} {ψ : WallMode n} {E : ℝ}
    (hE : E ≠ 0) (hψ : weight ψ = 1)
    (h : PMAction.ExactZeroMode.H Y D₁ D₂ *ᵥ ψ = (E : ℂ) • ψ) :
    weight (chargedPart ψ) = 1 / 2 := by
  obtain ⟨hu, hv⟩ := chiral_equations_iff.mp h
  have heq := opposite_weights hE hu hv
  have hsplit : weight ψ = weight (positivePart ψ) + weight (chargedPart ψ) := by
    simp only [weight, Fintype.sum_sum_type, positivePart, chargedPart, Sum.elim_inl, Sum.elim_inr]
    ring
  linarith

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]

/-- An orthonormal set of columns preserves squared norm on its coefficient space. -/
theorem weight_isometry (U : Matrix a b ℂ) (hU : Uᴴ * U = 1) (x : b → ℂ) :
    weight (U *ᵥ x) = weight x := by
  apply Complex.ofReal_injective
  rw [← dot_weight, ← dot_weight, ← adjoint_pairing U (U *ᵥ x) x,
    mulVec_mulVec, hU, one_mulVec]

end PMAction.WallRestChirality
