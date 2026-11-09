import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# The algebraic core of Osterwalder–Schrader reconstruction

The finite-volume Osterwalder–Schrader (OS) step turns a Euclidean reflection-positive measure into
a physical Hilbert space. The integral measure-theory side of the gauge branch is in
`PMAction.ReciprocalReflection`: the physical reciprocal-link law `gibbs`, the OS form

`osForm F G = ∫ F ω · conj(G (θω)) dgibbs`

with `θ` the site reflection, and the positivity axiom `reflection_positive'` (the diagonal
`osForm F F` is real and non-negative for upper observables). This file supplies the *algebraic*
core that converts those facts into a semi-inner-product:

* `conj_symm_of_real_diag`: a sesquilinear form whose diagonal is real is automatically
  **Hermitian**, `B x y = conj (B y x)` (polarization). Applying it to `osForm` — sesquilinear by
  integral linearity, real diagonal by `reflection_positive'` — makes the OS form Hermitian.

* `osCore`: those facts also make the OS form a `PreInnerProductSpace.Core` — the
  **semi-inner-product** whose inner product is `⟪F,G⟫ = B G F`.
* `os_cauchy_schwarz`: consequently `PreInnerProductSpace.Core`'s inner-product inequality gives
  `‖B y x‖ ≤ √(B x x).re · √(B y y).re`.
* `osCore_normSq_eq`: the core norm-squared is exactly the OS form's diagonal,
  `normSq F = Re (B F F)`, so the **null set** `{F | normSq F = 0}` of the semi-inner-product is
  the kernel of the OS form.
* `osNull_zero` / `osNull_add` / `osNull_smul`: the null set is a **subspace** (closed under `0`,
  `+` and scalar multiplication), packaged as the kernel `osNullSubmodule`.
* `osGram` / `osGram_posSemidef`: the Gram matrix `Mᵢⱼ = B Fⱼ Fᵢ` of a finite family of
  observables is **positive semidefinite** — the finite-dimensional face of reflection positivity.
* `osGramInnerProductSpace`: by `Matrix.PosSemidef.toInnerProductSpace`, `n → ℂ` is the
  **physical Hilbert space** with inner product `⟪x, y⟫ = xᴴ M y`, an isometric model of the span of
the `F`. The full quotient `V ⧸ osNullSubmodule` (for observables not assumed finite/independent): its
mathematical content is assembled here (`osNull_cross` well-definedness, `mem_osNullSubmodule_iff`
positive-definiteness), so the descended form is a genuine inner product; only the
`InnerProductSpace` *instance* plumbing on the quotient is the remaining scaffolding.

The framework here is the standard finite-dimensional OS reconstruction, specialized to the data
`ReciprocalReflection` actually proves. No continuum, infinite-volume or mass-gap claim is made.
-/

set_option linter.style.haveILetI false

noncomputable section
open scoped ComplexOrder
namespace PMAction.OsterwalderSchrader

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **A sesquilinear form with real diagonal is Hermitian.** This is the polarization step of OS
reconstruction: linearity in the first argument, conjugate-linearity in the second, and a real
diagonal force `B x y = conj (B y x)`. -/
theorem conj_symm_of_real_diag (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (hre : ∀ x, (B x x).im = 0) :
    ∀ x y, B x y = star (B y x) := by
  intro x y
  have e1 : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
    rw [hadd₁ x y (x + y), hadd₂ x x y, hadd₂ y x y]
    abel
  have h1 : (B x y).im + (B y x).im = 0 := by
    have h := hre (x + y)
    rw [e1] at h
    simp only [Complex.add_im] at h
    linarith [hre x, hre y, h]
  have hvv : B (Complex.I • y) (Complex.I • y) = B y y := by
    rw [hsmul₁ Complex.I y (Complex.I • y), hsmul₂ Complex.I y y,
      Complex.star_def, Complex.conj_I]
    rw [show Complex.I * (-Complex.I * B y y) = -(Complex.I * Complex.I) * B y y by ring,
      Complex.I_mul_I]
    ring
  have e2 : B (x + Complex.I • y) (x + Complex.I • y) =
      B x x + (-Complex.I) * B x y + Complex.I * B y x + B y y := by
    rw [hadd₁ x (Complex.I • y) (x + Complex.I • y), hadd₂ x x (Complex.I • y),
      hadd₂ (Complex.I • y) x (Complex.I • y), hvv, hsmul₁ Complex.I y x,
      hsmul₂ Complex.I x y, Complex.star_def, Complex.conj_I]
    abel
  have h2 : (B y x).re = (B x y).re := by
    have h := hre (x + Complex.I • y)
    rw [e2] at h
    simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, hre x, hre y, zero_mul, one_mul,
      neg_one_mul, add_zero, zero_add] at h
    linarith
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re]; exact h2.symm
  · simp only [Complex.star_def, Complex.conj_im]
    linarith

/-- **The Osterwalder–Schrader semi-inner-product.** A sesquilinear form with a real, non-negative
diagonal — in particular `ReciprocalReflection.osForm`, whose diagonal is real and non-negative on
upper observables by `reflection_positive'` — is a `PreInnerProductSpace.Core`. The four
reflection-positivity axioms are its defining fields; the inner product is `⟪F,G⟫ = B G F`. -/
@[instance_reducible]
def osCore (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (hpos : ∀ x, 0 ≤ (B x x).re)
    (hreal : ∀ x, (B x x).im = 0) :
    PreInnerProductSpace.Core ℂ V where
  inner x y := B y x
  conj_inner_symm x y := by
    have h := conj_symm_of_real_diag B hadd₁ hadd₂ hsmul₁ hsmul₂ hreal y x
    simpa [Complex.star_def] using h.symm
  re_inner_nonneg x := hpos x
  add_left x y z := hadd₂ z x y
  smul_left x y r := by
    have h := hsmul₂ r y x
    simpa [Complex.star_def] using h

/-- **Cauchy–Schwarz for the OS form.** With `osCore`, `PreInnerProductSpace.Core`'s inner-product
inequality reads `‖B y x‖ ≤ √(B x x).re · √(B y y).re`. -/
theorem os_cauchy_schwarz (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (hpos : ∀ x, 0 ≤ (B x x).re)
    (hreal : ∀ x, (B x x).im = 0) (x y : V) :
    ‖B y x‖ ≤ √(B x x).re * √(B y y).re := by
  let c := osCore B hadd₁ hadd₂ hsmul₁ hsmul₂ hpos hreal
  letI : Inner ℂ V := InnerProductSpace.Core.toPreInner' (c := c)
  letI : Norm V := InnerProductSpace.Core.toNorm (c := c)
  have h := InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℂ) (c := c) x y
  simp only [Norm.norm] at h
  exact h

/-- The **null set** of the OS form is where the (squared) norm vanishes. -/
theorem osCore_normSq_eq (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (hpos : ∀ x, 0 ≤ (B x x).re)
    (hreal : ∀ x, (B x x).im = 0) (x : V) :
    InnerProductSpace.Core.normSq (c := osCore B hadd₁ hadd₂ hsmul₁ hsmul₂ hpos hreal) x
      = (B x x).re := rfl

/-- `0` is null. -/
theorem osNull_zero (B : V → V → ℂ)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y) : B 0 0 = 0 := by
  have := hsmul₁ (0 : ℂ) (0 : V) 0
  simpa using this

/-- **The null set is closed under addition.** If `B x x = B y y = 0` then `B (x+y) (x+y) = 0`.
The cross term vanishes by Cauchy–Schwarz (`os_cauchy_schwarz`). -/
theorem osNull_add (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (hpos : ∀ x, 0 ≤ (B x x).re)
    (hreal : ∀ x, (B x x).im = 0) {x y : V}
    (hx : B x x = 0) (hy : B y y = 0) : B (x + y) (x + y) = 0 := by
  have hxr : (B x x).re = 0 := by rw [hx]; simp
  have hyr : (B y y).re = 0 := by rw [hy]; simp
  have hxy : B x y = 0 := by
    have h := os_cauchy_schwarz B hadd₁ hadd₂ hsmul₁ hsmul₂ hpos hreal y x
    rw [hxr, hyr] at h
    simp only [Real.sqrt_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hyx : B y x = 0 := by
    have h := conj_symm_of_real_diag B hadd₁ hadd₂ hsmul₁ hsmul₂ hreal x y
    rw [hxy] at h
    exact star_eq_zero.mp h.symm
  calc B (x + y) (x + y) = B x (x + y) + B y (x + y) := hadd₁ x y (x + y)
    _ = (B x x + B x y) + (B y x + B y y) := by rw [hadd₂ x x y, hadd₂ y x y]
    _ = 0 := by rw [hx, hxy, hyx, hy]; ring

/-- **The null set is closed under scaling.** -/
theorem osNull_smul (B : V → V → ℂ)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (c : ℂ) {x : V} (hx : B x x = 0) : B (c • x) (c • x) = 0 := by
  rw [hsmul₁ c x (c • x), hsmul₂ c x x]
  simp [hx]

/-- **Cross-null vanishes.** A null vector pairs to `0` with every vector: `B x y = 0` whenever
`B x x = 0`, by Cauchy–Schwarz (`os_cauchy_schwarz`). This is what makes the OS form well-defined
on the quotient `V ⧸ osNullSubmodule`. -/
theorem osNull_cross (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (hpos : ∀ x, 0 ≤ (B x x).re)
    (hreal : ∀ x, (B x x).im = 0) {x y : V} (hx : B x x = 0) : B x y = 0 := by
  have hxr : (B x x).re = 0 := by rw [hx]; simp
  have h := os_cauchy_schwarz B hadd₁ hadd₂ hsmul₁ hsmul₂ hpos hreal y x
  rw [hxr, Real.sqrt_zero, mul_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

/-- **The kernel of the OS form as a `Submodule`.** The null set `{F | B F F = 0}` is closed
under `0`, `+` and scalar multiplication (`osNull_zero`/`osNull_add`/`osNull_smul`), so it is a
`Submodule`. The physical Hilbert space of the OS reconstruction is the quotient
`V ⧸ osNullSubmodule`; assembling the descended inner-product instance on that quotient is the
remaining scaffolding (it needs the `SeparationQuotient`/`Matrix.PosSemidef.toInnerProductSpace`
machinery, scoped in `PMAction/REVIEW-AND-NEXT.md`). -/
def osNullSubmodule (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (hpos : ∀ x, 0 ≤ (B x x).re)
    (hreal : ∀ x, (B x x).im = 0) : Submodule ℂ V where
  carrier := {x | B x x = 0}
  zero_mem' := osNull_zero B hsmul₁
  add_mem' := fun hx hy => osNull_add B hadd₁ hadd₂ hsmul₁ hsmul₂ hpos hreal hx hy
  smul_mem' := fun c _ hx => osNull_smul B hsmul₁ hsmul₂ c hx

/-- **The null set is exactly the kernel.** `x` lies in `osNullSubmodule` iff `B x x = 0`, so the
form descended to `V ⧸ osNullSubmodule` is *positive-definite*: its diagonal vanishes only on the
zero class. Combined with `osNull_cross` (well-definedness), the OS form is a genuine inner product
on the quotient — the physical Hilbert space; only the `InnerProductSpace` *instance* plumbing
remains. -/
theorem mem_osNullSubmodule_iff (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (hpos : ∀ x, 0 ≤ (B x x).re)
    (hreal : ∀ x, (B x x).im = 0) (x : V) :
    x ∈ osNullSubmodule B hadd₁ hadd₂ hsmul₁ hsmul₂ hpos hreal ↔ B x x = 0 := Iff.rfl

/-- The **OS Gram matrix** of a finite family of observables, `Mᵢⱼ = B Fⱼ Fᵢ`, so that the OS
form reads `⟪x, y⟫ = xᴴ M y` (Mathlib's convention, conjugate-linear in the first argument). -/
def osGram (B : V → V → ℂ) {n : Type*} (F : n → V) : Matrix n n ℂ := fun i j => B (F j) (F i)

/-- **The OS Gram matrix is positive semidefinite.** `osCore` makes `V` a (semi-)inner-product
space; the Gram matrix of any finite family is then PSD (`Matrix.posSemidef_gram`). This is the
finite-dimensional face of reflection positivity. -/
theorem osGram_posSemidef (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (hpos : ∀ x, 0 ≤ (B x x).re)
    (hreal : ∀ x, (B x x).im = 0) {n : Type*} [Fintype n] (F : n → V) :
    (osGram B F).PosSemidef := by
  let c := osCore B hadd₁ hadd₂ hsmul₁ hsmul₂ hpos hreal
  letI : SeminormedAddCommGroup V := InnerProductSpace.Core.toSeminormedAddCommGroup (c := c)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c
  change (Matrix.gram ℂ F).PosSemidef
  exact Matrix.posSemidef_gram ℂ F

/-- **The physical Hilbert space, finite-dimensional form.** A finite family of observables carries
the PSD Gram matrix `osGram B F`; `Matrix.PosSemidef.toInnerProductSpace` makes `n → ℂ` the Hilbert
space with inner product `xᴴ M y`. -/
@[instance_reducible]
noncomputable def osGramInnerProductSpace (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₁ : ∀ (a : ℂ) x y, B (a • x) y = a * B x y)
    (hsmul₂ : ∀ (a : ℂ) x y, B x (a • y) = star a * B x y)
    (hpos : ∀ x, 0 ≤ (B x x).re)
    (hreal : ∀ x, (B x x).im = 0) {n : Type*} [Fintype n] (F : n → V) :
    @InnerProductSpace ℂ (n → ℂ) _ ((osGram B F).toSeminormedAddCommGroup
      (osGram_posSemidef B hadd₁ hadd₂ hsmul₁ hsmul₂ hpos hreal F)) :=
  (osGram B F).toInnerProductSpace (osGram_posSemidef B hadd₁ hadd₂ hsmul₁ hsmul₂ hpos hreal F)

end PMAction.OsterwalderSchrader
