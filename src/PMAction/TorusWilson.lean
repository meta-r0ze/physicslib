import PMAction.ConcreteFermion
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Wilson kernel on the `L⁴` torus with link phases

`PMConstants.UnitTransferWitness` takes its certificates from `tools/unit_transfer_certificate.py`,
which builds the Hermitian Wilson kernel `H = (1 ⊗ γ₅)(D − M)` on an `L⁴` torus. This module states
that kernel in Lean, for any link values, and identifies the script's spin matrices with the
library's.

* `wilsonD`, `wilsonH`: with the site hop `T_μ` (`T_μ(x, x + μ̂) = U_μ(x)`) and the Wilson
  projectors `−½(r − γ_μ)`, `−½(r + γ_μ)`:
  `D = (4r − M)·1 + Σ_μ (T_μ ⊗ (−½)(r − γ_μ) + T_μᴴ ⊗ (−½)(r + γ_μ))`, `H = (1 ⊗ γ₅) D`. This is the
  script's `build` (diagonal `4r − M`, forward hop `−½(r − γ_μ)` with phase `e^{2πi f}`, backward
  hop `−½(r + γ_μ)` with the conjugate phase), as a block matrix on `site × spin`.
* `wilsonH_hermitian`: `H` is Hermitian whenever the `γ_μ` and `γ₅` are Hermitian and `γ₅`
  anticommutes with each `γ_μ`, for any link values (`γ₅`-Hermiticity of `D`).
* `script_gamma0_eq` … `script_gamma2_eq`, `script_gamma3_eq`, `script_gamma5_eq`: the script's `γ_j = i β αⱼ`
  (`j = 0, 1, 2`), `γ₃ = β`, and `γ₀γ₁γ₂γ₃ = Γ` (`ConcreteFermion.gamma`): the script uses the
  library's representation. `script_hermitian`, `script_anticomm` give the hypotheses of
  `wilsonH_hermitian`.

The link phases are `PMAction.TorusFlux`. That the script assembles `wilsonH` from those links in
its site order is a code-review statement, recorded in `PMConstants.UnitTransferWitness`.
-/

noncomputable section
namespace PMAction.TorusWilson
open Matrix Complex ConcreteFermion Kronecker

section Kernel
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Forward Wilson projector `−½(r − γ_μ)`. -/
def fwd (g : Fin 4 → Spin) (r : ℝ) (μ : Fin 4) : Spin := (-(1 / 2 : ℂ)) • ((r : ℂ) • 1 - g μ)

/-- Backward Wilson projector `−½(r + γ_μ)`. -/
def bwd (g : Fin 4 → Spin) (r : ℝ) (μ : Fin 4) : Spin := (-(1 / 2 : ℂ)) • ((r : ℂ) • 1 + g μ)

/-- The Wilson operator with site hops `T μ`. -/
def wilsonD (T : Fin 4 → Matrix S S ℂ) (g : Fin 4 → Spin) (r M : ℝ) : Matrix (S × Fin 4) (S × Fin 4) ℂ :=
  ((4 * r - M : ℝ) : ℂ) • 1 + ∑ μ, (T μ ⊗ₖ fwd g r μ + (T μ)ᴴ ⊗ₖ bwd g r μ)

/-- The Hermitian Wilson kernel `(1 ⊗ γ₅) D`. -/
def wilsonH (T : Fin 4 → Matrix S S ℂ) (g : Fin 4 → Spin) (g5 : Spin) (r M : ℝ) :
    Matrix (S × Fin 4) (S × Fin 4) ℂ :=
  ((1 : Matrix S S ℂ) ⊗ₖ g5) * wilsonD T g r M

theorem fwd_adj (g : Fin 4 → Spin) (g5 : Spin) (r : ℝ) (μ : Fin 4) (hg : (g μ)ᴴ = g μ)
    (hac : g5 * g μ = -(g μ * g5)) : (fwd g r μ)ᴴ * g5 = g5 * bwd g r μ := by
  simp only [fwd, bwd, conjTranspose_smul, conjTranspose_sub, conjTranspose_one, hg,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, hac, star_neg, star_div₀, star_one, star_ofNat, Complex.star_def,
    Complex.conj_ofReal]
  module

theorem bwd_adj (g : Fin 4 → Spin) (g5 : Spin) (r : ℝ) (μ : Fin 4) (hg : (g μ)ᴴ = g μ)
    (hac : g5 * g μ = -(g μ * g5)) : (bwd g r μ)ᴴ * g5 = g5 * fwd g r μ := by
  simp only [fwd, bwd, conjTranspose_smul, conjTranspose_add, conjTranspose_one, hg,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, hac, star_neg, star_div₀, star_one, star_ofNat, Complex.star_def,
    Complex.conj_ofReal]
  module

theorem hop_term (T : Matrix S S ℂ) (F B g5 : Spin) (hF : Fᴴ * g5 = g5 * B)
    (hB : Bᴴ * g5 = g5 * F) :
    (T ⊗ₖ F + Tᴴ ⊗ₖ B)ᴴ * ((1 : Matrix S S ℂ) ⊗ₖ g5) =
      ((1 : Matrix S S ℂ) ⊗ₖ g5) * (T ⊗ₖ F + Tᴴ ⊗ₖ B) := by
  rw [conjTranspose_add, conjTranspose_kronecker, conjTranspose_kronecker,
    conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul,
    ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, hF, hB]
  exact add_comm _ _

/-- **The Wilson kernel is Hermitian** for Hermitian `γ_μ`, `γ₅` with `γ₅` anticommuting. -/
theorem wilsonH_hermitian (T : Fin 4 → Matrix S S ℂ) (g : Fin 4 → Spin) (g5 : Spin) (r M : ℝ)
    (hg : ∀ μ, (g μ)ᴴ = g μ) (h5 : g5ᴴ = g5) (hac : ∀ μ, g5 * g μ = -(g μ * g5)) :
    (wilsonH T g g5 r M).IsHermitian := by
  unfold IsHermitian wilsonH
  rw [conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one, h5]
  unfold wilsonD
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_one, conjTranspose_sum,
    Matrix.add_mul, Matrix.mul_add, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · rw [show star (((4 * r - M : ℝ)) : ℂ) = ((4 * r - M : ℝ) : ℂ) from Complex.conj_ofReal _,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · exact Finset.sum_congr rfl fun μ _ =>
      hop_term _ _ _ _ (fwd_adj g g5 r μ (hg μ) (hac μ)) (bwd_adj g g5 r μ (hg μ) (hac μ))

end Kernel

/-! ## The script's spin matrices are the library's -/

/-- `tools/unit_transfer_certificate.py`'s `gammas()`: `[[0, −iσ_j], [iσ_j, 0]]` and `[[0, 1], [1, 0]]`. -/
def scriptGamma : Fin 4 → Spin := ![
  !![0, 0, 0, -I; 0, 0, -I, 0; 0, I, 0, 0; I, 0, 0, 0],
  !![0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0],
  !![0, 0, -I, 0; 0, 0, 0, I; I, 0, 0, 0; 0, -I, 0, 0],
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]]

set_option maxHeartbeats 1000000 in
/-- **The script's spatial gammas are `i β αⱼ`.** -/
theorem script_gamma0_eq : scriptGamma 0 = I • (beta * alpha 0) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [scriptGamma, beta, alpha]

set_option maxHeartbeats 1000000 in
theorem script_gamma1_eq : scriptGamma 1 = I • (beta * alpha 1) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [scriptGamma, beta, alpha]

set_option maxHeartbeats 1000000 in
theorem script_gamma2_eq : scriptGamma 2 = I • (beta * alpha 2) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [scriptGamma, beta, alpha]

/-- **The script's fourth gamma is `β`.** -/
theorem script_gamma3_eq : scriptGamma 3 = beta := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [scriptGamma, beta]

set_option maxHeartbeats 1000000 in
/-- **The script's `γ₅ = γ₀γ₁γ₂γ₃` is the library's `Γ`.** -/
theorem script_gamma5_eq :
    scriptGamma 0 * scriptGamma 1 * scriptGamma 2 * scriptGamma 3 = gamma := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [scriptGamma, gamma, mul_apply, Fin.sum_univ_four]

set_option maxHeartbeats 1000000 in
theorem script_hermitian : ∀ μ, (scriptGamma μ)ᴴ = scriptGamma μ := by
  intro μ; fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [scriptGamma, conjTranspose_apply]

set_option maxHeartbeats 1000000 in
theorem script_anticomm : ∀ μ, gamma * scriptGamma μ = -(scriptGamma μ * gamma) := by
  intro μ; fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [scriptGamma, gamma, mul_apply, Fin.sum_univ_four]

/-- **The script's kernel is Hermitian for any link values.** -/
theorem script_kernel_hermitian {S : Type*} [Fintype S] [DecidableEq S]
    (T : Fin 4 → Matrix S S ℂ) (r M : ℝ) :
    (wilsonH T scriptGamma gamma r M).IsHermitian :=
  wilsonH_hermitian T scriptGamma gamma r M script_hermitian gamma_hermitian script_anticomm

end PMAction.TorusWilson
