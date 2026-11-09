import Mathlib.Data.Fin.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Two-system entanglement and no-signalling

The measurement construction (`PMAction.Measurement`) gives one system and one apparatus. This
module extends it to **two** systems: a joint two-qubit state space, an **entangled** Bell state
with perfect correlations, and the fact that it is not a product state.

* `State2` — a two-qubit state, `Fin 2 → Fin 2 → ℂ`.
* `singlet` — the Bell state `(|01⟩ − |10⟩)/√2`.
* `singlet_normalized` — `‖singlet‖² = 1`.
* `singlet_anticorrelated` — measuring both qubits in the `Z` basis gives **opposite** outcomes
  (`P(0,1) = P(1,0) = 1/2`, `P(0,0) = P(1,1) = 0`): a maximal correlation.
* `singlet_not_product` — the Bell state is **entangled** (not a product state).
-/

noncomputable section
namespace PMAction.Entanglement

/-- A two-qubit (system ⊗ system) state. -/
abbrev State2 := Fin 2 → Fin 2 → ℂ

/-- Squared norm of a two-qubit state. -/
def normSq2 (ψ : State2) : ℝ := ∑ i, ∑ j, Complex.normSq (ψ i j)

/-- `√2` over `ℂ`. -/
def s2 : ℂ := (Real.sqrt 2 : ℂ)

/-- The Bell singlet `(|01⟩ − |10⟩)/√2`. -/
def singlet : State2 := fun i j =>
  if i = 0 ∧ j = 1 then (1 : ℂ) / s2 else if i = 1 ∧ j = 0 then -((1 : ℂ) / s2) else 0

theorem s2_ne_zero : s2 ≠ 0 := by
  unfold s2
  rw [Complex.ofReal_ne_zero]
  exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))

theorem s2_normSq : Complex.normSq s2 = 2 := by
  unfold s2
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem inv_s2_normSq : Complex.normSq ((1 : ℂ) / s2) = 2⁻¹ := by
  rw [Complex.normSq_div, s2_normSq, Complex.normSq_one]; norm_num

/-- **Normalization.** `‖singlet‖² = 1`. -/
theorem singlet_normalized : normSq2 singlet = 1 := by
  simp only [normSq2, singlet, Fin.sum_univ_two, Fin.isValue, Fin.reduceEq, and_true,
    and_false, ite_true, ite_false, Complex.normSq_zero, Complex.normSq_neg,
    inv_s2_normSq]
  norm_num

/-- **Perfect anticorrelation.** In the `Z` basis the two qubits always disagree. -/
theorem singlet_anticorrelated :
    singlet 0 0 = 0 ∧ singlet 1 1 = 0 ∧
      Complex.normSq (singlet 0 1) = 2⁻¹ ∧ Complex.normSq (singlet 1 0) = 2⁻¹ := by
  refine ⟨by simp [singlet, Fin.isValue],
    by simp [singlet, Fin.isValue], ?_, ?_⟩
  · simpa [singlet, Fin.isValue, Fin.reduceEq] using inv_s2_normSq
  · simpa [singlet, Fin.isValue, Fin.reduceEq, Complex.normSq_neg] using inv_s2_normSq

/-- **The Bell state is entangled** — it is not a product `φ ⊗ χ`. -/
theorem singlet_not_product :
    ¬ ∃ φ χ : Fin 2 → ℂ, ∀ i j, singlet i j = φ i * χ j := by
  rintro ⟨φ, χ, h⟩
  have h00 : φ 0 * χ 0 = 0 := by simpa [singlet, Fin.isValue, Fin.reduceEq] using (h 0 0).symm
  have h11 : φ 1 * χ 1 = 0 := by simpa [singlet, Fin.isValue, Fin.reduceEq] using (h 1 1).symm
  have h01 : φ 0 * χ 1 ≠ 0 := by
    have hh := h 0 1
    simp only [singlet, Fin.isValue, Fin.reduceEq, and_self,
      ite_true, ite_false] at hh
    rw [← hh]; exact div_ne_zero one_ne_zero s2_ne_zero
  have h10 : φ 1 * χ 0 ≠ 0 := by
    have hh := h 1 0
    simp only [singlet, Fin.isValue, Fin.reduceEq, and_self,
      ite_true, ite_false] at hh
    rw [← hh]; exact neg_ne_zero.mpr (div_ne_zero one_ne_zero s2_ne_zero)
  rcases mul_eq_zero.mp h00 with h0 | h0
  · exact h01 (by rw [h0, zero_mul])
  · exact h10 (by rw [h0, mul_zero])

/-- Local action `(A ⊗ B) ψ`: `A` on the first system, `B` on the second. -/
def apply (A B : Matrix (Fin 2) (Fin 2) ℂ) (ψ : State2) : State2 :=
  fun i j => ∑ a, ∑ b, A i a * B j b * ψ a b

/-- `Z`-basis projector on outcome `i`. -/
def zProj (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := fun j k => if j = i ∧ k = i then 1 else 0

/-- `X`-basis projectors `|±⟩⟨±|`. -/
def xProj : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => fun _ _ => (2 : ℂ)⁻¹
  | 1 => fun j k => if j = k then (2 : ℂ)⁻¹ else -((2 : ℂ)⁻¹)

/-- The first system's marginal probability `P(0)` when the second is measured with resolution
`B` (a complete family `∑_k B_k = 1`). -/
def marginal0 (B : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : State2) : ℝ :=
  ∑ k, normSq2 (apply (zProj 0) (B k) ψ)

/-- **No-signalling.** The singlet's first-system marginal `P(0)` is `1/2` whether the second
system is measured in the `Z` or the `X` basis — the distant (space-like) choice cannot be read off
locally. (Both families are complete resolutions, `∑_k B_k = 1`; the marginal depends only on the
local projector.) -/
theorem no_signalling_singlet :
    marginal0 zProj singlet = 2⁻¹ ∧ marginal0 xProj singlet = 2⁻¹ := by
  constructor <;>
    simp only [marginal0, normSq2, apply, zProj, xProj, singlet, Fin.sum_univ_two, Fin.isValue,
      Fin.reduceEq, and_self, and_true, and_false, ite_true, ite_false, zero_mul, mul_zero] <;>
    norm_num [s2_normSq]

end PMAction.Entanglement
