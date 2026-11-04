import PMConstants.RegulatoryMaximin
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Three closures for the scalar ledger

**Finite restoration has total gain 3.** `RegulatoryMaximin.full_restore_trace` needed the
regulator to restore within one update. That is not needed. If a restoring map `K` returns every
displacement after finitely many updates, `(1 - K)^n = 0`, so `1 - K` is nilpotent and has zero
trace; then `tr K = dim = 3` (`finite_restore_trace`). Every exact finite-time restorer has the same
total gain.

**The reference is read as an amplitude.** If the reference were read only as an occupation
pattern (a diagonal density on the carriers, pure or mixed), both `T₃` and `Y/2` would commute with
it (`diagonal_reading_keeps_both`), leaving two unbroken neutral directions. The vector reading of
`ReferenceStabilizer` leaves exactly one, `Q`. So the single massive neutral boson requires the
reference to carry phase: the regulator maintains an amplitude, not a population.

**`23 = ν + σ + χ` is the only decomposition.** Among sums of distinct architecture inputs
`D = 4, Δ = 43, ν = 16, N = 32, σ = 5, χ = 2, R_M = 172, L_embed = 31` (Paper I), the only one equal to
`23` is `ν + σ + χ` (`unique_decomposition`). With `RegulatoryMaximin.count_unique` the measured
coupling fixes the count, and this fixes which labels it is, up to the premise that the labels are
a set of distinct architecture inputs.
-/

noncomputable section
namespace PMConstants.ReferenceRestoration
open PMConstants Matrix GeneratorNormalization PacketTraceForm

/-- **Every exact finite-time restorer has total gain 3.** -/
theorem finite_restore_trace (K : (ℝ × ℂ) →ₗ[ℝ] (ℝ × ℂ)) (n : ℕ)
    (hK : (LinearMap.id - K) ^ n = 0) : LinearMap.trace ℝ (ℝ × ℂ) K = 3 := by
  have hnil : IsNilpotent (LinearMap.id - K) := ⟨n, hK⟩
  have ht : LinearMap.trace ℝ (ℝ × ℂ) (LinearMap.id - K) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  rw [map_sub, LinearMap.trace_id, ReferenceDirections.displacement_dim] at ht
  have : ((3 : ℕ) : ℝ) = 3 := by norm_num
  linarith

lemma t3_isDiag : Matrix.IsDiag t3 := by
  unfold t3 weakGen PacketGaugeActions.block
  have hA : (!![(1 / 2 : ℂ), 0; 0, -1 / 2]).IsDiag := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  exact (isDiag_one.kronecker hA).fromBlocks (isDiag_zero.fromBlocks (hA.fromBlocks isDiag_zero))

lemma hyper_isDiag : Matrix.IsDiag hyperGen := by
  unfold hyperGen PacketGaugeActions.charge PacketGaugeActions.block
  refine IsDiag.smul _ ?_
  exact (isDiag_one.smul _).fromBlocks ((isDiag_one.kronecker (isDiag_diagonal _)).fromBlocks
    ((isDiag_one.smul _).fromBlocks (isDiag_diagonal _)))

/-- **An occupation reading keeps both neutral directions.** -/
theorem diagonal_reading_keeps_both (w : PacketGaugeActions.Channels → ℂ) :
    t3 * diagonal w = diagonal w * t3 ∧ hyperGen * diagonal w = diagonal w * hyperGen := by
  constructor
  · rw [← t3_isDiag.diagonal_diag, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext c; ring
  · rw [← hyper_isDiag.diagonal_diag, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext c; ring

/-- `T₃` and `Y/2` are independent: no multiple of one is the other on the reference doublet. -/
theorem neutral_independent (a b : ℂ) (h : a • t3 + b • hyperGen = 0) : a = 0 ∧ b = 0 := by
  have h0 := congrFun (congrFun h (ReferenceAnchor.lepton 0)) (ReferenceAnchor.lepton 0)
  have h1 := congrFun (congrFun h (ReferenceAnchor.lepton 1)) (ReferenceAnchor.lepton 1)
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul,
    ReferenceStabilizer.hyper_lepton] at h0 h1
  simp only [t3, ReferenceStabilizer.weak_lepton] at h0 h1
  norm_num at h0 h1
  exact ⟨by linear_combination h0 - h1, by linear_combination -(h0 + h1)⟩

/-- Paper I's integer architecture inputs. -/
def inputs : Fin 8 → ℕ := ![4, 43, 16, 32, 5, 2, 172, 31]

/-- **`ν + σ + χ` is the only sum of distinct inputs equal to 23.** -/
theorem unique_decomposition (S : Finset (Fin 8)) :
    ∑ i ∈ S, inputs i = 23 ↔ S = {2, 4, 5} := by
  revert S; decide +kernel

end PMConstants.ReferenceRestoration
