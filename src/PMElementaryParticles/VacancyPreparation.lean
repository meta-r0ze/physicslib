import PMElementaryParticles.VacancyProjection
import PMAction.CoherentComparisonRepair
import PMAction.ControllerHamiltonian
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Occupied packet preparation by finite hypercharge comparisons

One packet phase makes every occupied channel a nontrivial fifth root of
unity and leaves the sterile direction fixed. Four coherent comparisons
remove the vacancy and give a common amplitude multiplier on every other
channel. The preparation uses the retained minus ports of the comparisons.
-/

noncomputable section
set_option synthInstance.maxSize 512
namespace PMElementaryParticles.VacancyPreparation
open Matrix PMConstants.PacketGaugeActions PMConstants.ChannelOccupancy
open PMElementaryParticles.ProtocolInventory PMAction.CoherentComparisonRepair
open scoped Matrix.Norms.Operator

private def chargeIndex (c : Channels) : ℤ := (tag c).2.2

private def fifthPhase (n : ℤ) : ℂ :=
  Complex.exp ((2 * (Real.pi : ℂ) / 5 * (n : ℂ)) * Complex.I)

private theorem fifthPhase_pow (n : ℤ) : fifthPhase n ^ 5 = 1 := by
  rw [fifthPhase, ← Complex.exp_nat_mul]
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨n, ?_⟩
  push_cast
  ring

private theorem fifthPhase_one_iff (n : ℤ) : fifthPhase n = 1 ↔ 5 ∣ n := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
    have hi := congrArg Complex.im hk
    have hr : (n : ℝ) = 5 * (k : ℝ) := by
      apply (mul_left_cancel₀ Real.pi_ne_zero)
      simp [Complex.mul_im, Complex.mul_re, Complex.I_im, Complex.I_re] at hi
      convert congrArg (fun x : ℝ => (5 / 2) * x) hi using 1 <;> ring
    exact ⟨k, by exact_mod_cast hr⟩
  · rintro ⟨k, rfl⟩
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨k, ?_⟩
    push_cast
    ring

private theorem fifthPhase_channel (c : Channels) :
    fifthPhase (chargeIndex c) = 1 ↔ baseProtocol c = none := by
  rw [fifthPhase_one_iff]
  revert c
  decide +kernel

/-- The same hypercharge parameter is used for the four comparison stages. -/
def phaseStep : ℝ := 6 * Real.pi / 5

private theorem transport_diagonal (j : ℕ) :
    hypercharge ((j : ℝ) * phaseStep) =
      diagonal (fun c => fifthPhase (chargeIndex c) ^ j) := by
  unfold hypercharge
  rw [PMAction.LinkEvolution.transport_eq_exp, VacancyProjection.charge_diagonal,
    ← diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext c
  rw [Pi.coe_exp, fifthPhase, ← Complex.exp_nat_mul, ← Complex.exp_eq_exp_ℂ]
  congr 1
  simp [phaseStep, smul_eq_mul, chargeIndex]
  ring

private theorem fifth_product (z : ℂ) (hz : z ^ 5 = 1) (hne : z ≠ 1) :
    (1 - z) * (1 - z ^ 2) * (1 - z ^ 3) * (1 - z ^ 4) = 5 := by
  have hsum : 1 + z + z ^ 2 + z ^ 3 + z ^ 4 = 0 := by
    apply (mul_left_cancel₀ (sub_ne_zero.mpr hne))
    calc
      (z - 1) * (1 + z + z ^ 2 + z ^ 3 + z ^ 4) = z ^ 5 - 1 := by ring
      _ = (z - 1) * 0 := by rw [hz]; ring
  calc
    _ = 5 - (1 + z + z ^ 2 + z ^ 3 + z ^ 4) +
        (z ^ 5 - 1) * (3 - z ^ 3 - z ^ 4 + z ^ 5) := by ring
    _ = 5 := by rw [hz, hsum]; ring

/-- The four retained branches, from left to right in matrix product order. -/
def filter : M :=
  minus (hypercharge (1 * phaseStep)) * minus (hypercharge (2 * phaseStep)) *
    minus (hypercharge (3 * phaseStep)) * minus (hypercharge (4 * phaseStep))

private theorem minus_diagonal (j : ℕ) :
    minus (hypercharge ((j : ℝ) * phaseStep)) =
      diagonal (fun c => (1 / 2 : ℂ) * (1 - fifthPhase (chargeIndex c) ^ j)) := by
  rw [transport_diagonal, minus, ← diagonal_one, diagonal_sub, ← diagonal_smul]
  rfl

/-- Retaining all four comparison branches prepares the exact occupied
projection, with one common amplitude factor on every occupied channel. -/
theorem filter_eq_projector : filter = (5 / 16 : ℂ) • VacancyProjection.occupied := by
  have h₁ := minus_diagonal 1
  have h₂ := minus_diagonal 2
  have h₃ := minus_diagonal 3
  have h₄ := minus_diagonal 4
  norm_num only [Nat.cast_ofNat, Nat.cast_one, pow_one] at h₁ h₂ h₃ h₄
  unfold filter
  rw [h₁, h₂, h₃, h₄, VacancyProjection.occupied_eq_inventory, ← diagonal_smul]
  simp only [diagonal_mul_diagonal]
  congr 1
  funext c
  let z := fifthPhase (chargeIndex c)
  change (1/2 * (1-z)) * (1/2 * (1-z^2)) * (1/2 * (1-z^3)) * (1/2 * (1-z^4)) =
    (5/16 : ℂ) * (if baseProtocol c = none then 0 else 1)
  by_cases hc : baseProtocol c = none
  · have hz : z = 1 := (fifthPhase_channel c).mpr hc
    simp [hz, hc]
  · have hz : z ≠ 1 := fun h => hc ((fifthPhase_channel c).mp h)
    rw [ite_eq_right hc, mul_one]
    calc
      _ = (1/16 : ℂ) * ((1-z) * (1-z^2) * (1-z^3) * (1-z^4)) := by ring
      _ = _ := by rw [fifth_product z (fifthPhase_pow _) hz]; ring

/-- Each retained branch comes from the existing unitary two-port comparison
on a fresh plus-port input. -/
theorem stage_unitary_and_readout (j : ℕ) (v : Channels → ℂ) :
    let U := hypercharge ((j : ℝ) * phaseStep)
    PMAction.CoherentComparisonRepair.compare U ∈
        unitary (Matrix (Channels ⊕ Channels) (Channels ⊕ Channels) ℂ) ∧
      (PMAction.CoherentComparisonRepair.compare U *ᵥ Sum.elim v 0) ∘ Sum.inr =
        minus U *ᵥ v := by
  intro U
  refine ⟨compare_unitary U (hypercharge_unitary _), ?_⟩
  rw [PMAction.CoherentComparisonRepair.compare, fromBlocks_mulVec]
  simp

/-- The occupied sector is exactly the set of obtainable retained amplitudes. -/
theorem filter_range_iff (v : Channels → ℂ) :
    (∃ u : Channels → ℂ, filter *ᵥ u = v) ↔ VacancyProjection.occupied *ᵥ v = v := by
  rw [filter_eq_projector]
  constructor
  · rintro ⟨u, rfl⟩
    rw [smul_mulVec, mulVec_smul, mulVec_mulVec, VacancyProjection.occupied_idempotent]
  · intro hv
    refine ⟨(16 / 5 : ℂ) • v, ?_⟩
    rw [smul_mulVec, mulVec_smul, hv, smul_smul]
    norm_num

/-- The retained branch has a uniform squared-norm fraction on the
occupied input. This is an amplitude-accounting statement. -/
theorem filter_weight (v : Channels → ℂ) :
    PMAction.CommonResponse.nsq (filter *ᵥ v) =
      (25 / 256 : ℝ) * PMAction.CommonResponse.nsq (VacancyProjection.occupied *ᵥ v) := by
  rw [filter_eq_projector, smul_mulVec, PMAction.ControllerHamiltonian.nsq_smul]
  norm_num [Complex.normSq_apply]

/-- The retained amplitude agrees with the static-light mask on each
encoded static channel. -/
theorem static_filter_entry (g : Fin 3) (c : Channels) (hc : active c = false) :
    filter c c = (5 / 16 : ℂ) * VacancyProjection.staticLight
      (g, ControlledGluedRegister.labelIndex c) (g, ControlledGluedRegister.labelIndex c) := by
  rw [filter_eq_projector, Matrix.smul_apply, smul_eq_mul, VacancyProjection.staticLight_agrees g c hc]

end PMElementaryParticles.VacancyPreparation
