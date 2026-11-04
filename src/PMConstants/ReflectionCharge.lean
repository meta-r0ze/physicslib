import PMAction.RestorationResponse
import PMConstants.PersistentGain
import PMConstants.BudgetReadout

/-!
# The reflection charge rate `c`

`PersistentGain` left the rate `c` at which reflected load is charged to the scalar ledger open
("Deriving `c` remains open"). With the budget's readout (`BudgetReadout`) and Paper II's
response scaling, it is fixed.

* `reflected_response`: a reflected amplitude `√R · ψ` has comparison response `R` times that of
  `ψ` (Paper II `RestorationResponse.response_smul`): reflected load scales with the reflected
  power fraction.
* `charge_rate`: restoring the reflected part of a complete repair therefore costs `R` times the
  complete repair's readout, which is `3` (`BudgetReadout.budget_readout`). So `c = 3`, in ledger
  units per unit reflected fraction.
* `gain_at_three`: with `c = 3`, the unique largest persistent gain `g*` lies within
  `3·10⁻⁸/23 < 1.4·10⁻⁹` of `128/989` (`PersistentGain.persistent_maximum`), so `λ` and `m_H` are
  unchanged at the displayed precision.

Premises: what is reflected is a fraction of the complete repair's displacement (not of a single
label's), and it is restored by the same kind of repair, read out in the same unit.
-/

noncomputable section
namespace PMConstants.ReflectionCharge
open PMAction CommonResponse

/-- **Reflected load scales with the reflected power.** -/
theorem reflected_response {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (ψ : ι → ℂ) (R : ℝ) (hR : 0 ≤ R) :
    stateFlag U (((Real.sqrt R : ℝ) : ℂ) • ψ) = R * stateFlag U ψ := by
  rw [RestorationResponse.response_smul, Complex.normSq_ofReal, Real.mul_self_sqrt hR]

/-- **The charge rate is the complete repair's readout, `3`.** -/
theorem charge_rate (Rep : RepairBudget.ExactRepair) (f : Module.End ℝ BudgetReadout.D →ₗ[ℝ] ℝ)
    (hf : BudgetReadout.FrameIndependent f) (hone : f BudgetReadout.P₁ = 1) (R : ℝ) :
    R * f Rep.K.toLinearMap = 3 * R := by
  rw [BudgetReadout.budget_readout Rep f hf hone]; ring

/-- **At `c = 3` the persistent gain is within `1.4·10⁻⁹` of `128/989`.** -/
theorem gain_at_three :
    ∃ gs : ℝ, PersistentGain.Persistent 3 gs ∧ (∀ g, PersistentGain.Persistent 3 g → g ≤ gs) ∧
      gs < selfCoupling ∧ selfCoupling - gs < 0.0000000014 := by
  obtain ⟨gs, hp, hmax, -, hlt, hclose⟩ := PersistentGain.persistent_maximum (c := 3) (by norm_num)
  exact ⟨gs, hp, hmax, hlt, by linarith⟩

end PMConstants.ReflectionCharge
