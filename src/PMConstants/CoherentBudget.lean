import PMConstants.RepairBudget
import PMAction.CoherentRecordRestoration

/-!
# The scalar budget with Codex's coherent restorer as the repair

Paper II's `CoherentRecordRestoration` (promoted from Codex's former research file
`CoherentReference`) gives an explicit unitary, retained-record restorer of the actual reference
tangent: live and record copies of the lepton-doublet modes, record prepared in the reference, and
the mode exchange. Its protocol is restated here in the same form and plugged into
`PMConstants.RepairBudget.ExactRepair`.

* `coherent_repair`: the exchange protocol is an `ExactRepair`: it returns every displacement,
  not only small ones, exactly to the reference.
* `coherent_budget`: with it, `budget_from_repair` gives `B = 3` and the `λ` window at `N = 23`.

So premise 1 of `RepairBudget` (every small drift is repaired exactly) has a concrete unitary
witness on the actual displacement space. Still premises, as Codex's note says: that the vacuum
implements this record contract (record location, preparation, renewal of the occupied record and
its price), and premise 2, that the budget is the total restoring gain of one complete repair.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PMConstants.CoherentBudget
open Matrix PMAction.CoherentRecordRestoration PMAction.BranchMixerSynthesis
abbrev D := ℝ × ℂ
abbrev Doublet := Fin 2 → ℂ
abbrev Modes := Fin 2 ⊕ Fin 2

def reference : Doublet := ![1, 0]
def tangent (d : D) : Doublet := ![Complex.I * (d.1 : ℂ), Complex.I * d.2]
def displacement (ψ : Doublet) : D := ((ψ 0).im, -Complex.I * ψ 1)
def input (d : D) : Doublet := reference + tangent d

theorem displacement_reference : displacement reference = 0 := by
  simp [displacement, reference]

theorem displacement_input (d : D) : displacement (input d) = d := by
  rcases d with ⟨x, z⟩
  ext <;> simp [displacement, input, reference, tangent]
  ring_nf
  simp

def prepare (d : D) : Modes → ℂ := Sum.elim (input d) reference
def update (ψ : Modes → ℂ) : Modes → ℂ := exchange *ᵥ ψ
def observe (ψ : Modes → ℂ) : D := displacement (fun s => ψ (.inl s))

theorem exact (d : D) : observe (update (prepare d)) = 0 := by
  simp only [observe, update, prepare, exchange_action, Sum.elim_inl]
  exact displacement_reference

/-- **Codex's coherent restorer is an exact repair.** -/
def coherent_repair : RepairBudget.ExactRepair where
  T := Modes → ℂ
  prepare := prepare
  run := update
  observe := observe
  K := ContinuousLinearMap.id ℝ D
  exact_small := Filter.Eventually.of_forall exact
  net_derivative := by
    have h : (fun d : D => d - observe (update (prepare d))) = id := by
      funext d; rw [exact]; simp
    rw [h]; exact hasFDerivAt_id (0 : D)

theorem coherent_budget (B : ℝ)
    (hB : B = LinearMap.trace ℝ D coherent_repair.K.toLinearMap) :
    B = 3 ∧ ((0.1286 : ℚ) < (3 - 1/43) / (23 : ℕ) ∧ (3 - 1/43) / (23 : ℕ) < (0.1300 : ℚ)) :=
  RepairBudget.budget_from_repair coherent_repair B hB

end PMConstants.CoherentBudget
