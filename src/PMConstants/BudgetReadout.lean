import PMConstants.RepairBudget
import PMAction.CoherentRecordRestoration
import PMConstants.RegulatoryBudget

/-!
# What the scalar budget reads from a repair

`RepairBudget` left one identification: the budget `B` is the total restoring gain (the trace) of
one complete repair. This module replaces "the trace" by two conditions on how any budget reads a
repair, and shows they force the value.

* `repair_derivative_id`: an exact repair's net correction has derivative exactly the identity on
  `D = ℝ × ℂ` (Paper II `net_correction_derivative`). So every readout of the repair is a readout
  of `id_D`.
* `readout_of_identity`: a readout `f` that is **linear** (independent repairs add) and
  **frame-independent** (`f (g K g⁻¹) = f K`, the persistence closure Covariance), counting a repair
  of a **single direction as one unit**, gives `f id = 3`. The proof splits `id` into three line
  projectors and moves each onto the first by a frame change.
* `budget_readout`: so every such readout of any `ExactRepair` is `3`, and the trace is one
  (`trace_is_readout`).
* `single_unit_excluded`: a readout that counts the whole repair as one event (`B = 1`) is
  excluded by the measured `λ` window: the additivity condition does real work.

Record price (`renewal_per_direction_excluded`): the coherent record must keep every restored
direction (`record_dimension_bound`, at least `3`). If renewing it is charged to the same budget at
one unit per direction, spread over the 43 phases, the per-phase charge is at least `3/43`, and
`(3 − 3/43)/23` falls below the window. So the `1/43` credit is **not** the per-direction renewal
of the repair record. (Priced instead at the walk protocol's seed preparation, renewal shifts `λ`
by less than its error; see `WalkTrials`.)

**The clock credit with the same unit** (`ledger_from_readouts`). The clock phase is one real
direction. Re-synchronizing it once per cycle costs one unit under the same readout, and a
phase-invariant charge spread over the 43-phase cycle is `1/43` per phase
(`RegulatoryBudget.clock_credit`). So both terms of `(3 − 1/43)/23` are now readouts in one unit:
the reference repair's `3` and the clock's one direction per cycle.

Premises: linear, frame-independent readout; unit = one restored direction; the clock phase is
re-synchronized once per cycle and charged per phase.
-/

set_option linter.unnecessarySeqFocus false

noncomputable section
namespace PMConstants.BudgetReadout
open Filter Topology PMConstants

abbrev D := ℝ × ℂ

/-- **An exact repair's net correction has derivative the identity.** -/
theorem repair_derivative_id (R : RepairBudget.ExactRepair) : R.K = ContinuousLinearMap.id ℝ D :=
  R.net_derivative.unique
    (PMAction.DifferentialRestoration.net_correction_derivative R.prepare R.run R.observe
      R.exact_small)

/-- Projector onto the real axis. -/
def P₁ : Module.End ℝ D where
  toFun d := (d.1, 0)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- Projector onto the real part of the complex axis. -/
def P₂ : Module.End ℝ D where
  toFun d := (0, (d.2.re : ℂ))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- Projector onto the imaginary part of the complex axis. -/
def P₃ : Module.End ℝ D where
  toFun d := (0, (d.2.im : ℂ) * Complex.I)
  map_add' _ _ := by ext <;> simp <;> ring
  map_smul' _ _ := by ext <;> simp <;> ring

theorem id_split : (LinearMap.id : Module.End ℝ D) = P₁ + P₂ + P₃ := by
  ext ⟨a, z⟩ <;> simp [P₁, P₂, P₃] <;> apply Complex.ext <;> simp

/-- Frame change exchanging the real axis with `Re z`. -/
def σ₂ : D ≃ₗ[ℝ] D where
  toFun d := (d.2.re, ⟨d.1, d.2.im⟩)
  invFun d := (d.2.re, ⟨d.1, d.2.im⟩)
  map_add' _ _ := by ext <;> simp <;> apply Complex.ext <;> simp
  map_smul' _ _ := by ext <;> simp <;> apply Complex.ext <;> simp
  left_inv _ := by ext <;> simp
  right_inv _ := by ext <;> simp

/-- Frame change exchanging the real axis with `Im z`. -/
def σ₃ : D ≃ₗ[ℝ] D where
  toFun d := (d.2.im, ⟨d.2.re, d.1⟩)
  invFun d := (d.2.im, ⟨d.2.re, d.1⟩)
  map_add' _ _ := by ext <;> simp <;> apply Complex.ext <;> simp
  map_smul' _ _ := by ext <;> simp <;> apply Complex.ext <;> simp
  left_inv _ := by ext <;> simp
  right_inv _ := by ext <;> simp

theorem conj₂ : σ₂.toLinearMap ∘ₗ P₁ ∘ₗ σ₂.symm.toLinearMap = P₂ := by
  ext ⟨a, z⟩ <;> simp [σ₂, P₁, P₂] <;> apply Complex.ext <;> simp

theorem conj₃ : σ₃.toLinearMap ∘ₗ P₁ ∘ₗ σ₃.symm.toLinearMap = P₃ := by
  ext ⟨a, z⟩ <;> simp [σ₃, P₁, P₃] <;> apply Complex.ext <;> simp

/-- Frame independence of a readout. -/
def FrameIndependent (f : Module.End ℝ D →ₗ[ℝ] ℝ) : Prop :=
  ∀ (g : D ≃ₗ[ℝ] D) (K : Module.End ℝ D), f (g.toLinearMap ∘ₗ K ∘ₗ g.symm.toLinearMap) = f K

/-- **A linear, frame-independent readout counting one direction as one unit reads `3` from the
identity.** -/
theorem readout_of_identity (f : Module.End ℝ D →ₗ[ℝ] ℝ) (hf : FrameIndependent f)
    (hone : f P₁ = 1) : f LinearMap.id = 3 := by
  have h2 : f P₂ = 1 := by rw [← conj₂, hf, hone]
  have h3 : f P₃ = 1 := by rw [← conj₃, hf, hone]
  rw [id_split, map_add, map_add, hone, h2, h3]; norm_num

/-- **Every such readout of an exact repair is `3`.** -/
theorem budget_readout (R : RepairBudget.ExactRepair) (f : Module.End ℝ D →ₗ[ℝ] ℝ)
    (hf : FrameIndependent f) (hone : f P₁ = 1) : f R.K.toLinearMap = 3 := by
  rw [repair_derivative_id]; exact readout_of_identity f hf hone

/-- **The trace is such a readout.** -/
theorem trace_is_readout :
    FrameIndependent (LinearMap.trace ℝ D) ∧ LinearMap.trace ℝ D P₁ = 1 := by
  refine ⟨fun g K => ?_, ?_⟩
  · rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]; simp
  · have : P₁ = LinearMap.inl ℝ ℝ ℂ ∘ₗ LinearMap.fst ℝ ℝ ℂ := by
      ext ⟨a, z⟩ <;> simp [P₁]
    rw [this, LinearMap.trace_comp_comm']
    simp

/-- **Counting the whole repair as one event is excluded by the `λ` window.** -/
theorem single_unit_excluded : ¬ ((0.1286 : ℝ) < (1 - 1/43) / 23) := by norm_num

/-- **Per-direction renewal of the repair record cannot be the clock credit.** Any renewal charge
of at least `3/43` per phase puts the ledger below the window. -/
theorem renewal_per_direction_excluded (c : ℝ) (hc : 3 / 43 ≤ c) :
    (3 - c) / 23 < 0.1286 := by
  have : (3 - c) / 23 ≤ (3 - 3/43) / 23 := by gcongr
  linarith [show (3 - 3/43 : ℝ) / 23 < 0.1286 by norm_num]

/-- The coherent record keeps at least the three restored directions. -/
theorem record_at_least_three (R : Type*) [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R]
    (T : (D × R) →ₗ[ℝ] (D × R)) (hT : Function.Injective T) (hreset : ∀ x, (T (x, 0)).1 = 0) :
    3 ≤ Module.finrank ℝ R := by
  have := PMAction.CoherentRecordRestoration.record_dimension_bound T hT hreset
  rwa [ReferenceDirections.displacement_dim] at this

/-- **Both ledger terms in one unit.** -/
theorem ledger_from_readouts (R : RepairBudget.ExactRepair) (f : Module.End ℝ D →ₗ[ℝ] ℝ)
    (hf : FrameIndependent f) (hone : f P₁ = 1)
    (clock : Fin PMSubstrate.E8Values.Delta → ℝ) (hinv : ∀ i, clock (finRotate PMSubstrate.E8Values.Delta i) = clock i) (hsum : ∑ i, clock i = 1) :
    (f R.K.toLinearMap - clock 0) / 23 = (3 - 1 / 43) / 23 ∧
      (0.1286 : ℝ) < (3 - 1 / 43) / 23 ∧ (3 - 1 / 43 : ℝ) / 23 < 0.1300 := by
  rw [budget_readout R f hf hone, RegulatoryBudget.clock_credit clock hinv hsum]
  norm_num

end PMConstants.BudgetReadout
