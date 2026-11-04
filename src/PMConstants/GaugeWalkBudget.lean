import PMAction.GaugeRecordEmbedding
import PMConstants.RepairBudget

/-!
# The scalar's repair with the weak doublet on its own payload index

An earlier construction (`WalkBudget`, now removed) encoded the reference doublet
directly in the walk spinor's two velocity channels. Codex's review (`WALK-REFERENCE-PROTOCOL.md`)
points out that this does not identify the encoded pair with the weak-isospin doublet, and it
cannot: the spinor's transport commutant is Abelian (shown in the former research file
`TransportCarriers`). This file rebuilds the repair on Codex's
`GaugeRecordEmbedding`: two live/record control channels times a separate payload index
`Fin 2`, the lepton doublet on which weak acts. The embedding is an isometry into spinor × payload
modes, and `γ ⊗ 1` exchanges live and record without touching the payload.

* `swap_controls`: `(exchange ⊗ 1)` swaps the live and record channels of every payload label.
* `run_embedded`: `(γ ⊗ 1)` on the embedded state is the embedded swap (`exchange_intertwining`).
* `gauge_repair`: preparing live = reference + tangent `d` and record = reference, applying
  `γ ⊗ 1` and reading the live channel returns every displacement exactly. This is an
  `ExactRepair`, so `B = 3` (`gauge_budget`).
* `repair_covariant`: the update commutes with every payload matrix `1 ⊗ G`, so it commutes with
  the actual weak and hypercharge actions on the doublet.
* `payload_faithful`: `G ↦ 1 ⊗ G` is injective, so weak acts faithfully on the payload index, unlike
  on transport modes.

This replaces `WalkBudget` as the walk implementation of the scalar's repair. The record is the
record control channel of the payload modes; its renewal is the incoming stream. Inputs as before:
the physical realization of the extra control/payload modes (`4 × 2` complex modes here), the
stream's source and the pulses' prices.
-/

noncomputable section
namespace PMConstants.GaugeWalkBudget
open Matrix PMAction ConcreteFermion GaugeRecordEmbedding
open scoped Kronecker

abbrev D := ℝ × ℂ
abbrev Doublet := Fin 2 → ℂ

def reference : Doublet := ![1, 0]
def tangent (d : D) : Doublet := ![Complex.I * (d.1 : ℂ), Complex.I * d.2]
def input (d : D) : Doublet := reference + tangent d
def displacement (ψ : Doublet) : D := ((ψ 0).im, -Complex.I * ψ 1)

/-- Control `0` is live, control `1` is the record (as in `referenceInput`). -/
def packet (live record : Doublet) : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = 0 then live p.2 else record p.2

theorem swap_controls (live record : Doublet) :
    (GaugeRecordEmbedding.exchange ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ packet live record =
      packet record live := by
  ext ⟨c, j⟩
  fin_cases c <;> fin_cases j <;>
    simp [packet, GaugeRecordEmbedding.exchange, mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, one_apply]

def prepare (d : D) : Fin 4 × Fin 2 → ℂ := embedding *ᵥ packet (input d) reference
def run (v : Fin 4 × Fin 2 → ℂ) : Fin 4 × Fin 2 → ℂ := (gamma ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ v
def liveOf (v : Fin 4 × Fin 2 → ℂ) : Doublet := fun j => ((embedding (n := Fin 2))ᴴ *ᵥ v) (0, j)
def observe (v : Fin 4 × Fin 2 → ℂ) : D := displacement (liveOf v)

theorem run_embedded (live record : Doublet) :
    run (embedding *ᵥ packet live record) = embedding *ᵥ packet record live := by
  unfold run
  rw [mulVec_mulVec, exchange_intertwining, ← mulVec_mulVec, swap_controls]

theorem liveOf_embedded (live record : Doublet) : liveOf (embedding *ᵥ packet live record) = live := by
  funext j
  simp only [liveOf, mulVec_mulVec, embedding_isometry, one_mulVec]
  simp [packet]

theorem exact (d : D) : observe (run (prepare d)) = 0 := by
  unfold observe prepare
  rw [run_embedded, liveOf_embedded]
  simp [displacement, reference]

/-- **The gauge-compatible walk repair is exact.** -/
def gauge_repair : RepairBudget.ExactRepair where
  T := Fin 4 × Fin 2 → ℂ
  prepare := prepare
  run := run
  observe := observe
  K := ContinuousLinearMap.id ℝ D
  exact_small := Filter.Eventually.of_forall exact
  net_derivative := by
    have h : (fun d : D => d - observe (run (prepare d))) = id := by
      funext d; rw [exact]; simp
    rw [h]; exact hasFDerivAt_id (0 : D)

theorem gauge_budget (B : ℝ) (hB : B = LinearMap.trace ℝ D gauge_repair.K.toLinearMap) :
    B = 3 ∧ ((0.1286 : ℚ) < (3 - 1/43) / (23 : ℕ) ∧ (3 - 1/43) / (23 : ℕ) < (0.1300 : ℚ)) :=
  RepairBudget.budget_from_repair gauge_repair B hB

/-- **The repair commutes with every payload gauge action.** -/
theorem repair_covariant (G : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 4 × Fin 2 → ℂ) :
    run (((1 : Spin) ⊗ₖ G) *ᵥ v) = ((1 : Spin) ⊗ₖ G) *ᵥ run v := by
  unfold run
  rw [mulVec_mulVec, mulVec_mulVec, ← mul_kronecker_mul, ← mul_kronecker_mul]
  simp

/-- **Weak acts faithfully on the payload index.** -/
theorem payload_faithful : Function.Injective
    (fun G : Matrix (Fin 2) (Fin 2) ℂ => (1 : Spin) ⊗ₖ G) := by
  intro G H h
  ext i j
  have := congrFun (congrFun h (0, i)) (0, j)
  simpa [kronecker_apply] using this

end PMConstants.GaugeWalkBudget

