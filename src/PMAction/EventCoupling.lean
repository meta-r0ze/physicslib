import PMAction.CommonResponse
import PMAction.Machine.CarrierResponse
import PMAction.Machine.SummedReference

/-!
# From event prices to gauge couplings (moved from PMConstants, Nov 2026)

Paper II mechanics that turn the common event price into a lattice stiffness and a coupling,
with no Paper III ledger. `PMConstants.GaugeStiffness`, `EventStiffness` and `ChainCouplings`
re-export these names and add the ledgers and the electric calibration.

* `refresh_ledger`: `W` refreshes at curvature cost `c₀ S` each cost `(c₀ W) S`.
* `gsq`: the D₄ normalization `g² = 1/(2β)`; `mixing`, `electric`: the two-sector algebra.
* `c0`, `refresh_from_events`: a phase test repaired by `m` primitive events at the common toll
  has `c₀ = toll·m/2`.
* `coupling_from_events`: `g² = 1/(toll·m·W)`.
* `scalar_shares_prefactor`: the scalar link and the gauge plaquette share the prefactor
  `toll·m/4` when priced by the same readout event.
* `chainCoupling`, `chain_canonical`: the summed-read coupling `g² = 1/(κ_R·toll·m·W)`.
-/

noncomputable section
namespace PMAction.EventCoupling
open PMAction

theorem refresh_ledger (c₀ S : ℝ) (W : ℕ) :
    (∑ _k : Fin W, c₀ * S) = (c₀ * W) * S := by
  simp [Finset.sum_const]; ring

def gsq (β : ℝ) : ℝ := 1 / (2 * β)

theorem mixing {c W Y : ℝ} (hc : 0 < c) (hW : 0 < W) (hY : 0 < Y) :
    gsq (c*Y) / (gsq (c*W) + gsq (c*Y)) = W / (W + Y) := by
  unfold gsq; field_simp; ring

theorem electric {c W Y : ℝ} (hc : 0 < c) (hW : 0 < W) (hY : 0 < Y) :
    gsq (c*W) * gsq (c*Y) / (gsq (c*W) + gsq (c*Y)) = gsq (c*(W + Y)) := by
  unfold gsq; field_simp; ring

def c0 (toll : ℝ) (m : ℕ) : ℝ := toll * m / 2

theorem refresh_from_events (toll θ : ℝ) (m W : ℕ) :
    (∑ _ : Fin W, CarrierResponse.repairCost toll m (InterferenceReadout.phase θ)) =
      (c0 toll m * W) * (1 - Real.cos θ) := by
  rw [CarrierResponse.refreshed_phase_cost]; unfold c0; ring

theorem coupling_from_events (toll : ℝ) (m : ℕ) (W : ℝ) :
    gsq (c0 toll m * W) = 1 / (toll * m * W) := by
  unfold gsq c0; congr 1; ring

theorem scalar_shares_prefactor (toll θ : ℝ) (m : ℕ) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix κ κ ℂ) (φ φ' : κ → ℂ) :
    CommonResponse.responseCost toll m (CommonResponse.linkFlag U φ φ') =
        toll * m / 4 * CommonResponse.nsq (φ' - U.mulVec φ) ∧
      CarrierResponse.repairCost toll m (InterferenceReadout.phase θ) =
        toll * m / 4 * CommonResponse.nsq
          ((fun _ => (1 : ℂ)) - (InterferenceReadout.phase θ).mulVec (fun _ => 1)) := by
  obtain ⟨h1, h2, -, h4⟩ := CommonResponse.common_normalization toll m θ U φ φ'
  exact ⟨h2, h4 ▸ h1⟩

/-- Canonical summed-read coupling `g² = 1/(κ_R·toll·m·W)`. -/
def chainCoupling (κ toll : ℝ) (m : ℕ) (W : ℝ) : ℝ := 1 / (κ * toll * m * W)

theorem chain_canonical {toll κ W g : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m)
    (hκ : 0 < κ) (hW : 0 < W) (hg : g ≠ 0) :
    (toll * m * W / 4) * (κ * g ^ 2) = 1 / 4 ↔ g ^ 2 = chainCoupling κ toll m W :=
  SummedReference.sum_canonical_iff ht hm hκ hW hg

end PMAction.EventCoupling
