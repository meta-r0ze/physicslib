import PMConstants.Hypercharge
import PMConstants.GaugeStiffness
import PMConstants.CertifiedConstants

/-!
# Per-sector normalization from the generation's channel content

If a loop's cost is measured on the sixteen channel states of one generation,
`1 − (1/16) Re Tr U`, its quadratic part for sector `i` is proportional to the sector's
index on those states, `T_i = Σ_states (generator)²`. Stiffness `β_i = c W_i` then gives
`g_i² ∝ 1/(T_i W_i)`.

* `weak_index`, `strong_index`: four doublets and four triplets give `T₂ = T₃ = 2`.
* `hyper_index_forced`: under Paper III's flux, Yukawa and neutrality premises the charges are
  forced (`Hypercharge.charges_forced`) and the hypercharge index (with `Q = T₃ + Y/2`) is
  `T_Y = 10/3`; `T_Y/T₂ = 5/3`.
* `indexed_mixing`: `s = g'²/(g² + g'²) = T₂W_W/(T₂W_W + T_Y W_Y)`.
* `clock_ledger_parity`: the clock ledger enters as `T₂ W_W = 2W_W`, which is never `43`.
  So the paper's `s = Δ/N_sys` holds with equal normalization only if its ledger counts
  channel-weighted cost; read as integer refresh counts, the clock contributes `2Δ`.
* `strong_from_ledger`: in channel-cost units the uniform rule gives `α_s = α N_sys/L₃`.
  The paper's formula is the non-integer `L₃ = N_sys/(16η + 1/4) ∈ (11, 12)`; the integer
  ledgers give `α_s ∈ (0.1279, 0.1280)` for `L₃ = 11` and `(0.11730, 0.11732)` for `L₃ = 12`.
  Which ledger the strong sector carries is the remaining derivation.
-/

noncomputable section
namespace PMConstants.StiffnessIndices
open PMConstants Hypercharge

/-- Four doublets per generation (three colours of quark doublet, one lepton doublet). -/
def weakIndex : ℚ := (3 + 1) * (1/2)
/-- Four triplets per generation (two in the quark doublet, `u_R`, `d_R`). -/
def strongIndex : ℚ := (2 + 1 + 1) * (1/2)
/-- Hypercharge index with `Q = T₃ + Y/2`: multiplicities 6, 3, 3, 2, 1, 1. -/
def hyperIndex (Y : Charges) : ℚ :=
  (6 * Y.q^2 + 3 * Y.u^2 + 3 * Y.d^2 + 2 * Y.l^2 + Y.e^2 + Y.n^2) / 4

theorem weak_index : weakIndex = 2 := by norm_num [weakIndex]
theorem strong_index : strongIndex = 2 := by norm_num [strongIndex]

theorem hyper_index_forced (Y : Charges) (hf : Flux Y) (hy : Yukawa Y 1) (hn : Y.n = 0) :
    hyperIndex Y = 10/3 ∧ hyperIndex Y / weakIndex = 5/3 := by
  rw [charges_forced Y hf hy hn]
  norm_num [hyperIndex, standard, weakIndex]

def gsqI (c T W : ℝ) : ℝ := 1 / (2 * c * T * W)

theorem indexed_mixing {c T₂ TY W Y : ℝ} (hc : 0 < c) (h2 : 0 < T₂) (hY' : 0 < TY)
    (hW : 0 < W) (hY : 0 < Y) :
    gsqI c TY Y / (gsqI c T₂ W + gsqI c TY Y) = T₂ * W / (T₂ * W + TY * Y) := by
  unfold gsqI; field_simp; ring

theorem clock_ledger_parity (W : ℕ) : 2 * W ≠ 43 := by omega

open CertifiedConstants in
theorem strong_from_ledger :
    (0.1279 : ℝ) < α * footprint / 11 ∧ α * footprint / 11 < 0.1280 ∧
    (0.11730 : ℝ) < α * footprint / 12 ∧ α * footprint / 12 < 0.11732 := by
  have h := alpha_bounds
  norm_num [footprint, overhead]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [h.1, h.2]

end PMConstants.StiffnessIndices
