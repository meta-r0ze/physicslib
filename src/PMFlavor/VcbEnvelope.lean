import PMFlavor.CKM
import PMConstants.RequirementRows
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `|V_cb|` as a divider between two causal envelopes (candidate)

`VubSeriesPath.vcb_not_two_leg`: `|V_cb|` is not a passive path with unit drive. Here its supplied
form `(π + χ)/(α⁻¹ − Dπ)` is read with the pieces that already build the node impedance.

**Envelopes.** A causal envelope of constant width `w` has boundary `πw` (Barbier,
`PMSubstrate.Capacity.barbier`) and closes after `χ` turns (Descartes); its impedance is
`env w = πw + χ`, the construction of `PMConstants.VevBoundary`. The node impedance is the clock
cycle's envelope plus small terms, `Z_geo = env Δ + …` (`PMSubstrate.Impedance`: capacity `πΔ`, map
`χ`).

**Reading.** In each clock cycle every frame row is refreshed exactly once
(`PMConstants.RequirementRows.rows_assigned`: weak the clock row, hypercharge the three spatial
rows), so `D` of the `Δ` ticks are refresh ticks and `Δ − D` are free. The `c`-side node-crossing
hop runs on the weak (reference) wall (`ExchangeChirality`) and is carried by one refresh tick, an
envelope of unit width. Its amplitude is the divider `env 1 / env (Δ − D)`, the refresh tick against
the free part of the cycle. The `s`-side hop (`|V_ub|`, `VubSeriesPath`) is on the spectator wall,
which the weak refresh does not act on, and has a bare unit drive.

* `matches_paper`: `env 1 / env 39` agrees with `CKM.vcb = (π + χ)/(α⁻¹ − 4π)` to `3·10⁻⁵`, far
  below the error.
* `divider_fits`: `env 1 / env 39` is `0.2σ` from `|V_cb| = 0.0411 ± 0.0012`.
* `drive_unique`: other drives over the same free envelope are excluded (more than `13σ`): a bare
  unit, `χ`, `π`, `env 2`.
* `free_ticks_needed`: removing no refresh tick (`env 1 / env 43`) or one (`env 1 / env 42`) is more
  than `2σ` low. The data allow `3`–`5` removed ticks; `D` is the refresh count.

**One law with `|V_ub|`.** In the Kirchhoff network of `KronSeries` a transfer's amplitude is its
drive over its path impedance (`amp`). `|V_ub|`: the spectator-wall hop is not refreshed by the
node, so it has a unit drive and must enter and leave the node, two legs and a boundary
(`vub_by_law`). `|V_cb|`: the weak-wall hop is refreshed by the node (weak acts on the reference's
wall, `PMAction.ChiralityConvention`, `PMConstants.WeakUniform`), so it starts inside the node's
cycle, driven by one refresh tick `env 1`, and crosses the free part of the cycle once, `env (Δ − D)`
(`vcb_by_law`). Their ratio, the quark parity breaking, fits (`ratio_fits`, `1.1σ`).

Readings that remain: the drive of a refresh tick is its envelope impedance `env 1`, and a refreshed
hop crosses the free cycle once instead of entering and leaving the node. Status: candidate.
-/

namespace PMFlavor.VcbEnvelope

/-- Impedance of a causal envelope of width `w`: Barbier boundary plus `χ = 2` closures. -/
noncomputable def env (w : ℝ) : ℝ := Real.pi * w + 2

theorem env_pos (w : ℝ) (hw : 0 ≤ w) : 0 < env w := by
  unfold env; have := Real.pi_pos; positivity

theorem env_bounds_div :
    (0.04128 : ℝ) < env 1 / env 39 ∧ env 1 / env 39 < 0.04130 := by
  have h1 := Real.pi_gt_d4; have h2 := Real.pi_lt_d4
  have hp : 0 < env 39 := env_pos 39 (by norm_num)
  unfold env at hp ⊢
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

theorem matches_paper : |env 1 / env 39 - CKM.vcb| < 0.00003 := by
  have h := env_bounds_div
  have hv := CKM.vcb_bounds
  rw [abs_lt]; constructor <;> linarith [h.1, h.2, hv.1, hv.2]

theorem divider_fits : |env 1 / env 39 - 0.0411| / 0.0012 < 1 := by
  have h := env_bounds_div
  rw [div_lt_one (by norm_num), abs_lt]; constructor <;> linarith [h.1, h.2]

theorem drive_unique :
    1 / env 39 < 0.0411 - 13 * 0.0012 ∧ 2 / env 39 < 0.0411 - 13 * 0.0012 ∧
      Real.pi / env 39 < 0.0411 - 13 * 0.0012 ∧ 0.0411 + 13 * 0.0012 < env 2 / env 39 := by
  have h1 := Real.pi_gt_d4; have h2 := Real.pi_lt_d4
  have hp : 0 < env 39 := env_pos 39 (by norm_num)
  unfold env at hp ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith
  · rw [lt_div_iff₀ hp]; nlinarith

theorem free_ticks_needed :
    env 1 / env 43 < 0.0411 - 2 * 0.0012 ∧ env 1 / env 42 < 0.0411 - 2 * 0.0012 := by
  have h1 := Real.pi_gt_d4; have h2 := Real.pi_lt_d4
  have hp3 : 0 < env 43 := env_pos 43 (by norm_num)
  have hp2 : 0 < env 42 := env_pos 42 (by norm_num)
  unfold env at hp3 hp2 ⊢
  constructor
  · rw [div_lt_iff₀ hp3]; nlinarith
  · rw [div_lt_iff₀ hp2]; nlinarith

/-- **One law for both node-crossing mixings: drive over path impedance.** `|V_ub|` is a unit drive
through two node legs and a boundary (`KronSeries`); `|V_cb|` is the refresh tick's envelope driving
the free part of the cycle. -/
noncomputable def amp (drive impedance : ℝ) : ℝ := drive / impedance

theorem vub_by_law : amp 1 (2 * CKM.αinv + Real.pi) = CKM.s13 := by
  unfold amp; rfl

theorem vcb_by_law : amp (env 1) (env 39) = env 1 / env 39 := rfl

/-- The ratio `|V_cb|/|V_ub|`, the quark parity breaking, is within `2σ`
(`11.45` against `0.0411/0.00382 = 10.76 ± 0.64`). -/
theorem ratio_fits :
    |amp (env 1) (env 39) / amp 1 (2 * CKM.αinv + Real.pi) - 10.76| / 0.645 < 2 := by
  have h := env_bounds_div
  have ha := CKM.ai_bounds
  have hp1 := Real.pi_gt_d4; have hp2 := Real.pi_lt_d4
  have hpos : 0 < 2 * CKM.αinv + Real.pi := by linarith
  have e : amp (env 1) (env 39) / amp 1 (2 * CKM.αinv + Real.pi) =
      env 1 / env 39 * (2 * CKM.αinv + Real.pi) := by
    unfold amp; field_simp
  have l := mul_lt_mul_of_pos_right h.1 hpos
  have u := mul_lt_mul_of_pos_right h.2 hpos
  rw [e, div_lt_iff₀ (by norm_num), abs_lt]
  constructor <;> linarith

end PMFlavor.VcbEnvelope
