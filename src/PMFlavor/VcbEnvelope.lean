import PMFlavor.CKM
import PMConstants.RequirementRows
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `|V_cb|` as a divider between two causal envelopes (candidate)

`|V_cb|` is not the two-leg passive path of `VubSeriesPath` (`E8PConstants.CandidateTests.vcb_not_two_leg`). Here its supplied
form `(π + χ)/(α⁻¹ − Dπ)` is read with the pieces that already build the node impedance.

**Envelopes.** A causal envelope of constant width `w` has boundary `πw` (Barbier,
`PMSubstrate.Capacity.barbier`) and closes after `χ` turns (Descartes); its impedance is
`env w = πw + χ`, the construction of `PMConstants.VevBoundary`. The node impedance is the clock
cycle's envelope plus small terms, `Z_geo = env Δ + …` (`PMSubstrate.Impedance`: capacity `πΔ`, map
`χ`).

**Reading, and what the schedule says about it.** The first reading was that each of the `D`
frame rows is refreshed once per cycle at its own tick, leaving `Δ − D` free ticks, and that the
`c`-side hop on the weak wall is carried by one refresh tick against the free part. The library does
not support the tick count: `RequirementRows.rows_assigned` assigns whole rows to sectors and has no
clock-slot variable, and `PMConstants.WeakLocality` shows weak's events reach every one of the `43`
addresses of the clock row, one per tick. So the subtraction of `D` from `Δ` has no schedule basis at
present; the tests below hold for the formula, not for that reading.

* `matches_paper`: `env 1 / env 39` agrees with `CKM.vcb = (π + χ)/(α⁻¹ − 4π)` to `3·10⁻⁵`.

**One law with `|V_ub|`.** In the Kirchhoff network of `KronSeries` a transfer's amplitude is its
drive over its path impedance (`amp`). `|V_ub|`: the spectator-wall hop is not refreshed by the
node, so it has a unit drive and must enter and leave the node, two legs and a boundary
(`vub_by_law`). `|V_cb|`: the weak-wall hop is refreshed by the node (weak acts on the reference's
wall, `PMAction.ChiralityConvention`, `PMConstants.WeakUniform`), so it starts inside the node's
cycle, driven by one refresh tick `env 1`, and crosses the free part of the cycle once, `env (Δ − D)`
(`vcb_by_law`).

Readings that remain: the drive of a refresh tick is its envelope impedance `env 1`, and a refreshed
hop crosses the free cycle once instead of entering and leaving the node. The first can be traded
for the standard current divider with a unit source, `env 1/(env 1 + env 39)`. Status: candidate. The
data comparisons are in `E8PConstants.CandidateTests`.
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

/-- **One law for both node-crossing mixings: drive over path impedance.** `|V_ub|` is a unit drive
through two node legs and a boundary (`KronSeries`); `|V_cb|` is the refresh tick's envelope driving
the free part of the cycle. -/
noncomputable def amp (drive impedance : ℝ) : ℝ := drive / impedance

theorem vub_by_law : amp 1 (2 * CKM.αinv + Real.pi) = CKM.s13 := by
  unfold amp; rfl

theorem vcb_by_law : amp (env 1) (env 39) = env 1 / env 39 := rfl

end PMFlavor.VcbEnvelope
