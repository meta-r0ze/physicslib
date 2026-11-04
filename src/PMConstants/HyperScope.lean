import PMConstants.SectorCapabilities
import PMConstants.ResourceLedger
import PMConstants.TableConsequences

/-!
# Which hypercharge scope the W mass allows

`SectorCapabilities` shows that hypercharge's payload could be priced by different task scopes:
all sixteen channels (the whole phase, as `RequirementComplement` assigns), the fifteen with
nonzero charge, or the fourteen whose phase differs from the reference's
(`relative_phase_counts`). With the weak ledger `43` fixed, these give footprints
`172 + n η + 5` and mixings `43/footprint`.

* `relative_scope_excluded`: the fourteen-channel (relative-phase) scope puts the W mass below
  `80.2664` GeV for the measured `m_Z`, more than `7.7σ` from the direct average.
* `ResourceLedger.sterile_counted`: the fifteen-channel (absolute-charge) scope is more than
  `3.1σ` low.
* `TableConsequences.w_mass`: the sixteen-channel (whole-phase) scope lies within `1.3σ`.

So among the support-based scopes the data keep only whole-phase coverage, the premise of
`RequirementComplement`. This is an empirical selection among the stated scopes, not a
derivation of the scope from the update.
-/

noncomputable section
namespace PMConstants.HyperScope
open PMConstants

def footprint14 : ℝ := 172 + 14 * overhead + 5

theorem relative_scope_excluded {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    mZ * Real.sqrt (1 - 43 / footprint14) < 80.2664 ∧
      (mZ * Real.sqrt (1 - 43 / footprint14) - 80.3692) / 0.0133 < -7.7 := by
  have hr : Real.sqrt (1 - 43 / footprint14) < 0.880213 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num [footprint14, overhead]
  have hp : 0 ≤ Real.sqrt (1 - 43 / footprint14) := Real.sqrt_nonneg _
  have h1 : mZ * Real.sqrt (1 - 43 / footprint14) < 80.2664 := by nlinarith [h.1, h.2]
  refine ⟨h1, ?_⟩
  rw [div_lt_iff₀ (by norm_num)]; linarith

end PMConstants.HyperScope
