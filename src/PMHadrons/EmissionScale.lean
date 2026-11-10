import PMHadrons.Emission
import PMHadrons.NucleonBase
import PMHadrons.PionWidth
import PMHadrons.KaonWidth
import PersistenceMechanics.LawSelection
import Mathlib.Tactic

/-!

# The emission scale: uniform configuration, and a no-go

The composite's emission configuration is the persistence-selected **uniform** state over its
emission mode space (`PersistenceMechanics.LawSelection.uniform_law`; with positive hazard the
survivors concentrate on the uniform law, `selected_uniform_worst`). So the boundary emission
weight is the uniform one and the decay constant is the VEV over the mode count:

```
fπ = v / |Ω_π| ,    fK = v / |Ω_K| ,
```

with `|Ω|` the emission mode count.

**No-go (`occupancy_reading_excluded`).** The emission mode count is **not** the composite's
occupancy. If it were, `|Ω_π| = χ`, `|Ω_K| = σ + χ`, so `fK/fπ = χ/(σ+χ) = 2/7 < 1`; but the E8
enclosures give `fK/fπ > 1` (`302.47/254.95 ≈ 1.186`, `fK_over_fPi_gt_one`). So the emission space
is a **separate** structure from the occupancy — the one remaining construction. The assigned
denominators are `|Ω_π| = Δ² + Δ − χ = 1890` and `|Ω_K| = Δ² − ν² = 1593`.

**Readings tested and failed (do not re-try).** GMOR on the derived masses gives `fK/fπ ≈ 1.08`;
the occupancy gives `2/7`; the boundary-event space (`ValidToll`, size `334`) over-scales `fπ`.
Both assigned counts are perturbations of the one-cycle causal cone (`Δ²`), so a cone-derived
mode space is the strongest lead; but since `fπ = v/(Δ²+Δ−χ)` is assigned, the count may be a
coincidence.
-/

namespace PMHadrons.EmissionScale

open PMSubstrate.E8Values

/-- The composite's emission configuration is the persistence-selected uniform law over its
emission mode space. -/
theorem emission_configuration_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    PersistenceMechanics.LawSelection.PosLaw
      (PersistenceMechanics.LawSelection.uniform (Ω := Ω)) :=
  PersistenceMechanics.LawSelection.uniform_law

/-- **The decay-constant comparison ratio is above one** (from the E8 enclosures). -/
theorem fK_over_fPi_gt_one :
    1 < PMHadrons.KaonWidth.kaonDecayConstantE8 / PMHadrons.PionWidth.pionDecayConstantE8 := by
  have hk := PMHadrons.KaonWidth.kaonDecayConstantE8_bounds
  have hp := PMHadrons.PionWidth.pionDecayConstantE8_bounds
  have hp0 : 0 < PMHadrons.PionWidth.pionDecayConstantE8 := lt_trans (by norm_num) hp.1
  rw [one_lt_div hp0]
  nlinarith [hk.1, hp.2]

/-- **The emission mode count is not the occupancy.** If it were, `fK/fπ = χ/(σ+χ) = 2/7 < 1`,
but it is `> 1`. So the emission space is separate. -/
theorem occupancy_reading_excluded :
    PMHadrons.KaonWidth.kaonDecayConstantE8 / PMHadrons.PionWidth.pionDecayConstantE8 ≠
      (chi : ℝ) / ((sigma : ℝ) + (chi : ℝ)) := by
  intro h
  have h1 := fK_over_fPi_gt_one
  have h2 : (chi : ℝ) / ((sigma : ℝ) + (chi : ℝ)) < 1 := by
    rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq]; norm_num
  rw [h] at h1
  linarith

/-- The pion emission mode count `|Ω_π| = Δ² + Δ − χ`. -/
def pionModes : ℕ := Delta ^ 2 + (Delta - chi)

theorem pionModes_eq : pionModes = 1890 := by decide

/-- The kaon emission mode count `|Ω_K| = Δ² − ν²`. -/
def kaonModes : ℕ := Delta ^ 2 - nu ^ 2

theorem kaonModes_eq : kaonModes = 1593 := by decide

/-- The pion emission mode count is the one-cycle **causal cone** (`NucleonBase.causalCone`) plus
the `Δ − χ` residual slots — the nucleon's Margin cone reappears as the pion's emission scale. -/
theorem pionModes_eq_causalCone :
    pionModes = PMHadrons.NucleonBase.causalCone + (Delta - chi) := by
  unfold pionModes
  rw [PMHadrons.NucleonBase.causalCone_eq_sq]

end PMHadrons.EmissionScale
