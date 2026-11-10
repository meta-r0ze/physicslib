import PMHadrons.CompositeMasses
import PMSubstrate.PersistencePremises
import Mathlib.Tactic

/-!

# The nucleon base is Margin's causal cone

The two composite bases are both **pillar counts**, not fitted numbers:

* mesons: `n = χ + σ·ℓ` substrate cells — the Map base `χ` plus, for each line-tier
  carrier, the Protocol interaction-direction count `σ` (`StrangeCarrier`);
* nucleons: the base `Δ²` is **Margin's causal cone of one cycle** — the events reachable from an
  origin in one clock period at speed one, `{(t, x) : t < Δ, |x| ≤ t}`, which number exactly `Δ²`
  (`PMSubstrate.PersistencePremises.causal_cone_card`), the count Margin prices.

`causal_cone_card` is the substrate theorem; here it is connected to the nucleon ledger
`CompositeMasses.base = Δ² − πD − 1/D`, so the leading `Δ²` is the cone, not an independent
integer. This is the pillar-consistent answer to "why the nucleons and the mesons use different
bases": they are pricing different pillars (Margin's cone vs Map's cells plus Protocol's
directions).
-/

namespace PMHadrons.NucleonBase

open Finset
open PMSubstrate.E8Values

/-- The number of causal-cone events in one cycle, `{(t, x) : t < Δ, |x| ≤ t}`. -/
def causalCone : ℕ :=
  ∑ t ∈ range Delta, (Icc (-(t : ℤ)) t).card

/-- **The causal cone of one cycle has `Δ²` events** — Margin's count. -/
theorem causalCone_eq_sq : causalCone = Delta ^ 2 :=
  PMSubstrate.PersistencePremises.causal_cone_card Delta

theorem causalCone_eq : causalCone = 1849 := by
  rw [causalCone_eq_sq, PMSubstrate.E8Values.Delta_eq]
  norm_num

/-- **The nucleon base carries Margin's causal cone.** `base = Δ² − πD − 1/D` with `Δ²` the
one-cycle causal-cone count, so the nucleon's leading room is the cone, not an independent
integer. -/
theorem base_eq_causalCone :
    PMHadrons.CompositeMasses.base =
      (causalCone : ℝ) - Real.pi * (D : ℝ) - 1 / (D : ℝ) := by
  unfold causalCone PMHadrons.CompositeMasses.base
  rw [PMSubstrate.PersistencePremises.causal_cone_card Delta, Nat.cast_pow]

/-- **The proton mass is the causal-cone base minus the pillar costs.** -/
theorem proton_eq_causalCone :
    PMHadrons.CompositeMasses.proton =
      (causalCone : ℝ) - Real.pi * (D : ℝ) - 1 / (D : ℝ) +
        (sigma : ℝ) * PMHadrons.CompositeMasses.zTol -
          PMHadrons.CompositeMasses.zMar / (chi : ℝ) -
            PMHadrons.CompositeMasses.αe * ((D : ℝ) + 1 / (D : ℝ)) := by
  unfold PMHadrons.CompositeMasses.proton
  rw [base_eq_causalCone]

end PMHadrons.NucleonBase
