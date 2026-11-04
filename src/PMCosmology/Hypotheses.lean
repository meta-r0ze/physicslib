import PMCosmology.Background
import PMCosmology.Scaling

/-!
# The Paper VI hypothesis ledger

Every cosmological result here is conditional on a short list of constitutive
premises: a load with two response rules, and a load-proportional density obeying
a separately conserved continuity equation. This module puts those premises in a
single structure, `CosmoModel`, and re-derives the key statements from it, so
"the paper assumes X" is a machine-checkable input list rather than prose spread
across modules.

Nothing here selects the load, the response rules or the continuity law; those
remain model inputs. The point is to make the conditional structure explicit.
-/

noncomputable section
namespace PMCosmology.Hypotheses
open PMCosmology

/-- The constitutive premises Paper VI uses, in one place. Each field is an input. -/
structure CosmoModel where
  /-- dimensionless load `L` -/
  load : ℝ
  load_ne : load ≠ 0
  /-- the two frozen draft inputs -/
  H_early : ℝ
  S_early : ℝ
  /-- the two response outputs -/
  hubble_late : ℝ
  clustering_late : ℝ
  /-- response rules: `H_late = H_early · L`, `S8_late = S8_early / L` -/
  hubble_rule : hubble_late = H_early * load
  clustering_rule : clustering_late = S_early / load
  /-- load-proportional density `ρ(a) = ρ₀ L(a)` and its derivative at `a` -/
  L : ℝ → ℝ
  rho0 : ℝ
  a : ℝ
  Ldot : ℝ
  w : ℝ
  derivative : HasDerivAt L Ldot a
  /-- separately conserved continuity, no inter-sector exchange term -/
  continuity : a * (rho0 * Ldot) = -3 * (1 + w) * (rho0 * L a)
  rho0_ne : rho0 ≠ 0
  L_ne : L a ≠ 0
  a_pos : 0 < a

namespace CosmoModel
variable (M : CosmoModel)

/-- **The response rules make `H_late · S8_late` exactly invariant.** -/
theorem product_invariant : M.hubble_late * M.clustering_late = M.H_early * M.S_early := by
  rw [M.hubble_rule, M.clustering_rule]
  field_simp [M.load_ne]

/-- **The equation of state** follows from the continuity law and load-proportional
density; it is not a separate assumption. -/
theorem equation_of_state : M.w = -1 - M.a * M.Ldot / (3 * M.L M.a) :=
  (Background.equation_of_state M.a M.rho0 (M.L M.a) M.Ldot M.w M.rho0_ne M.L_ne).mp
    M.continuity

/-- The density derivative tracks the load derivative. -/
theorem density_derivative :
    HasDerivAt (fun x => M.rho0 * M.L x) (M.rho0 * M.Ldot) M.a :=
  M.derivative.const_mul M.rho0

/-- **Vacuum equation of state iff the load is instantaneously constant.** -/
theorem vacuum_iff : M.w = -1 ↔ M.Ldot = 0 := by
  rw [M.equation_of_state]
  exact Background.vacuum_equation_iff M.a (M.L M.a) M.Ldot M.a_pos M.L_ne

/-- With the paper's load and draft early inputs, the response rule gives the
certified headline value `H_late = 502467/6880`. -/
theorem headline (hL : M.load = loadFactor) (hH : M.H_early = 674 / 10) :
    M.hubble_late = 502467 / 6880 := by
  rw [M.hubble_rule, hH, hL, exact_ratios.2.1]
  norm_num

end CosmoModel

end PMCosmology.Hypotheses
