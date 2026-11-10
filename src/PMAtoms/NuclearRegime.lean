import PMAtoms.TwoLedger
import PMAtoms.E8AtomValues
import Mathlib.Tactic

/-!
# Nuclear regimes and the deformed-actinide frontier

The smooth shell/deformation ledger is valid through the deformed closures
`Z = 96 = 2(Δ+σ)` and `N = 152 = (σ−χ)Δ + (ν+σ+χ)`.  Beyond that frontier the
Cm/Cf residuals are a regime change, not a missing coefficient.
-/

namespace PMAtoms
open PMElementaryParticles PMHadrons

/-- Coarse nuclear regimes. -/
inductive NuclearRegime
  | light
  | mid
  | deformedActinide
  | beyondFrontier
  deriving DecidableEq, Repr

/-- The smooth-ledger frontier. -/
def deformedFrontier (z n : Nat) : Prop :=
  z ≤ deformedProtonShell ∧ n ≤ deformedNeutronShell

def deformedFrontierB (z n : Nat) : Bool :=
  z ≤ deformedProtonShell && n ≤ deformedNeutronShell

/-- Regime classification by the E8 closures. -/
def regimeOf (z n : Nat) : NuclearRegime :=
  if z ≤ 20 ∧ n ≤ 20 then .light
  else if z ≤ protonShell ∧ n ≤ neutronShell then .mid
  else if deformedFrontierB z n then .deformedActinide
  else .beyondFrontier

theorem pb_regime : regimeOf 82 126 = .mid := by
  decide

theorem u_regime : regimeOf 92 146 = .deformedActinide := by
  decide

theorem cm_regime : regimeOf 96 148 = .deformedActinide := by
  decide

theorem cf_regime : regimeOf 98 154 = .beyondFrontier := by
  decide

theorem cm_at_frontier : deformedFrontier 96 148 := by
  unfold deformedFrontier deformedProtonShell deformedNeutronShell
  decide

theorem cf_beyond_frontier : ¬ deformedFrontier 98 154 := by
  unfold deformedFrontier deformedProtonShell deformedNeutronShell
  decide

end PMAtoms
