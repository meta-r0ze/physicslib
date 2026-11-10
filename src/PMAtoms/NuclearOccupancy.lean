import PMAtoms.Nucleus
import PMAtoms.NuclearShells
import PMAtoms.NuclearRegime
import Mathlib.Tactic

/-!

# Nuclear occupancy and closures

A nucleus is a composite of `A = Z + N` nucleon sites. Its shell closures are E8 counts
(`NuclearShells.nuclearMagic`: `2=χ, 8=Dχ, 20=Dσ, 28=D(σ+χ), 50=χσ², 82=2(Δ−χ),
126=(σ−χ)(Δ−1), 184=D(Δ+σ−χ)`), and the deformed-actinide frontier is the closure pair
`Z = 96 = 2(Δ+σ)`, `N = 152 = (σ−χ)Δ + (ν+σ+χ)` (`E8AtomValues`, `NuclearRegime`). This module
names the occupancy and its closure thresholds, so "why these counts / where does the ledger
saturate" is a cost-functional question (`PersistenceMechanics.SelectionSymmetry`), not arithmetic —
the same framing the hadron occupancy uses.

Two open items remain (REVIEW §1): the alpha-layer **saturation** past a closed core (every N=Z
nucleus past O-16 is over-bound by ≈`1.1–1.2 m_e` per alpha cluster, `RESIDUALS.md`), and the heavy
**deformation occupancy shape** (candidate `43/288`; holdout scatter `±0.019 u`).
-/

namespace PMAtoms.NuclearOccupancy

/-- Nucleon occupancy `A = Z + N`. -/
def occupancy (p : Nuclide) : ℕ := p.Z + p.N

/-- A proton closure: `Z` is a magic number. -/
def ProtonClosed (p : Nuclide) : Prop := p.Z ∈ nuclearMagic

/-- A neutron closure: `N` is a magic number. -/
def NeutronClosed (p : Nuclide) : Prop := p.N ∈ nuclearMagic

/-- Doubly closed (a closure pair). -/
def DoublyClosed (p : Nuclide) : Prop := ProtonClosed p ∧ NeutronClosed p

/-- **The deformed-actinide frontier is a closure pair**: `Z = 96`, `N = 152`. -/
theorem frontier_doublyClosed : DoublyClosed ⟨96, 152⟩ := by
  refine ⟨?_, ?_⟩
  · show (96 : ℕ) ∈ nuclearMagic; rw [nuclearMagic_eq]; decide
  · show (152 : ℕ) ∈ nuclearMagic; rw [nuclearMagic_eq]; decide

/-- Lead-208 (`Z = 82`, `N = 126`) is doubly closed. -/
theorem pb208_doublyClosed : DoublyClosed ⟨82, 126⟩ := by
  refine ⟨?_, ?_⟩
  · show (82 : ℕ) ∈ nuclearMagic; rw [nuclearMagic_eq]; decide
  · show (126 : ℕ) ∈ nuclearMagic; rw [nuclearMagic_eq]; decide

/-- The nucleus occupancy of the frontier pair. -/
theorem frontier_occupancy : occupancy ⟨96, 152⟩ = 248 := by
  unfold occupancy; norm_num

theorem pb208_occupancy : occupancy ⟨82, 126⟩ = 208 := by
  unfold occupancy; norm_num

end PMAtoms.NuclearOccupancy
