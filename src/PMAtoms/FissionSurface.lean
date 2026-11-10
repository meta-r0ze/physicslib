import PMAtoms.FissionFissility
import PMAtoms.FissionAsymmetry
import PMAtoms.NuclearShells
import PMAtoms.CollectiveE8
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Fragment-resolved fission surface

A fission parent is represented by a finite set of two-fragment splits.  Each
split carries:

* the E8 fissility cost of the parent,
* a fragment shell cost from the E8 magic ladder,
* a fragment Coulomb cost.

The fission rate is the finite channel sum.  Coefficients are E8 quantities; the
numerical barrier surface is still a candidate.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

/-- A two-fragment fission split. -/
structure FissionSplit where
  light : Nuclide
  heavy : Nuclide

/-- Symmetric split. -/
def symmetricSplit (p : Nuclide) : FissionSplit :=
  ⟨⟨p.Z / 2, p.N / 2⟩, ⟨p.Z / 2, p.N / 2⟩⟩

/-- `Sn-132` plus complement. -/
def sn132Split (p : Nuclide) : FissionSplit :=
  ⟨sn132, fissionComplement p⟩

/-- A finite fission-split family. -/
def fissionSplits (p : Nuclide) : List FissionSplit :=
  [sn132Split p, symmetricSplit p]

theorem fissionSplits_length (p : Nuclide) : (fissionSplits p).length = 2 := rfl

/-- Fragment distance to the E8 magic ladder. -/
def FissionSplit.shellDistance (s : FissionSplit) : Nat :=
  magicDistance s.light.Z + magicDistance s.light.N +
    magicDistance s.heavy.Z + magicDistance s.heavy.N

/-- Closed-fragment shell gain: the `Sn-132` channel lowers the barrier. -/
def FissionSplit.shellGain (s : FissionSplit) : ℝ :=
  if s.light = sn132 then shellWeight else 0

/-- Legacy shell distance cost, kept for diagnostics. -/
def FissionSplit.shellCost (s : FissionSplit) : ℝ :=
  shellWeight * (s.shellDistance : ℝ)

/-- Fragment Coulomb cost. -/
def FissionSplit.coulombCost (s : FissionSplit) : ℝ :=
  (chargeCoupling / (Δ : ℝ)) * (s.light.Z : ℝ) * (s.heavy.Z : ℝ) /
    (((s.light.Z + s.light.N : Nat) : ℝ) ^ ((1 : ℝ) / 3) +
      ((s.heavy.Z + s.heavy.N : Nat) : ℝ) ^ ((1 : ℝ) / 3))

/-- Full fragment-resolved cost. -/
def FissionSplit.cost (p : Nuclide) (s : FissionSplit) : ℝ :=
  fissionCostE8 p - s.shellGain + s.coulombCost

/-- Finite fragment-resolved fission rate. -/
noncomputable def fissionSurfaceRate (p : Nuclide) : ℝ :=
  List.sum ((fissionSplits p).map (fun s => alphaAttempt p * Real.exp (-(s.cost p))))

/-- Fragment-resolved fission lifetime. -/
noncomputable def fissionSurfaceLifetime (p : Nuclide) : ℝ :=
  1 / fissionSurfaceRate p

/-- Superheavy threshold `2Δ+2σ+2χ = 100`. -/
def fissionSuperheavyThreshold : Nat := 2 * Δ + 2 * σ + 2 * χ

theorem fissionSuperheavyThreshold_eq : fissionSuperheavyThreshold = 100 := by
  unfold fissionSuperheavyThreshold
  norm_num [Δ, σ, χ, PMSubstrate.baseline]

/-- Superheavy governor cost: `χ` per proton above the threshold. -/
def fissionSuperheavyCost (p : Nuclide) : ℝ :=
  (χ : ℝ) * (if fissionSuperheavyThreshold < p.Z then ((p.Z - fissionSuperheavyThreshold : Nat) : ℝ) else 0)

/-- Full fragment-resolved cost including the superheavy governor. -/
def FissionSplit.costWithGovernor (p : Nuclide) (s : FissionSplit) : ℝ :=
  s.cost p + fissionSuperheavyCost p

end PMAtoms
