import PMAtoms.FissionSurface
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Finite fission yield surface

A small yield family around the `Sn-132` closure plus the symmetric split.  The
weights are placeholders for the E8 fragment-yield measure; the rate sum is the
structural object.
-/

noncomputable section
namespace PMAtoms

/-- Split with an arbitrary light fragment. -/
def fissionSplitWith (z n : Nat) (p : Nuclide) : FissionSplit :=
  ⟨⟨z, n⟩, ⟨p.Z - z, p.N - n⟩⟩

/-- A weighted fragment channel. -/
structure FissionYield where
  split : FissionSplit
  weight : ℝ

/-- Light-fragment distance to the E8 magic ladder. -/
def FissionSplit.lightShellDistance (s : FissionSplit) : Nat :=
  magicDistance s.light.Z + magicDistance s.light.N

/-- E8 fragment-yield weight: `exp(−(shellWeight/Δ)·d_light)`. -/
noncomputable def fissionYieldWeight (s : FissionSplit) : ℝ :=
  Real.exp (-(shellWeight / (Δ : ℝ)) * (s.lightShellDistance : ℝ))

theorem fissionYieldWeight_pos (s : FissionSplit) : 0 < fissionYieldWeight s := by
  unfold fissionYieldWeight
  positivity

/-- Small yield family: Sn-132, neighbouring Sn isotopes, symmetric. -/
noncomputable def fissionYields (p : Nuclide) : List FissionYield :=
  [ ⟨sn132Split p, fissionYieldWeight (sn132Split p)⟩
  , ⟨fissionSplitWith 50 80 p, fissionYieldWeight (fissionSplitWith 50 80 p)⟩
  , ⟨fissionSplitWith 50 84 p, fissionYieldWeight (fissionSplitWith 50 84 p)⟩
  , ⟨symmetricSplit p, fissionYieldWeight (symmetricSplit p)⟩
  ]

theorem fissionYields_length (p : Nuclide) : (fissionYields p).length = 4 := rfl

/-- Finite fragment-yield fission rate. -/
noncomputable def fissionYieldRate (p : Nuclide) : ℝ :=
  List.sum ((fissionYields p).map (fun y =>
    y.weight * alphaAttempt p *
      Real.exp (-(y.split.costWithGovernor p))))

/-- Fragment-yield fission lifetime. -/
noncomputable def fissionYieldLifetime (p : Nuclide) : ℝ :=
  1 / fissionYieldRate p

/-- Test set for the superheavy surface. -/
def fissionTestNuclei : List Nuclide :=
  [⟨92, 146⟩, ⟨98, 154⟩, ⟨100, 154⟩, ⟨102, 150⟩, ⟨104, 152⟩]

theorem fissionTestNuclei_length : fissionTestNuclei.length = 5 := rfl

/-- Total yield weight. -/
noncomputable def fissionYieldNormalization (p : Nuclide) : ℝ :=
  (fissionYields p).foldl (fun acc y => acc + y.weight) 0

/-- Normalized fragment-yield fission rate. -/
noncomputable def fissionYieldRateNormalized (p : Nuclide) : ℝ :=
  List.sum ((fissionYields p).map (fun y =>
    (y.weight / fissionYieldNormalization p) * alphaAttempt p *
      Real.exp (-(y.split.costWithGovernor p))))

/-- Normalized fragment-yield lifetime. -/
noncomputable def fissionYieldLifetimeNormalized (p : Nuclide) : ℝ :=
  1 / fissionYieldRateNormalized p

/-- E8 full-yield measure scale `Δ²/(D+σ) = 1849/9`. -/
def fissionYieldMeasureScale : ℝ :=
  ((Δ : ℝ) ^ 2) / (((D + σ : Nat)) : ℝ)

theorem fissionYieldMeasureScale_eq : fissionYieldMeasureScale = 1849 / 9 := by
  unfold fissionYieldMeasureScale
  norm_num [Δ, D, σ, PMSubstrate.baseline]

/-- Full finite yield sum over all light fragments. -/
noncomputable def fissionFullSum (p : Nuclide) : ℝ :=
  Finset.sum ((Finset.range p.Z).product (Finset.range p.N)) (fun x =>
    if 0 < x.1 ∧ 0 < x.2 ∧ x.1 < p.Z ∧ x.2 < p.N then
      let s : FissionSplit := ⟨⟨x.1, x.2⟩, ⟨p.Z - x.1, p.N - x.2⟩⟩
      fissionYieldWeight s * alphaAttempt p *
        Real.exp (-(s.costWithGovernor p))
    else 0)

/-- Full-yield fission rate after the E8 measure normalization. -/
noncomputable def fissionFullRate (p : Nuclide) : ℝ :=
  fissionFullSum p / fissionYieldMeasureScale

/-- Full-yield fission lifetime. -/
noncomputable def fissionFullLifetime (p : Nuclide) : ℝ :=
  1 / fissionFullRate p

end PMAtoms
