import PMAtoms.FissionFinite
import PMAtoms.TwoLedger
import PMAtoms.Invariants
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# E8 fissility cost for spontaneous fission

Leading cost:

```
C_f = Δ²/(ν+D+σ+χ) − σχ·(Z²/A − (Δ−D)).
```

Above the `N=152` closure, the asymmetric `Sn-132` channel subtracts the E8
shell weight `Δ/(D+χ)`.  This is a candidate barrier model; it uses no
per-nucleus fit.
-/

noncomputable section
namespace PMAtoms

/-- Leading E8 fissility cost. -/
def fissionFissilityCost (p : Nuclide) : ℝ :=
  ((Δ : ℝ) ^ 2) / (((ν + D + σ + χ : Nat)) : ℝ) -
    ((σ : ℝ) * (χ : ℝ)) *
      (((p.Z : ℝ) ^ 2 / ((p.Z + p.N : Nat) : ℝ)) -
        (((Δ - D : Nat)) : ℝ))

theorem fissionFissilityCost_eq (p : Nuclide) :
    fissionFissilityCost p =
      1849 / 27 - 10 * (((p.Z : ℝ) ^ 2 / ((p.Z + p.N : Nat) : ℝ)) - 39) := by
  unfold fissionFissilityCost
  norm_num [Δ, ν, D, σ, χ, PMSubstrate.baseline]

/-- Asymmetric-fragment shell correction above `N=152`. -/
def fissionShellCorrection (p : Nuclide) : ℝ :=
  if 152 < p.N then shellWeight else 0

theorem fissionShellCorrection_eq (p : Nuclide) :
    fissionShellCorrection p =
      if 152 < p.N then 43 / 6 else 0 := by
  unfold fissionShellCorrection
  rw [shellWeight_eq]

/-- Full E8 fission cost. -/
noncomputable def fissionCostE8 (p : Nuclide) : ℝ :=
  fissionFissilityCost p - fissionShellCorrection p

/-- Fission activation weight. -/
noncomputable def fissionActivationE8 (p : Nuclide) : ℝ :=
  Real.exp (-(fissionCostE8 p))

theorem fissionActivationE8_pos (p : Nuclide) : 0 < fissionActivationE8 p := by
  unfold fissionActivationE8
  positivity

/-- Fission rate with the E8 fissility and shell costs. -/
noncomputable def fissionRateE8 (p : Nuclide) : ℝ :=
  alphaAttempt p * fissionActivationE8 p

theorem fissionRateE8_pos {p : Nuclide} (hZ : 0 < p.Z) (hN : 0 < p.N) :
    0 < fissionRateE8 p :=
  mul_pos (alphaAttempt_pos hZ hN) (fissionActivationE8_pos p)

/-- Fission lifetime. -/
noncomputable def fissionLifetimeE8 (p : Nuclide) : ℝ :=
  1 / fissionRateE8 p

/-- E8 fissility slope `σχ`. -/
def fissionFissilitySlope : ℝ := (σ : ℝ) * (χ : ℝ)

theorem fissionFissilitySlope_eq : fissionFissilitySlope = 10 := by
  unfold fissionFissilitySlope
  norm_num [σ, χ, PMSubstrate.baseline]

/-- E8 fissility threshold `Δ−D`. -/
def fissionFissilityThreshold : ℝ := ((Δ - D : Nat) : ℝ)

theorem fissionFissilityThreshold_eq : fissionFissilityThreshold = 39 := by
  unfold fissionFissilityThreshold
  norm_num [Δ, D, PMSubstrate.baseline]

/-- E8 fission scale. -/
def fissionScale : ℝ :=
  ((Δ : ℝ) ^ 2) / (((ν + D + σ + χ : Nat)) : ℝ)

theorem fissionScale_eq : fissionScale = 1849 / 27 := by
  unfold fissionScale
  norm_num [Δ, ν, D, σ, χ, PMSubstrate.baseline]

/-- E8 asymmetric-fragment shell weight. -/
def fissionFragmentShellWeight : ℝ := shellWeight

theorem fissionFragmentShellWeight_eq : fissionFragmentShellWeight = 43 / 6 := by
  unfold fissionFragmentShellWeight
  rw [shellWeight_eq]

/-- Explicit E8 form of the fissility cost. -/
theorem fissionFissilityCost_eq_E8 (p : Nuclide) :
    fissionFissilityCost p =
      fissionScale - fissionFissilitySlope *
        (((p.Z : ℝ) ^ 2 / ((p.Z + p.N : Nat) : ℝ)) -
          fissionFissilityThreshold) := by
  unfold fissionFissilityCost fissionScale fissionFissilitySlope fissionFissilityThreshold
  ring

/-- Shell trigger at the N=152 closure. -/
theorem fissionShellCorrection_cf250 : fissionShellCorrection ⟨98, 152⟩ = 0 := by
  unfold fissionShellCorrection
  norm_num

theorem fissionShellCorrection_cf252 : fissionShellCorrection cf252 = 43 / 6 := by
  unfold fissionShellCorrection cf252
  rw [shellWeight_eq]
  norm_num

theorem fissionShellCorrection_fm252 : fissionShellCorrection ⟨100, 152⟩ = 0 := by
  unfold fissionShellCorrection
  norm_num

theorem fissionShellCorrection_fm254 : fissionShellCorrection ⟨100, 154⟩ = 43 / 6 := by
  unfold fissionShellCorrection
  rw [shellWeight_eq]
  norm_num

end PMAtoms
