import PMAtoms.AlphaHindrance
import PMAtoms.SingleParticle
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Configuration-mixing hindrance for alpha decay

The smooth and spin-parity terms are not enough for the odd-A outliers.  A simple
Nilsson two-level mixing model uses the E8 parameters

```
κ = 1/ν,  μ = χ/σ,  δ = 1/σ
```

and the level gap `|E_parent − E_daughter|`.  The odd-A hindrance is

```
σ / (gap + 1/χ).
```

Even-even transitions get zero hindrance.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

def alphaKappa : ℝ := 1 / (ν : ℝ)
def alphaMu : ℝ := (χ : ℝ) / (σ : ℝ)
def alphaDelta : ℝ := 1 / (σ : ℝ)

theorem alphaKappa_eq : alphaKappa = 1 / 16 := by
  unfold alphaKappa; norm_num [ν, PMSubstrate.baseline]
theorem alphaMu_eq : alphaMu = 2 / 5 := by
  unfold alphaMu; norm_num [χ, σ, PMSubstrate.baseline]
theorem alphaDelta_eq : alphaDelta = 1 / 5 := by
  unfold alphaDelta; norm_num [σ, PMSubstrate.baseline]

/-- Nilsson gap between parent and daughter orbitals. -/
noncomputable def alphaNilssonGap (parent daughter : NuclearOrbital) : ℝ :=
  |nilssonEnergy alphaKappa alphaMu alphaDelta parent -
    nilssonEnergy alphaKappa alphaMu alphaDelta daughter|

theorem alphaNilssonGap_nonneg (parent daughter : NuclearOrbital) :
    0 ≤ alphaNilssonGap parent daughter := abs_nonneg _

/-- Odd-A configuration-mixing hindrance. -/
noncomputable def alphaMixingHindrance (parent daughter : NuclearOrbital) : ℝ :=
  (σ : ℝ) / (alphaNilssonGap parent daughter + 1 / (χ : ℝ))

theorem alphaMixingHindrance_pos (parent daughter : NuclearOrbital) :
    0 < alphaMixingHindrance parent daughter := by
  unfold alphaMixingHindrance
  apply div_pos
  · norm_num [σ, PMSubstrate.baseline]
  · have hg := alphaNilssonGap_nonneg parent daughter
    have hc : 0 < 1 / (χ : ℝ) := by norm_num [χ, PMSubstrate.baseline]
    linarith

/-- Apply mixing only to odd-A parents. -/
noncomputable def alphaOddAHindrance (parent daughter : NuclearOrbital)
    (p : Nuclide) : ℝ :=
  if (p.Z + p.N) % 2 = 1 then alphaMixingHindrance parent daughter else 0

/-- Configured alpha cost. -/
noncomputable def alphaCostConfigured (parent daughter : NuclearOrbital)
    (p : Nuclide) : ℝ :=
  alphaCostQ2 p + alphaOddAHindrance parent daughter p

noncomputable def alphaActivationConfigured (parent daughter : NuclearOrbital)
    (p : Nuclide) : ℝ :=
  Real.exp (-(alphaCostConfigured parent daughter p))

theorem alphaActivationConfigured_pos (parent daughter : NuclearOrbital)
    (p : Nuclide) : 0 < alphaActivationConfigured parent daughter p := by
  unfold alphaActivationConfigured
  positivity

noncomputable def alphaRateConfigured (parent daughter : NuclearOrbital)
    (p : Nuclide) : ℝ :=
  alphaAttempt p * alphaActivationConfigured parent daughter p

theorem alphaRateConfigured_pos (parent daughter : NuclearOrbital) (p : Nuclide)
    (hZ : 0 < p.Z) (hN : 0 < p.N) :
    0 < alphaRateConfigured parent daughter p :=
  mul_pos (alphaAttempt_pos hZ hN)
    (alphaActivationConfigured_pos parent daughter p)

noncomputable def alphaLifetimeConfigured (parent daughter : NuclearOrbital)
    (p : Nuclide) : ℝ :=
  1 / alphaRateConfigured parent daughter p

/-- E8-normalized form of the mixing hindrance. -/
theorem alphaMixingHindrance_eq (parent daughter : NuclearOrbital) :
    alphaMixingHindrance parent daughter =
      ((σ : ℝ) * (χ : ℝ)) /
        ((χ : ℝ) * alphaNilssonGap parent daughter + 1) := by
  unfold alphaMixingHindrance
  have hχ : (χ : ℝ) ≠ 0 := by norm_num [χ, PMSubstrate.baseline]
  field_simp [hχ]

/-- Even-even parents have no configuration hindrance. -/
theorem alphaCostConfigured_evenEven (parent daughter : NuclearOrbital)
    (p : Nuclide) (h : (p.Z + p.N) % 2 = 0) :
    alphaCostConfigured parent daughter p = alphaCostQ2 p := by
  unfold alphaCostConfigured alphaOddAHindrance
  rw [ite_eq_right]
  · ring
  · omega

/-- Two-level E8 mixing Hamiltonian. -/
def alphaTwoLevel (gap V : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![gap, V; V, 0]

/-- Scalar mixing resolvent `(1 + χ·gap)⁻¹`. -/
noncomputable def alphaMixingResolvent (gap : ℝ) : ℝ :=
  (1 + (χ : ℝ) * gap)⁻¹

/-- The hindrance is the E8 channel weight times the scalar mixing resolvent. -/
theorem alphaMixingHindrance_eq_resolvent (parent daughter : NuclearOrbital) :
    alphaMixingHindrance parent daughter =
      (σ : ℝ) * (χ : ℝ) *
        alphaMixingResolvent (alphaNilssonGap parent daughter) := by
  unfold alphaMixingHindrance alphaMixingResolvent
  have hχ : (χ : ℝ) ≠ 0 := by norm_num [χ, PMSubstrate.baseline]
  field_simp [hχ]
  ring

/-- E8 two-level coupling `V = κμδ = 1/200`. -/
def alphaMixingV : ℝ := alphaKappa * alphaMu * alphaDelta

theorem alphaMixingV_eq : alphaMixingV = 1 / 200 := by
  unfold alphaMixingV
  rw [alphaKappa_eq, alphaMu_eq, alphaDelta_eq]
  norm_num

/-- Upper dressed two-level gap. -/
noncomputable def alphaMixedGap (gap V : ℝ) : ℝ :=
  (gap + Real.sqrt (gap ^ 2 + 4 * V ^ 2)) / 2

theorem alphaMixedGap_zero (gap : ℝ) (h : 0 ≤ gap) :
    alphaMixedGap gap 0 = gap := by
  unfold alphaMixedGap
  rw [show gap ^ 2 + 4 * (0 : ℝ) ^ 2 = gap ^ 2 by ring]
  rw [Real.sqrt_sq h]
  ring

/-- Full two-level mixing hindrance using the dressed gap. -/
noncomputable def alphaMixingHindranceFull (parent daughter : NuclearOrbital)
    (V : ℝ) : ℝ :=
  ((σ : ℝ) * (χ : ℝ)) /
    ((χ : ℝ) * alphaMixedGap (alphaNilssonGap parent daughter) V + 1)

theorem alphaMixingHindranceFull_zero (parent daughter : NuclearOrbital) :
    alphaMixingHindranceFull parent daughter 0 =
      alphaMixingHindrance parent daughter := by
  unfold alphaMixingHindranceFull alphaMixingHindrance
  rw [alphaMixedGap_zero _ (alphaNilssonGap_nonneg parent daughter)]
  have hχ : (χ : ℝ) ≠ 0 := by norm_num [χ, PMSubstrate.baseline]
  field_simp [hχ]

noncomputable def alphaOddAHindranceFull (V : ℝ)
    (parent daughter : NuclearOrbital) (p : Nuclide) : ℝ :=
  if (p.Z + p.N) % 2 = 1 then alphaMixingHindranceFull parent daughter V else 0

noncomputable def alphaCostConfiguredFull (V : ℝ)
    (parent daughter : NuclearOrbital) (p : Nuclide) : ℝ :=
  alphaCostQ2 p + alphaOddAHindranceFull V parent daughter p

noncomputable def alphaLifetimeConfiguredFull (V : ℝ)
    (parent daughter : NuclearOrbital) (p : Nuclide) : ℝ :=
  1 / (alphaAttempt p * Real.exp (-(alphaCostConfiguredFull V parent daughter p)))

end PMAtoms
