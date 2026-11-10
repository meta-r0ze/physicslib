import PMAtoms.NuclearLedger
import PMAtoms.CollectiveRegime
import PMAtoms.Nucleus
import PMElementaryParticles.MeanLife
import PMAtoms.FermiFunction
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! **Continuum comparison.** This uses a continuum beta phase-space integral and is not an E8 assumption. The E8-native route is `PMElementaryParticles.BetaLattice`.

 **Experimental/candidate module.** Not part of `certifiedMass`.

# Nuclear beta decay

A nuclear beta channel is

```
(Z,N) → (Z+1,N−1) + e⁻ + ν̄
```

The mass ledger uses the certified smooth mass; the rate is the same contact
width as the neutron, with a supplied nuclear matrix element `M` and phase-space
factor `f`.  The module fixes the channel and the width factorization; it does
not insert measured half-lives.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

/-- Daughter of `β⁻` decay. -/
def betaDaughter (p : Nuclide) : Nuclide := ⟨p.Z + 1, p.N - 1⟩

theorem betaDaughter_massNumber (p : Nuclide) (hN : 0 < p.N) :
    (betaDaughter p).massNumber = p.massNumber := by
  simp only [betaDaughter, Nuclide.massNumber]
  omega

theorem betaDaughter_charge (p : Nuclide) :
    (betaDaughter p).charge = p.charge + 1 := by
  unfold betaDaughter Nuclide.charge
  simp

/-- Beta `Q` value in `m_e` units, using the certified smooth mass. -/
def betaQ (p : Nuclide) : ℝ :=
  certifiedMass p.Z p.N - certifiedMass (p.Z + 1) (p.N - 1) - 1

/-- A beta channel is allowed when there is a neutron and positive `Q`. -/
def betaAllowed (p : Nuclide) : Prop :=
  0 < p.N ∧ 0 < betaQ p

/-- Collective mass ledger for the beta channel: daughter plus electron. -/
noncomputable def betaChannel (p : Nuclide) : CollectiveChannel :=
  { mass := certifiedMass (p.Z + 1) (p.N - 1) + 1
    barrier := 0 }

theorem betaChannel_totalMass (p : Nuclide) :
    (betaChannel p).totalMass = certifiedMass (p.Z + 1) (p.N - 1) + 1 := by
  simp [betaChannel, CollectiveChannel.totalMass]

/-- Beta width factorization: contact coupling, nuclear matrix element, and
phase space. -/
def betaWidth (G Vud M f : ℝ) : ℝ :=
  (G * Vud) ^ 2 * M ^ 2 * f / (2 * Real.pi ^ 3)

theorem betaWidth_eq (G Vud M f : ℝ) :
    betaWidth G Vud M f =
      (G * Vud) ^ 2 * M ^ 2 * f / (2 * Real.pi ^ 3) := rfl

theorem betaWidth_pos (G Vud M f : ℝ)
    (hG : G ≠ 0) (hV : Vud ≠ 0) (hM : M ≠ 0) (hf : 0 < f) :
    0 < betaWidth G Vud M f := by
  have hG2 : 0 < G ^ 2 := sq_pos_of_ne_zero hG
  have hV2 : 0 < Vud ^ 2 := sq_pos_of_ne_zero hV
  have hGV : 0 < (G * Vud) ^ 2 := by
    rw [mul_pow]
    exact mul_pos hG2 hV2
  have hM2 : 0 < M ^ 2 := sq_pos_of_ne_zero hM
  have hden : 0 < 2 * Real.pi ^ 3 := by positivity
  unfold betaWidth
  exact div_pos (mul_pos (mul_pos hGV hM2) hf) hden

/-- Nuclear beta mean life from the width. -/
def betaLifetime (G Vud M f : ℝ) : ℝ :=
  MeanLife (betaWidth G Vud M f)

theorem betaLifetime_eq (G Vud M f : ℝ) :
    betaLifetime G Vud M f = 1 / betaWidth G Vud M f := rfl


/-- Electron total-energy endpoint for a beta `Q` value in `m_e` units. -/
def betaEndpoint (q : ℝ) : ℝ := q + 1

theorem betaEndpoint_gt_one {q : ℝ} (hq : 0 < q) : 1 < betaEndpoint q := by
  unfold betaEndpoint
  linarith

/-- Beta phase-space integrand with a massive electron. -/
def betaPhaseIntegrand (q E : ℝ) : ℝ :=
  E * Real.sqrt (E ^ 2 - 1) * (betaEndpoint q - E) ^ 2

theorem betaPhaseIntegrand_continuous (q : ℝ) : Continuous (betaPhaseIntegrand q) := by
  unfold betaPhaseIntegrand
  fun_prop

theorem betaPhaseIntegrand_pos (q E : ℝ) (_hq : 0 < q)
    (h1 : 1 < E) (h2 : E < betaEndpoint q) : 0 < betaPhaseIntegrand q E := by
  have hE : 0 < E := by linarith
  have hs : 0 < Real.sqrt (E ^ 2 - 1) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hd : 0 < betaEndpoint q - E := by linarith
  unfold betaPhaseIntegrand
  positivity

/-- Beta phase-space integral. -/
def betaPhaseSpace (q : ℝ) : ℝ :=
  ∫ E in (1 : ℝ)..betaEndpoint q, betaPhaseIntegrand q E

theorem betaPhaseSpace_pos {q : ℝ} (hq : 0 < q) : 0 < betaPhaseSpace q := by
  unfold betaPhaseSpace
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((betaPhaseIntegrand_continuous q).intervalIntegrable _ _)
  · intro E hE
    exact betaPhaseIntegrand_pos q E hq hE.1 hE.2
  · exact betaEndpoint_gt_one hq

/-- Recoil/radiative-corrected beta width; `R` is the supplied correction and
`F` is the supplied Fermi function. -/
def betaWidthRecoil (G Vud M F R q : ℝ) : ℝ :=
  R * F * (G * Vud) ^ 2 * M ^ 2 * betaPhaseSpace q / (2 * Real.pi ^ 3)

theorem betaWidthRecoil_eq (G Vud M F R q : ℝ) :
    betaWidthRecoil G Vud M F R q =
      R * F * (G * Vud) ^ 2 * M ^ 2 * betaPhaseSpace q /
        (2 * Real.pi ^ 3) := rfl

theorem betaWidthRecoil_pos (G Vud M F R q : ℝ)
    (hG : G ≠ 0) (hV : Vud ≠ 0) (hM : M ≠ 0)
    (hF : 0 < F) (hR : 0 < R) (hq : 0 < q) :
    0 < betaWidthRecoil G Vud M F R q := by
  have hG2 : 0 < G ^ 2 := sq_pos_of_ne_zero hG
  have hV2 : 0 < Vud ^ 2 := sq_pos_of_ne_zero hV
  have hGV : 0 < (G * Vud) ^ 2 := by
    rw [mul_pow]
    exact mul_pos hG2 hV2
  have hM2 : 0 < M ^ 2 := sq_pos_of_ne_zero hM
  have hden : 0 < 2 * Real.pi ^ 3 := by positivity
  unfold betaWidthRecoil
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos hR hF) hGV) hM2)
    (betaPhaseSpace_pos hq)) hden

/-- Recoil/radiative-corrected beta mean life. -/
def betaLifetimeRecoil (G Vud M F R q : ℝ) : ℝ :=
  MeanLife (betaWidthRecoil G Vud M F R q)

theorem betaLifetimeRecoil_eq (G Vud M F R q : ℝ) :
    betaLifetimeRecoil G Vud M F R q =
      1 / betaWidthRecoil G Vud M F R q := rfl



end PMAtoms
