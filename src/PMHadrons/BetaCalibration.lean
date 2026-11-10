import PMElementaryParticles.BetaLattice
import PMHadrons.NeutronRate
import PMElementaryParticles.MuonLifetime
import PMSubstrate.E8Values
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Beta hazard from the E8 weak link

The finite spectral beta rate is

```
rate = h · f,
```

where `f` is the spectral open-weight fraction and `h = β·c0` is the substrate
weak-transition hazard.  The candidate E8 calibration is

```
h = G_F²/(σ−χ) = G_F²/3,
```

with `G_F` the E8-derived Fermi constant in `m_e⁻²` and `σ−χ` the interaction
remainder.  This is a candidate, not a fitted number.
-/

noncomputable section
namespace PMHadrons
open PMElementaryParticles

open PMHadrons.NeutronRate
open PMSubstrate

/-- Squared weak contact amplitude, in `m_e⁻⁴`. -/
def weakAmplitudeSquared : ℝ := fermiME ^ 2

theorem weakAmplitudeSquared_pos : 0 < weakAmplitudeSquared := by
  unfold weakAmplitudeSquared
  exact sq_pos_of_pos fermiME_pos

/-- One weak transition channel: the interaction remainder `σ−χ = 3`. -/
def weakChannelCost : ℝ :=
  1 / (((PMSubstrate.E8Values.sigma - PMSubstrate.E8Values.chi : Nat)) : ℝ)

theorem weakChannelCost_eq : weakChannelCost = 1 / 3 := by
  unfold weakChannelCost
  norm_num [PMSubstrate.E8Values.sigma, PMSubstrate.E8Values.chi,
    PMSubstrate.baseline]

theorem weakChannelCost_pos : 0 < weakChannelCost := by
  rw [weakChannelCost_eq]
  norm_num

/-- Candidate E8 beta hazard: squared weak amplitude times the channel cost. -/
def betaHazardE8 : ℝ := weakAmplitudeSquared * weakChannelCost

theorem betaHazardE8_eq :
    betaHazardE8 = fermiME ^ 2 / 3 := by
  unfold betaHazardE8 weakAmplitudeSquared weakChannelCost
  norm_num [PMSubstrate.E8Values.sigma, PMSubstrate.E8Values.chi,
    PMSubstrate.baseline]
  ring

theorem betaHazardE8_pos : 0 < betaHazardE8 := by
  unfold betaHazardE8
  exact mul_pos weakAmplitudeSquared_pos weakChannelCost_pos

/-- Broad certified enclosure of the E8 beta hazard. -/
theorem betaHazardE8_bounds :
    (2.8e-24 : ℝ) < betaHazardE8 ∧ betaHazardE8 < 3.42e-24 := by
  rw [betaHazardE8_eq]
  have h := PMElementaryParticles.MuonLifetime.fermiME_bounds
  constructor <;> nlinarith [h.1, h.2]

/-- Lifetime from a hazard and a spectral fraction. -/
def betaLifetimeFromFraction (h f : ℝ) : ℝ := 1 / (h * f)

theorem betaLifetimeFromFraction_pos {h f : ℝ} (hh : 0 < h) (hf : 0 < f) :
    0 < betaLifetimeFromFraction h f := by
  unfold betaLifetimeFromFraction
  positivity

/-- Candidate neutron lifetime from the E8 hazard and a spectral fraction. -/
def betaNeutronLifetimeE8 (f : ℝ) : ℝ :=
  betaLifetimeFromFraction betaHazardE8 f

theorem betaNeutronLifetimeE8_pos {f : ℝ} (hf : 0 < f) :
    0 < betaNeutronLifetimeE8 f :=
  betaLifetimeFromFraction_pos betaHazardE8_pos hf

end PMHadrons
