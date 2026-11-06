import PMAtoms.BetaCalibration
import PMAtoms.BetaLattice
import PMAtoms.NuclearPacking3D
import PMAtoms.Invariants
import PMElementaryParticles.CompositeMasses
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Neutron beta prediction from the minimal E8 cube

The minimal volume-persistent cube is `3×3×3` (`cube_interior_iff`).  The
neutron Q-window fixes the spectral cutoff between the lowest and second mode,
so only the lowest mode is open.  The spectral fraction is then the finite
Boltzmann weight ratio, and the lifetime follows from `betaHazardE8`.
-/

noncomputable section
namespace PMAtoms

/-- Minimal volume-persistent cube. -/
def neutronCube : Nat := 3

/-- Neutron cutoff in `m_e` units, near the endpoint `m_n − m_p`. -/
def neutronCutoff : ℝ := 253 / 100

theorem neutronCube_minimal : ¬ (∃ v, cubeInterior 2 v) := by
  rw [cube_interior_iff]
  norm_num

/-- Finite spectral fraction for the minimal cube and neutron cutoff. -/
def neutronSpectralFraction : ℝ :=
  betaSpectralRateCutoff 1 1 neutronCube neutronCutoff

theorem neutronSpectralFraction_eq :
    neutronSpectralFraction =
      betaSpectralRate 1 1 neutronCube
        (betaOpenModes neutronCube neutronCutoff) := rfl

/-- Candidate neutron lifetime from the E8 hazard and finite spectral fraction. -/
def neutronLifetimeE8 : ℝ :=
  betaLifetimeFromFraction betaHazardE8 neutronSpectralFraction

theorem neutronLifetimeE8_eq :
    neutronLifetimeE8 = 1 / (betaHazardE8 * neutronSpectralFraction) := rfl

theorem neutronLifetimeE8_pos (hf : 0 < neutronSpectralFraction) :
    0 < neutronLifetimeE8 :=
  betaLifetimeFromFraction_pos betaHazardE8_pos hf

/-- Exact neutron endpoint `m_n − m_p` in `m_e` units. -/
noncomputable def neutronCutoffExact : ℝ :=
  PMElementaryParticles.CompositeMasses.neutron -
    PMElementaryParticles.CompositeMasses.proton

/-- Exact-cutoff spectral fraction; the open set automatically includes any
higher mode that crosses the cutoff. -/
noncomputable def neutronSpectralFractionExact : ℝ :=
  betaSpectralRateCutoff 1 1 neutronCube neutronCutoffExact

/-- Exact-cutoff lifetime. -/
noncomputable def neutronLifetimeExactCutoff : ℝ :=
  betaLifetimeFromFraction betaHazardE8 neutronSpectralFractionExact

/-- E8 margin factor `1 − χ/Δ = 41/43`. -/
def neutronMarginFactor : ℝ :=
  (((Δ - χ : Nat)) : ℝ) / (Δ : ℝ)

theorem neutronMarginFactor_eq : neutronMarginFactor = 41 / 43 := by
  unfold neutronMarginFactor
  norm_num [Δ, χ, PMSubstrate.baseline]

theorem neutronMarginFactor_pos : 0 < neutronMarginFactor := by
  rw [neutronMarginFactor_eq]; norm_num

/-- Margin-corrected endpoint prediction. -/
def neutronLifetimeCorrected : ℝ :=
  neutronMarginFactor * neutronLifetimeExactCutoff

theorem neutronLifetimeCorrected_eq :
    neutronLifetimeCorrected =
      neutronMarginFactor * neutronLifetimeExactCutoff := rfl

end PMAtoms
