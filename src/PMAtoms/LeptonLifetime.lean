import PMAtoms.BetaLattice
import PMElementaryParticles.MuonLifetime
import PMElementaryParticles.LeptonMasses
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Finite lepton spectral channel

The muon uses the same minimal-cube spectral family as beta.  At the muon mass
the cutoff opens the full `3×3×3` spectrum, so the finite fraction is close to
one.  The mass/phase-space coefficient remains the one proved in
`PMElementaryParticles.MuonRate`.
-/

noncomputable section
namespace PMAtoms

/-- Minimal-cube muon spectral fraction. -/
noncomputable def muonSpectralFraction : ℝ :=
  betaSpectralRateCutoff 1 1 3 PMElementaryParticles.LeptonMasses.muon

/-- Finite-channel muon width. -/
noncomputable def muonFiniteWidth : ℝ :=
  PMElementaryParticles.MuonLifetime.muonWidth * muonSpectralFraction

/-- Finite-channel muon lifetime. -/
noncomputable def muonFiniteLifetime : ℝ :=
  1 / muonFiniteWidth

theorem muonFiniteLifetime_eq :
    muonFiniteLifetime =
      1 / (PMElementaryParticles.MuonLifetime.muonWidth * muonSpectralFraction) := rfl

end PMAtoms
