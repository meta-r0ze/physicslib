import PMElementaryParticles.BetaLattice
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Lepton spectral channel

The finite E8 beta channel is reused for lepton decays.  This replaces the
continuum contact/phase-space treatment of `MuonRate`/`MassiveDaughterSpectrum`
with the same finite spectral family.  The channel weights still need a lepton
eigenvalue input; the structural rate and lifetime are shared with `BetaLattice`.
-/

noncomputable section
namespace PMElementaryParticles

/-- A lepton spectral channel is a finite `BetaLatticeChannel`. -/
abbrev LeptonLatticeChannel := BetaLatticeChannel

def leptonLatticeRate (β c0 : ℝ) (c : LeptonLatticeChannel) : ℝ :=
  betaLatticeRate β c0 c

theorem leptonLatticeRate_eq (β c0 : ℝ) (c : LeptonLatticeChannel) :
    leptonLatticeRate β c0 c =
      β * c0 * (c.active : ℝ) / (c.size : ℝ) :=
  betaLatticeRate_eq β c0 c

def leptonLatticeLifetime (β c0 : ℝ) (c : LeptonLatticeChannel) : ℝ :=
  betaLatticeLifetime β c0 c

theorem leptonLatticeLifetime_eq (β c0 : ℝ) (c : LeptonLatticeChannel) :
    leptonLatticeLifetime β c0 c = 1 / leptonLatticeRate β c0 c :=
  betaLatticeLifetime_eq β c0 c

theorem leptonLatticeRate_pos (β c0 : ℝ) (c : LeptonLatticeChannel)
    (hβ : 0 < β) (hc0 : 0 < c0) (hactive : 0 < c.active) :
    0 < leptonLatticeRate β c0 c :=
  betaLatticeRate_pos β c0 c hβ hc0 hactive

end PMElementaryParticles
