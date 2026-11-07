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


/-- At the muon cutoff every `3×3×3` mode is open. -/
theorem muon_openModes : betaOpenModes 3 PMElementaryParticles.LeptonMasses.muon = Finset.univ := by
  apply betaOpenModes_eq_univ_of_twelve_le
  linarith [PMElementaryParticles.LeptonMasses.muon_value.1]

/-- The muon finite spectral fraction is exactly one. -/
theorem muonSpectralFraction_eq_one : muonSpectralFraction = 1 := by
  unfold muonSpectralFraction betaSpectralRateCutoff
  rw [muon_openModes]
  unfold betaSpectralRate betaWeightedRate
  have hpos : (0 : ℝ) <
      ∑ i : Fin 3 × (Fin 3 × Fin 3),
        betaSpectralWeight 3 (i.1.val + 1) (i.2.1.val + 1) (i.2.2.val + 1) := by
    apply Finset.sum_pos
    · intro i _; exact betaSpectralWeight_pos 3 _ _ _
    · exact Finset.univ_nonempty
  simp only [one_mul]
  rw [div_self hpos.ne']

/-- The finite-channel muon width is the continuum muon width. -/
theorem muonFiniteWidth_eq : muonFiniteWidth = PMElementaryParticles.MuonLifetime.muonWidth := by
  unfold muonFiniteWidth
  rw [muonSpectralFraction_eq_one, mul_one]

/-- The finite-channel muon lifetime is the continuum muon lifetime. -/
theorem muonFiniteLifetime_eq_continuum :
    muonFiniteLifetime = PMElementaryParticles.MuonLifetime.muonLifetime := by
  unfold muonFiniteLifetime
  rw [muonFiniteWidth_eq]
  rfl

/-- Certified broad enclosure of the finite-channel muon lifetime. -/
theorem muonFiniteLifetime_bounds :
    (1.25e15 : ℝ) < muonFiniteLifetime ∧ muonFiniteLifetime < 2.5e15 := by
  rw [muonFiniteLifetime_eq_continuum]
  exact PMElementaryParticles.MuonLifetime.muonLifetime_bounds

end PMAtoms
