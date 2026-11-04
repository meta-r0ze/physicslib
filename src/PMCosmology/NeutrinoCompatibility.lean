import PMElementaryParticles.NeutrinoContext

/-! Apply upstream exclusions to Paper VI's proposed contextual neutrino law.
Benchmarks are frozen inputs from the earlier audit, not current observations.
No alternate propagation spectrum or cosmological likelihood is derived. -/
noncomputable section
namespace PMCosmology.NeutrinoCompatibility
open PMConstants.FloorNeutrino

/-- A small mass sum alone is not a successful oscillation spectrum. -/
theorem small_sum_and_bad_splittings :
    PMConstants.Bulk.floorMass PMConstants.CertifiedConstants.α meEV +
      PMConstants.Bulk.floorMass PMConstants.CertifiedConstants.α meEV/43 +
      PMConstants.Bulk.floorMass PMConstants.CertifiedConstants.α meEV/43^2 < 0.0095 ∧
    17 < ((6*PMElementaryParticles.NeutrinoContext.mRest)^2-PMElementaryParticles.NeutrinoContext.mRest^2-
      0.002534)/0.000025 :=
  ⟨tower_sum, PMElementaryParticles.NeutrinoContext.weak_minus_rest_excluded⟩

/-- A common response factor, including six, cannot fit both fixed
oscillation windows even when all possible pairwise gaps may be relabeled. -/
theorem no_common_scale_fits_windows (base scale : ℝ) (h : scale*base ≠ 0)
    (i j : Fin 3) :
    ¬ (0.0024 ≤ gaps base scale i ∧ gaps base scale i ≤ 0.0027 ∧
       0.00007 ≤ gaps base scale j ∧ gaps base scale j ≤ 0.00008) := by
  rintro ⟨ha, hb, hc, hd⟩
  apply no_moderate_gap_ratio base scale h i j
  have hj : 0 < gaps base scale j := by linarith
  constructor
  · apply (lt_div_iff₀ hj).mpr
    linarith
  · apply (div_lt_iff₀ hj).mpr
    linarith

end PMCosmology.NeutrinoCompatibility
