import PMAction.ContactRunning

/-!
# Muon decay has no radiative log: its correction is one pure number

`PMAction.ContactRunning` gives the one-loop photon running of a charged-current contact
`[ψ̄₁Γψ₂][ψ̄₃Γψ₄]` as `1 + c·(α/4π)·ln(M²/μ²)` in the amplitude. For muon decay the legs are
`(ν_μ, μ)` and `(e, ν_e)`, charges `(0, −1, −1, 0)`, and `c = 0` (`leptonic_no_log`). In the
charge-retention order `[ēΓμ][ν̄_μΓν_e]` (the `V − A` contact is Fierz-invariant, `PMAction.ContactFierz`)
the two charged legs share one bilinear with equal charges, a conserved current, and `c = 0` again
(`retention_no_log`): the Ward identity term `½(Q₁ − Q₂)²` vanishes and no photon joins the two
bilinears.

So the muon's radiative factor does not depend on the window between the W scale and the decay
scale: it is a single number, `q = 1 − (α/2π)(π² − 25/4)` (`MuonLifetimeCorrected`, supplied), and
deriving it means computing the finite one-loop dressing of the `e–μ` current, not a log
(EP REVIEW, radiative factor). Contrast the semileptonic case, `c = 3Q` (`contact_semileptonic`).
-/

namespace PMElementaryParticles.MuonRadiativeLog
open PMAction.ContactRunning

theorem leptonic_no_log : contactCoefficient 0 (-1) (-1) 0 = 0 := by
  unfold contactCoefficient sameWeight oppositeWeight
  norm_num

theorem retention_no_log : contactCoefficient (-1) (-1) 0 0 = 0 := by
  unfold contactCoefficient sameWeight oppositeWeight
  norm_num

/-- The rate factor of muon decay is `1` at leading log, at every window `L`. -/
theorem rate_factor_one (α L : ℝ) :
    1 + 2 * contactCoefficient 0 (-1) (-1) 0 * (α / (4 * Real.pi)) * L = 1 := by
  rw [leptonic_no_log]; ring

end PMElementaryParticles.MuonRadiativeLog
