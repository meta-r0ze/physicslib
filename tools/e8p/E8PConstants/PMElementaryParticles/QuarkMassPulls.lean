import PMHadrons.CompositeMasses
import PMElementaryParticles.QuarkMasses

/-!
# Quark-mass measured pulls (moved from the PMElementaryParticles leaf)

The E8 quark-mass formulas and their E8-only enclosures stay in
`PMElementaryParticles.QuarkMasses`; the PDG 2024 pull comparisons live here.

`m_u = 2.16(7)`, `m_d = 4.70(7)`, `m_s = 93.5(8)` MeV; `m_c = 1273.0(46)`,
`m_b = 4183(7)`, `m_t = 172570(290)` MeV.
-/

noncomputable section
namespace E8PConstants.QuarkMassPulls
open PMElementaryParticles PMElementaryParticles.QuarkMasses
open PMHadrons.CompositeMasses

theorem pulls :
    (-1.5 < (up * me - 2.16) / 0.07 ∧ (up * me - 2.16) / 0.07 < -1.4) ∧
    (-1.1 < (down * me - 4.70) / 0.07 ∧ (down * me - 4.70) / 0.07 < -1.0) ∧
    (0 < (strange * me - 93.5) / 0.8 ∧ (strange * me - 93.5) / 0.8 < 0.1) ∧
    (-1.3 < (charm * me - 1273.0) / 4.6 ∧ (charm * me - 1273.0) / 4.6 < -1.2) ∧
    (-0.3 < (bottom * me - 4183) / 7 ∧ (bottom * me - 4183) / 7 < -0.1) ∧
    (0.3 < (top * me - 172570) / 290 ∧ (top * me - 172570) / 290 < 0.4) := by
  unfold up down strange charm bottom top η me
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.overhead_eq]
  norm_num

end E8PConstants.QuarkMassPulls
