import PMElementaryParticles.Values

/-!
# Quark-mass measured pulls (moved from the PMElementaryParticles leaf)

The E8 quark-mass formulas and their E8-only enclosures stay in
`PMElementaryParticles.QuarkMasses` and are read here through `PMElementaryParticles.Values`; the PDG 2024 pull comparisons live here.

`m_u = 2.16(7)`, `m_d = 4.70(7)`, `m_s = 93.5(8)` MeV; `m_c = 1273.0(46)`,
`m_b = 4183(7)`, `m_t = 172570(290)` MeV.
-/

noncomputable section
namespace E8PConstants.QuarkMassPulls
open PMElementaryParticles.Values

theorem pulls :
    (-1.5 < (up * me - 2.16) / 0.07 ∧ (up * me - 2.16) / 0.07 < -1.4) ∧
    (-1.1 < (down * me - 4.70) / 0.07 ∧ (down * me - 4.70) / 0.07 < -1.0) ∧
    (0 < (strange * me - 93.5) / 0.8 ∧ (strange * me - 93.5) / 0.8 < 0.1) ∧
    (-1.3 < (charm * me - 1273.0) / 4.6 ∧ (charm * me - 1273.0) / 4.6 < -1.2) ∧
    (-0.3 < (bottom * me - 4183) / 7 ∧ (bottom * me - 4183) / 7 < -0.1) ∧
    (0.3 < (top * me - 172570) / 290 ∧ (top * me - 172570) / 290 < 0.4) := by
  have := up_value; have := down_value; have := strange_value
  have := charm_value; have := bottom_value; have := top_value
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    first
    | (rw [lt_div_iff₀ (by norm_num)]; linarith)
    | (rw [div_lt_iff₀ (by norm_num)]; linarith)

end E8PConstants.QuarkMassPulls
