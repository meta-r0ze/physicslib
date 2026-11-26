import PMHadrons.KaonWidth
import PMHadrons.MesonMasses
import PMElementaryParticles.MassiveWidth
import Mathlib.Tactic

/-!

# Leading-order `K_ℓ3` (`K⁺ → π⁰ ℓ⁺ ν`) width

The semileptonic kaon modes are not blocked by a bound-state wavefunction at
leading order. With the vector form factor at zero momentum transfer set to its
flavour-symmetric value `f₊(0) = 1` (the corrections start at second order in the
`s`–`u` mass difference, Ademollo–Gatto) and `m_ℓ → 0`, the width is

```
Γ(K⁺ → π⁰ ℓ⁺ ν) = G_F² |V_us|² m_K⁵ · ½ · (phase(z)/4) / (192π³),
```

where `z = (m_π⁰/m_K⁺)²` uses the neutral-pion and charged-kaon substrate
masses. Here `phase` is the muon-decay phase-space function
(`PMElementaryParticles.MassiveWidth.phase`): the `λ^{3/2}` Dalitz integral equals
`phase(z)/4` exactly.

The inventory records this as a leading-order rate. Finite charged-lepton
phase space, form factors, and radiative and isospin corrections are open.
-/

noncomputable section
namespace PMHadrons.KaonSemileptonic
open PMHadrons.CompositeMasses PMHadrons.KaonWidth PMHadrons.MesonMasses
open PMElementaryParticles

/-- The mass-squared ratio for the neutral pion in this channel. -/
noncomputable def l3Z : ℝ := (pion0 / kaonPlus) ^ 2

theorem l3Z_nonneg : 0 ≤ l3Z := by
  unfold l3Z; positivity

theorem l3Z_lt_one : l3Z < 1 := by
  have hp := pion0_value; have hk := kaonPlus_value
  have hp0 : 0 < pion0 := lt_trans (by norm_num) hp.1
  have hk0 : 0 < kaonPlus := lt_trans (by norm_num) hk.1
  have hlt : pion0 < kaonPlus := by nlinarith [hp.2, hk.1]
  unfold l3Z
  exact pow_lt_one₀ (div_nonneg hp0.le hk0.le) ((div_lt_one hk0).mpr hlt) (n := 2) (by norm_num)

theorem l3Z_lt_charged_ratio : l3Z < (pionPlus / kaonPlus) ^ 2 := by
  have hp : 0 < pion0 := by linarith [pion0_value.1]
  have hk : 0 < kaonPlus := by linarith [kaonPlus_value.1]
  have hlt : pion0 < pionPlus := by linarith [pion0_value.2, pionPlus_value.1]
  unfold l3Z
  exact pow_lt_pow_left₀ (div_lt_div_of_pos_right hlt hk)
    (div_nonneg hp.le hk.le) two_ne_zero

/-- The `K_ℓ3` phase-space factor `phase(z)/4` (the `λ^{3/2}` Dalitz integral). -/
noncomputable def l3PhaseSpace : ℝ := MassiveWidth.phase l3Z / 4

theorem l3PhaseSpace_pos : 0 < l3PhaseSpace := by
  unfold l3PhaseSpace
  exact div_pos (MassiveWidth.phase_positive l3Z l3Z_nonneg l3Z_lt_one) (by norm_num)

/-- Leading-order `K_ℓ3` partial width in `m_e` units (form-factor free, `m_ℓ → 0`). -/
noncomputable def kaonL3Width : ℝ :=
  (PMConstants.Values.fermi 1) ^ 2 * vusE8 ^ 2 * kaonPlus ^ 5 * (1 / 2) *
    l3PhaseSpace / (192 * Real.pi ^ 3)

theorem kaonL3Width_pos : 0 < kaonL3Width := by
  have hF : 0 < (PMConstants.Values.fermi 1) :=
    PMElementaryParticles.SharedUnits.fermiME_pos
  have hv : 0 < vusE8 := lt_trans (by norm_num) vusE8_bounds.1
  have hk0 : 0 < kaonPlus := lt_trans (by norm_num) kaonPlus_value.1
  unfold kaonL3Width
  apply div_pos
  · exact mul_pos (mul_pos (mul_pos (mul_pos (pow_pos hF 2) (pow_pos hv 2))
      (pow_pos hk0 5)) (by norm_num)) l3PhaseSpace_pos
  · positivity

end PMHadrons.KaonSemileptonic
