import PersistenceMechanics.DecayChannel
import PMHadrons.PionWidth
import PMHadrons.KaonWidth
import PMHadrons.NeutronPrediction
import PMSubstrate.E8Margin
import PMFlavor.Values
import PMElementaryParticles.Values
import Mathlib.Tactic

/-! **Consistency module.** Hadron decays in the `PersistenceMechanics.DecayChannel` template.

`rate = β · toll · capacity · map · protocol · governor · margin · exp(−action)`, as
`PMAtoms.DecayInstantiation` does for beta, alpha and fission. Each theorem recovers the existing
width; nothing numerical changes. Slots:

| factor | slot |
|---|---|
| `G_F²` (weak contact); `G_F²/3` for the beta hazard | toll |
| two-body phase space `m m_μ² (1 − m_μ²/m²)² / 8π` | capacity |
| emission overlap `f²`, CKM `|V|²` (identity overlap) | map |
| spectral open-mode fraction (beta) | protocol (as `PMAtoms.betaDecayChannel`) |
| surviving-phase fraction `41/43` (`PMAtoms.PersistenceComplex`: it is the Governor) | governor |
| pion-channel factor `32/33` | margin |

What the template shows:

* **Pion and kaon are filled differently.** The kaon's map carries `|V_us|²`; the pion's map has
  no `|V_ud|²` and its margin is `32/33`. Same channel type, so the slots should match
  (`KaonPionRatio`: with `|V_ud|²` in the pion's map the ratio's residual is the `f_K` tension).
* **The neutron's correction needs a Governor above one.** `neutronLifetimeCorrected` equals the
  lifetime of the channel with `governor = 43/41` (`neutronLifetimeCorrected_eq_channel`,
  `neutronCorrected_governor_gt_one`). A Governor restricts transitions
  (`PersistencePremises.restriction_lowers`), so its factor is at most one; with `41/43` the
  lifetime is `neutronLifetimeExactCutoff / (41/43)` (`neutronChannel_lifetime`), `≈ 964.8 s`.

**Where the neutron's `+9.8%` comes from** (floating-point comparison, outside Lean). With the
Governor at `41/43`, the E8 rate is low by `964.8/878.4 = 1.0984`. Against the SM's
`|V_ud|²(1+3g_A²) f (1+RC)/2π³`, factor by factor:

| SM piece the E8 neutron channel does not carry | factor |
|---|---:|
| Coulomb attraction of the outgoing electron (full `f` over the E8 endpoint's `f₀`) | 1.0322 |
| radiative correction `(1+δ_R')(1+Δ_R^V)` | 1.0399 |
| `g_A`: `1.2754` against E8 `σ/D = 5/4` | 1.0338 |
| spectral `1/(3P)` against continuum `(1+3g_A²)f₀/2π³` at `g_A = 5/4` | 0.9941 |
| `|V_ud|²` against the Governor `41/43` | 0.9944 |
| **product** | **1.0970** |

The product leaves `0.13%`. So the Governor slot sits where the SM has `|V_ud|²` (`41/43` vs
`0.948`, `0.56%`), the spectral factor matches the continuum axial-times-phase-space at `g_A = 5/4`
(`0.6%`), and the gap is three pieces: the Coulomb factor (`α` and the endpoint, E8 inputs), the
radiative correction (no E8 counterpart), and `g_A` (E8 `5/4` is `2.0%` low). The present
`lifetime × 41/43` multiplies the rate by `(43/41)² = 1.0999` relative to the Governor reading,
which is why it lands near `878 s`.
-/

noncomputable section
namespace PMHadrons.DecayInstantiation
open PersistenceMechanics.Decay

/-- `π⁺ → μ⁺ν` as filled today: no `|V_ud|²` in map, `32/33` in margin. -/
def pionChannel : DecayChannel :=
  { capacity := MesonMasses.pionPlus * PMElementaryParticles.LeptonMasses.muon ^ 2 *
      (1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 /
        (8 * Real.pi)
    map := PionWidth.pionDecayConstantE8 ^ 2
    protocol := 1
    governor := 1
    toll := PMElementaryParticles.SharedUnits.fermiME ^ 2
    margin := PMSubstrate.E8Margin.pionMargin
    action := 0 }

theorem pionChannel_rate :
    rate 1 pionChannel = PionWidth.pionWidthE8 * PMSubstrate.E8Margin.pionMargin := by
  unfold rate pionChannel PionWidth.pionWidthE8 PionWidth.pionWidth
  dsimp only
  simp only [neg_zero, Real.exp_zero]
  ring

/-- `K⁺ → μ⁺ν`: `|V_us|²` in map, no margin. -/
def kaonChannel : DecayChannel :=
  { capacity := CompositeMasses.kaonPlus * PMElementaryParticles.LeptonMasses.muon ^ 2 *
      (1 - (PMElementaryParticles.LeptonMasses.muon / CompositeMasses.kaonPlus) ^ 2) ^ 2 /
        (8 * Real.pi)
    map := KaonWidth.kaonDecayConstantE8 ^ 2 * KaonWidth.vusE8 ^ 2
    protocol := 1
    governor := 1
    toll := PMElementaryParticles.SharedUnits.fermiME ^ 2
    margin := 1
    action := 0 }

theorem kaonChannel_rate : rate 1 kaonChannel = KaonWidth.kaonWidthE8 := by
  unfold rate kaonChannel KaonWidth.kaonWidthE8 KaonWidth.kaonWidthCKM KaonWidth.kaonWidth
  dsimp only
  simp only [neg_zero, Real.exp_zero]
  ring

/-- `n → p e ν̄` with the surviving-phase fraction in the Governor slot. -/
def neutronChannel (governor : ℝ) : DecayChannel :=
  { capacity := 1
    map := 1
    protocol := neutronSpectralFractionExact
    governor := governor
    toll := betaHazardE8
    margin := 1
    action := 0 }

/-- **With the Governor at `41/43`, the lifetime is the uncorrected one divided by `41/43`.** -/
theorem neutronChannel_lifetime :
    lifetime 1 (neutronChannel PMSubstrate.E8Margin.phaseMargin) =
      neutronLifetimeExactCutoff / PMSubstrate.E8Margin.phaseMargin := by
  unfold lifetime rate neutronChannel neutronLifetimeExactCutoff betaLifetimeFromFraction
  dsimp only
  simp only [neg_zero, Real.exp_zero]
  ring

/-- **The present correction is the channel with Governor `43/41`.** -/
theorem neutronLifetimeCorrected_eq_channel :
    neutronLifetimeCorrected =
      lifetime 1 (neutronChannel (1 / PMSubstrate.E8Margin.phaseMargin)) := by
  rw [neutronLifetimeCorrected_eq]
  unfold neutronMarginFactor lifetime rate neutronChannel neutronLifetimeExactCutoff
    betaLifetimeFromFraction
  dsimp only
  simp only [neg_zero, Real.exp_zero, one_div, mul_inv, inv_inv, mul_one, one_mul]
  ring

/-- That Governor is above one, which a restriction cannot be. -/
theorem neutronCorrected_governor_gt_one : 1 < 1 / PMSubstrate.E8Margin.phaseMargin := by
  rw [PMSubstrate.E8Margin.phaseMargin_eq]
  norm_num

/-! ## One template for the three semileptonic decays

π → μν (`d → u`), K → μν (`s → u`) and n → p e ν̄ (`d → u`) are the same weak contact. Filled the
same way (PMFlavor: the CKM magnitude is the identity overlap, so it goes in **map**; PM: a
Governor only restricts, and PMAtoms' `betaDecayChannel` has no Governor), each channel is

  `toll = G_F²` (`G_F²/3` for the beta hazard) · capacity · map `= |V|²·(overlap)` · margin `R`,

with **one** `R` for all three. The pion fixes it: `32/33 = |V_ud|²·R`, so
`sharedFactor = (32/33)/|V_ud|² ≈ 1.0211` (`pionChannelCKM_rate`: the pion is unchanged).
`R` has no E8 derivation yet; it is the factor the SM writes as the short-distance running of
the contact from the W scale (`PMAction.WeakVertex.exchange_at_zero`) to the hadron scale.

Consequences (no new number is introduced):

* **Kaon** (`kaonChannelCKM_rate`): its rate is the present one times `R`, `τ ≈ 1.973×10⁻⁸ s`
  against the `K_μ2` partial `1.948×10⁻⁸ s` (+1.28%); the residual is the `f_K` tension
  (`KaonPionRatio`).
* **Neutron** (`neutronChannelCKM_lifetime`): `|V_ud|²·R = 32/33` replaces the reversed `41/43`;
  `τ_n = τ_exact·33/32`, proved `948.69–948.70 s` (`neutronLifetimeUnifiedSeconds_bounds`),
  +8.0% against `878.4 s`. The 8.0% is, to 0.01%, the three things the neutron channel has and
  the meson channels do not (floating-point comparison): the outgoing charged electron's Coulomb
  attraction (1.032), the nucleon's axial coupling (`g_A`: 1.034 for `1.2754` against E8 `5/4`),
  and the low-energy part of the radiative correction (1.018), times spectral-vs-continuum
  (0.994). E8 counterparts to build: the `3×3×3` cube's own Green function
  (`PMAtoms.LatticeCharge3`) for the first, the composite's axial overlap (same family as the
  emission space behind `f_K`) for the second.
-/

/-- The shared margin `R = (32/33)/|V_ud|²` (not derived; fixed by the pion). -/
def sharedFactor : ℝ := PMSubstrate.E8Margin.pionMargin / PMFlavor.Values.vud ^ 2

lemma vud_ne_zero : PMFlavor.Values.vud ≠ 0 := by
  have h := PMFlavor.Values.vud_bounds
  intro h0; rw [h0] at h; norm_num at h

/-- `|V_ud|²·R = 32/33`. -/
lemma vud_sq_mul_shared :
    PMFlavor.Values.vud ^ 2 * sharedFactor = PMSubstrate.E8Margin.pionMargin := by
  have hv : PMFlavor.Values.vud ^ 2 ≠ 0 := pow_ne_zero 2 vud_ne_zero
  unfold sharedFactor
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hv]

/-- π → μν with `|V_ud|²` in map and the shared margin. -/
def pionChannelCKM : DecayChannel :=
  { pionChannel with
    map := PionWidth.pionDecayConstantE8 ^ 2 * PMFlavor.Values.vud ^ 2
    margin := sharedFactor }

/-- **The pion is unchanged**: `|V_ud|²·R = 32/33`. -/
theorem pionChannelCKM_rate :
    rate 1 pionChannelCKM = PionWidth.pionWidthE8 * PMSubstrate.E8Margin.pionMargin := by
  have key := vud_sq_mul_shared
  unfold rate pionChannelCKM pionChannel PionWidth.pionWidthE8 PionWidth.pionWidth
  dsimp only
  simp only [neg_zero, Real.exp_zero]
  linear_combination
    (PMElementaryParticles.SharedUnits.fermiME ^ 2 * PionWidth.pionDecayConstantE8 ^ 2 *
      (MesonMasses.pionPlus * PMElementaryParticles.LeptonMasses.muon ^ 2 *
        (1 - (PMElementaryParticles.LeptonMasses.muon / MesonMasses.pionPlus) ^ 2) ^ 2 /
          (8 * Real.pi))) * key

/-- K → μν with `|V_us|²` in map and the same margin. -/
def kaonChannelCKM : DecayChannel :=
  { kaonChannel with margin := sharedFactor }

/-- **The kaon gets the pion's `R`.** -/
theorem kaonChannelCKM_rate : rate 1 kaonChannelCKM = KaonWidth.kaonWidthE8 * sharedFactor := by
  unfold rate kaonChannelCKM kaonChannel KaonWidth.kaonWidthE8 KaonWidth.kaonWidthCKM
    KaonWidth.kaonWidth
  dsimp only
  simp only [neg_zero, Real.exp_zero]
  ring

/-- n → p e ν̄ with `|V_ud|²` in map, the same margin, no Governor. -/
def neutronChannelCKM : DecayChannel :=
  { capacity := 1
    map := PMFlavor.Values.vud ^ 2
    protocol := neutronSpectralFractionExact
    governor := 1
    toll := betaHazardE8
    margin := sharedFactor
    action := 0 }

/-- **The neutron's correction becomes the pion's `32/33`.** -/
theorem neutronChannelCKM_rate :
    rate 1 neutronChannelCKM =
      betaHazardE8 * neutronSpectralFractionExact * PMSubstrate.E8Margin.pionMargin := by
  have key := vud_sq_mul_shared
  unfold rate neutronChannelCKM
  dsimp only
  simp only [neg_zero, Real.exp_zero]
  linear_combination (betaHazardE8 * neutronSpectralFractionExact) * key

theorem neutronChannelCKM_lifetime :
    lifetime 1 neutronChannelCKM =
      neutronLifetimeExactCutoff / PMSubstrate.E8Margin.pionMargin := by
  unfold lifetime
  rw [neutronChannelCKM_rate]
  unfold neutronLifetimeExactCutoff betaLifetimeFromFraction
  ring

/-- Unified neutron lifetime in seconds. -/
def neutronLifetimeUnifiedSeconds : ℝ :=
  neutronLifetimeExactCutoff / PMSubstrate.E8Margin.pionMargin *
    PMElementaryParticles.PhysicalUnits.electronTime

/-- **With the pion's factor, the E8 neutron lifetime is between `948.69` and `948.70` s.** -/
theorem neutronLifetimeUnifiedSeconds_bounds :
    (948.69 : ℝ) < neutronLifetimeUnifiedSeconds ∧ neutronLifetimeUnifiedSeconds < 948.70 := by
  obtain ⟨hP1, hP2⟩ := neutron_poly_bounds
  obtain ⟨hh1, hh2⟩ := betaHazardE8_tight
  have he := PMElementaryParticles.Values.electronTime_tight
  set P := ∑ s : Fin 7, (neutronWeightCount s.val : ℝ) * Real.exp (-Real.sqrt 2) ^ s.val with hPdef
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP1
  have hhpos : 0 < betaHazardE8 := lt_trans (by norm_num) hh1
  have hτ : neutronLifetimeUnifiedSeconds =
      (33 / 32) * ((P / betaHazardE8) * PMElementaryParticles.PhysicalUnits.electronTime) := by
    unfold neutronLifetimeUnifiedSeconds
    rw [PMSubstrate.E8Margin.pionMargin_eq]
    unfold neutronLifetimeExactCutoff betaLifetimeFromFraction
    rw [neutronSpectralFractionExact_eq, neutronSpectralFraction_eq_inv_poly, ← hPdef]
    have hPne : P ≠ 0 := hPpos.ne'
    have hhne : betaHazardE8 ≠ 0 := hhpos.ne'
    field_simp
  have hXlo : (2.20828699 : ℝ) / 3.0919962e-24 < P / betaHazardE8 := by
    rw [div_lt_div_iff₀ (by norm_num) hhpos]
    nlinarith
  have hXhi : P / betaHazardE8 < (2.20828851 : ℝ) / 3.0919850e-24 := by
    rw [div_lt_div_iff₀ hhpos (by norm_num)]
    nlinarith
  have hXpos : 0 < P / betaHazardE8 := div_pos hPpos hhpos
  rw [hτ]
  constructor
  · have := mul_lt_mul'' hXlo he.1 (by norm_num) (by norm_num)
    nlinarith
  · have := mul_lt_mul'' hXhi he.2 hXpos.le (lt_trans (by norm_num) he.1).le
    nlinarith

end PMHadrons.DecayInstantiation
