import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import E8PConstants.Catalog

/-!
# Experimental reference values (frozen comparisons)

Mirrors the spirit of `PM-1-Arch/calculations/experimental_values.py`: each value
carries a measured central value, an uncertainty, and a citation. Stored as exact
`Rat` so the discrepancy/σ display is rational arithmetic, not floating point.
These are *comparison inputs*, not model values and not error bars of the Lean
catalog. `none` means the value has no experimental counterpart here (or is pure
geometric arithmetic).
Flavour references (checked 2026-11-16 against PDG 2024 "CKM quark-mixing matrix" and NuFIT 6.0,
JHEP 12 (2024) 216): `|V_ud|`, `|V_us|`, `|V_cb|`, `|V_ub|` are the review's averages; `λ`, `A`, `ρ̄`, `η̄`
the global fit; `J` the fit value. Asymmetric errors use the side toward the model value. PMNS: normal
ordering, both NuFIT 6.0 analyses (IC19 without SK-atm; IC24 with SK-atm), since `θ₂₃`'s octant
differs between them.
-/
namespace E8PConstants

namespace TauInputs
abbrev muonTimeFs : ℝ := 2.1969811e9
abbrev electronicBranch : ℝ := 0.1782
/-- Singleton enclosures select the central prediction; reference uncertainty stays in expRefs. -/
theorem muonTime_point_interval : muonTimeFs ≤ muonTimeFs ∧ muonTimeFs ≤ muonTimeFs :=
  ⟨le_rfl, le_rfl⟩
theorem branch_point_interval : electronicBranch ≤ electronicBranch ∧ electronicBranch ≤ electronicBranch :=
  ⟨le_rfl, le_rfl⟩
abbrev muonTimeLoFs : ℝ := 2.1969789e9
abbrev muonTimeHiFs : ℝ := 2.1969833e9
abbrev branchLo : ℝ := 0.1778
abbrev branchHi : ℝ := 0.1786

theorem muonTime_interval : muonTimeLoFs ≤ muonTimeFs ∧ muonTimeFs ≤ muonTimeHiFs := by
  norm_num [muonTimeLoFs, muonTimeHiFs, muonTimeFs]
theorem branch_interval : branchLo ≤ electronicBranch ∧ electronicBranch ≤ branchHi := by
  norm_num [branchLo, branchHi, electronicBranch]
end TauInputs

namespace OscillationInputs
abbrev atmospheric {R : Type u} [OfScientific R] : R := 0.002534
abbrev atmosphericSigma {R : Type u} [OfScientific R] : R := 0.000025
end OscillationInputs

structure ExpRef where
  value : Rat
  uncertainty : Rat
  citation : String
  deriving Repr

/- Frozen PDG 2024 lifetime/branching inputs used only to construct matching references.
The uncertainties below are rounded-up first-order quadrature estimates, assuming independent
inputs; unavailable input correlations are not model uncertainties. No model bound is changed. -/
namespace DecayReferences
 def pionLifetime : Rat := 26.033e-9
 def pionMuonBranch : Rat := 0.9998770
 def kaonLifetime : Rat := 12.380e-9
 def kaonMuonBranch : Rat := 0.6356
 def neutralPionLifetime : Rat := 8.43e-17
 def neutralPionPhotonBranch : Rat := 0.98823
 def pionMuonPartialLifetime : Rat := pionLifetime / pionMuonBranch
 def kaonMuonPartialLifetime : Rat := kaonLifetime / kaonMuonBranch
 def neutralPionPhotonPartialLifetime : Rat := neutralPionLifetime / neutralPionPhotonBranch
 def muonicWidthRatio : Rat := pionMuonPartialLifetime / kaonMuonPartialLifetime
end DecayReferences

namespace GaugeReferences

universe u

-- Reuse the exact decimal in the rational report and in real-valued comparison proofs.
abbrev zMassGeV {R : Type u} [OfScientific R] : R := 91.1876
abbrev zMassLoGeV {R : Type u} [OfScientific R] : R := 91.1855
abbrev zMassHiGeV {R : Type u} [OfScientific R] : R := 91.1897
abbrev wMassGeV {R : Type u} [OfScientific R] : R := 80.3692
abbrev wMassSigmaGeV {R : Type u} [OfScientific R] : R := 0.0133
abbrev higgsMassGeV {R : Type u} [OfScientific R] : R := 125.20
abbrev vevRoundedGeV {R : Type u} [OfScientific R] : R := 246.22
abbrev strongComparison {R : Type u} [OfScientific R] : R := 0.1180
abbrev strongSigma {R : Type u} [OfScientific R] : R := 0.0009
abbrev strongWindowHi {R : Type u} [OfScientific R] : R := 0.1189
abbrev inverseZAlphaLo {R : Type u} [OfScientific R] : R := 127.94
abbrev inverseZAlphaHi {R : Type u} [OfScientific R] : R := 127.96
abbrev topLoGeV {R : Type u} [OfScientific R] : R := 172.28
abbrev topHiGeV {R : Type u} [OfScientific R] : R := 172.86
abbrev screeningLo {R : Type u} [OfScientific R] : R := 0.0589
abbrev screeningHi {R : Type u} [OfScientific R] : R := 0.0591
abbrev scalarLo {R : Type u} [OfScientific R] : R := 0.1286
abbrev scalarHi {R : Type u} [OfScientific R] : R := 0.1300

end GaugeReferences

/-- All experimental references recorded for a key (frozen comparison data). -/
def expRefs : Key → List ExpRef
  | .inverseAlpha => [
      ⟨137.035999177, 0.000000021, "mohr_codata_2025"⟩,
      ⟨137.035999206, 0.000000011, "morel_determination_2020"⟩,
      ⟨137.035999046, 0.000000027, "parker_measurement_2018"⟩,
      ⟨137.035999166, 0.000000015, "fan_measurement_2023"⟩]
  | .alpha => [⟨0.0072973525643, 0.0000000000011, "mohr_codata_2025"⟩]
  | .strong => [⟨0.1179, 0.0009, "navas_review_2024"⟩]
  | .higgsMass => [⟨GaugeReferences.higgsMassGeV, 0.11, "navas_review_2024"⟩]
  | .fermi => [⟨0.000011663788, 0.000000000006, "navas_review_2024"⟩]
  | .vev => [⟨246.21965, 0.00006, "navas_review_2024"⟩]
  | .electronYukawa => [⟨0.000002935, 0.000000001, "navas_review_2024"⟩]
  | .jarlskog => [⟨0.0000312, 0.0000012, "navas_review_2024"⟩]
  | .hubbleLate => [
      ⟨73.0, 1.0, "riess_sh0es_2022"⟩,
      ⟨67.4, 0.5, "planck_2018"⟩,
      ⟨67.4, 1.2, "abbott_des_y1_2018"⟩]
  | .clusteringLate => [
      ⟨0.776, 0.017, "abbott_des_2022"⟩,
      ⟨0.832, 0.013, "planck_2018"⟩,
      ⟨0.759, 0.024, "kids_1000_2021"⟩]
  | .protonRatio => [⟨1836.152673426, 0.000000032, "mohr_codata_2025"⟩]
  | .neutronRatio => [⟨1838.68366200, 0.00000074, "mohr_codata_2025"⟩]
  | .muonRatio => [⟨206.7682827, 0.0000046, "mohr_codata_2025"⟩]
  | .omegaRatio => [⟨5.36, 0.05, "planck2018"⟩]
  | .darkRaw => [⟨5.36, 0.05, "planck2018"⟩]
  | .vonKlitzing => [⟨25812.80745, 0.00001, "mohr_codata_2025"⟩]
  | .planckMass => [⟨1.22091e19, 1.0e14, "mohr_codata_2025"⟩]
  -- `R∞hc` and `a₀` use `m_e` as an input, and CODATA derives `m_e` from `R∞` and `α`, so these two
  -- rows are `α` comparisons. Their σ uses the `m_e` input uncertainty (`3.1×10⁻¹⁰` relative),
  -- combined with the reference's own; CODATA 2022 `R∞hc = 13.605693122990(15)` eV.
  | .rydbergEV => [⟨13.605693122990, 0.0000000043, "codata_2022"⟩]
  -- CODATA 2022 `a₀ = 0.529177210544(82)` Å; σ combines it with the `m_e` input (`1.6×10⁻¹⁰` Å).
  | .bohrRadius => [⟨0.529177210544, 0.00000000018, "codata_2022"⟩]
  -- Light neutrino species from the Z invisible width, LEP with the corrected Bhabha luminosity
  -- (Janot and Jadach, PLB 803 (2020) 135319; PDG 2024 average). Light means m < m_Z/2.
  | .generations => [⟨2.9963, 0.0074, "janot_jadach_2020"⟩]
  | .vud | .vudDressed => [⟨0.97367, 0.00032, "pdg_2024"⟩]
  | .tauLifetimeFs => [⟨290.3, 0.82, "pdg_2024"⟩]
  | .neutronLifetimePredicted => [⟨878.4, 0.5, "pdg_2024"⟩]
  | .pionLifetimePredicted => [⟨DecayReferences.pionMuonPartialLifetime, 5.001e-12, "pdg_2024_pi_mu2_inclusive_partial"⟩]
  | .kaonPionRatio => [⟨DecayReferences.muonicWidthRatio, 0.003176, "pdg_2024_inclusive_muonic_partial_ratio"⟩]
  | .kaonMuLifetimeSeconds | .kaonFiniteLifetimeSeconds => [⟨DecayReferences.kaonMuonPartialLifetime, 4.612e-11, "pdg_2024_k_mu2_inclusive_partial"⟩]
  | .neutronLifetimeUnified => [⟨878.4, 0.5, "pdg_2024"⟩]
  | .muonLifetimeSeconds => [⟨2.1969811e-6, 0.0000022e-6, "pdg_2024"⟩]
  | .neutralPionFiniteLifetimeSeconds => [⟨DecayReferences.neutralPionPhotonPartialLifetime, 1.316e-18, "pdg_2024_pi0_gamma_gamma_partial"⟩]
  | .zEq => [⟨3387, 21, "planck_2018"⟩]
  | .ckmS13 => [⟨0.00382, 0.00020, "pdg_2024"⟩]
  | .ckmS23 => [⟨0.0411, 0.0012, "pdg_2024"⟩]
  | .ckmVcb => [⟨0.0411, 0.0012, "pdg_2024"⟩]
  | .wolfLambda => [⟨0.22431, 0.00085, "navas_review_2024"⟩]
  | .wolfA => [⟨0.826, 0.015, "navas_review_2024"⟩]
  | .wolfRho => [⟨0.1591, 0.0095, "navas_review_2024"⟩]
  | .wolfEta => [⟨0.3523, 0.0071, "navas_review_2024"⟩]
  | .sin2Theta12 => [
      ⟨0.307, 0.012, "esteban_nufit-60_2024_no_ic19"⟩,
      ⟨0.308, 0.012, "esteban_nufit-60_2024_no_ic24_sk"⟩]
  | .sin2Theta23 => [
      ⟨0.561, 0.012, "esteban_nufit-60_2024_no_ic19"⟩,
      ⟨0.470, 0.017, "esteban_nufit-60_2024_no_ic24_sk"⟩]
  | .sin2Theta13 => [
      ⟨0.02195, 0.00058, "esteban_nufit-60_2024_no_ic19"⟩,
      ⟨0.02215, 0.00058, "esteban_nufit-60_2024_no_ic24_sk"⟩]
  | .pm3J => [⟨0.0000312, 0.0000012, "navas_review_2024"⟩]
  | .cabibbo => [⟨0.22501, 0.00068, "navas_review_2024"⟩]
  | .pionPlusMeV => [⟨139.57039, 0.00018, "pdg_2024"⟩]
  | .fPiMeV => [⟨130.2, 0.8, "flag_2024"⟩]
  | .fKMeV => [⟨155.7, 0.3, "flag_2024"⟩]
  | .wRatio => [⟨0.881355, 0.000146, "pdg_2024"⟩]
  | .upMeV => [⟨2.16, 0.07, "pdg_2024"⟩]
  | .downMeV => [⟨4.7, 0.07, "pdg_2024"⟩]
  | .strangeMeV => [⟨93.5, 0.8, "pdg_2024"⟩]
  | .charmMeV => [⟨1273.0, 4.6, "pdg_2024"⟩]
  | .bottomMeV => [⟨4183, 7, "pdg_2024"⟩]
  | .topMeV => [⟨172570, 290, "pdg_2024"⟩]
  | .tauRatio => [⟨3477.36, 0.18, "pdg_2024"⟩]
  | .protonRadius => [⟨0.84075, 0.00064, "codata_2022"⟩]
  | .pion0MeV => [⟨134.9768, 0.0005, "pdg_2024"⟩]
  | .kaon0MeV => [⟨497.611, 0.013, "pdg_2024"⟩]
  | .kaonPlusMeV => [⟨493.677, 0.016, "pdg_2024"⟩]
  | .baryonPmJ => [⟨6.12e-10, 4.0e-12, "planck_2018"⟩]
  | .baryonPm3J => [⟨6.12e-10, 4.0e-12, "planck_2018"⟩]
  | .alphaG => [⟨(1752 : Rat) / (10 : Rat)^48, (1 : Rat) / (10 : Rat)^48, "mohr_codata_2025"⟩]
  | .wMassUnc => [
      ⟨GaugeReferences.wMassGeV, GaugeReferences.wMassSigmaGeV, "pdg_2024_world"⟩,
      ⟨80.4335, 0.0094, "cdf_2022"⟩]
  | .zMassUnc => [⟨GaugeReferences.zMassGeV, 0.0021, "pdg_2024"⟩]
  | _ => []

/-- Comparison-error provenance; tau already includes its supplied branching-input error. -/
def comparisonNote (k : Key) : String :=
  match k with
  | .tauLifetimeFs => "combined comparison uncertainty: 0.5 fs measured lifetime and about 0.65 fs propagated B_e input, rounded to 0.82 fs; not a 0.82 fs experimental lifetime error"
  | .pionLifetimePredicted => "partial reference = 26.033 ns / 0.9998770; uncertainty from 0.005 ns and BR error 0.0000004 in quadrature, rounded up; input correlations unavailable"
  | .kaonMuLifetimeSeconds => "partial reference = 12.380 ns / 0.6356; uncertainty from 0.020 ns and BR error 0.0011 in quadrature, rounded up; shares comparison inputs with the scored kaon/pion width ratio"
  | .kaonFiniteLifetimeSeconds => "partial reference = 12.380 ns / 0.6356; uncertainty from 0.020 ns and BR error 0.0011 in quadrature, rounded up; raw model is context only"
  | .kaonPionRatio => "ratio uses both muonic branching fractions; uncertainty propagated from frozen lifetimes/branches in quadrature, rounded up; input correlations unavailable"
  | .neutralPionFiniteLifetimeSeconds => "partial reference = 8.43e-17 s / 0.98823; uncertainty from 0.13e-17 s and BR error 0.00034 in quadrature, rounded up; input correlations unavailable"
  | _ => ""

/-- Whether a reference is **scored** in the audit summary. Unscored references are shown for
context, with `·` instead of a glyph:
* `electron_yukawa`: a closure value repeating the VEV comparison, not a direct measurement;
* `electron_closure`: a scheme-dependent tree-relation diagnostic, not a scored test;
* intermediate (tree-level / uncorrected) values, whose corrected counterparts are scored:
  `w_mass_uncorrected`, `z_mass_uncorrected` (→ `w_ratio`), `dark_raw` (→ `omega_ratio`);
* `baryon_pmJ`, the Paper IV Jarlskog proposal that `PMFlavor.CKM.papers_disagree` sets against
  Paper III's `baryon_pm3J` (the scored candidate);
* early-universe (CMB) references against late-universe values (`hubble_late`, `clustering_late`):
  that gap is the Hubble / `S₈` tension, not a model miss (DES Y1 + BAO + BBN is calibrated by the
  BBN sound horizon, so it is grouped with the early-universe references);
* `neutron_lifetime_unified_s`: the `3³` spectral template, kept as a comparison; the scored E8
  neutron is `neutron_lifetime_predicted_s` (continuum route);
* `kaon_finite_lifetime_s`: raw muonic partial channel;
* `kaon_muonic_partial_lifetime_s`: normalized partial channel, sharing
  comparison inputs with the scored kaon/pion width ratio;
* `muon_lifetime_s`: E8 `G_F` with the derived phase factor and the supplied Fermi-theory QED series
  through two loops; the `G_F` it tests is already scored in `fermi_constant`. -/
def scoredRef (k : Key) (r : ExpRef) : Bool :=
  match k with
  | .electronYukawa | .electronClosure
  | .wMassUnc | .zMassUnc | .darkRaw | .baryonPmJ | .muonLifetimeSeconds
  | .neutronLifetimeUnified | .kaonMuLifetimeSeconds | .kaonFiniteLifetimeSeconds => false
  | .hubbleLate | .clusteringLate => r.citation != "planck_2018" && r.citation != "abbott_des_y1_2018"
  | _ => true

/-- Primary experimental reference for display compatibility (first recorded). -/
def expRef (k : Key) : Option ExpRef := (expRefs k).head?

end E8PConstants
