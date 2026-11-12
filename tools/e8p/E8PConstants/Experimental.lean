import E8PConstants.Catalog

/-!
# Experimental reference values (frozen comparisons)

Mirrors the spirit of `PM-1-Arch/calculations/experimental_values.py`: each value
carries a measured central value, an uncertainty, and a citation. Stored as exact
`Rat` so the discrepancy/σ display is rational arithmetic, not floating point.
These are *comparison inputs*, not model values and not error bars of the Lean
catalog. `none` means the value has no experimental counterpart here (or is pure
geometric arithmetic).
-/
namespace E8PConstants

structure ExpRef where
  value : Rat
  uncertainty : Rat
  citation : String
  deriving Repr

/-- All experimental references recorded for a key (frozen comparison data). -/
def expRefs : Key → List ExpRef
  | .inverseAlpha => [
      ⟨137.035999177, 0.000000021, "mohr_codata_2025"⟩,
      ⟨137.035999206, 0.000000011, "morel_determination_2020"⟩,
      ⟨137.035999046, 0.000000027, "parker_measurement_2018"⟩,
      ⟨137.035999166, 0.000000015, "fan_measurement_2023"⟩]
  | .alpha => [⟨0.0072973525643, 0.0000000000011, "mohr_codata_2025"⟩]
  | .strong => [⟨0.1179, 0.0009, "navas_review_2024"⟩]
  | .higgsMass => [⟨125.20, 0.11, "navas_review_2024"⟩]
  | .fermi => [⟨0.000011663788, 0.000000000006, "navas_review_2024"⟩]
  | .vev => [⟨246.21965, 0.00006, "navas_review_2024"⟩]
  | .electronYukawa => [⟨0.000002935, 0.000000001, "navas_review_2024"⟩]
  | .jarlskog => [⟨0.0000308, 0.0000015, "navas_review_2024"⟩]
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
  | .vud | .vudDressed => [⟨0.97373, 0.00031, "pdg_2024"⟩]
  | .tauLifetimeFs => [⟨290.3, 0.82, "pdg_2024"⟩]
  | .neutronLifetimePredicted => [⟨878.4, 0.5, "pdg_2024"⟩]
  | .pionLifetimePredicted => [⟨2.6033e-8, 0.0005e-8, "pdg_2024"⟩]
  -- τ_π / (τ_K / BR(K→μν)) = 2.6033 / (1.2380 / 0.6356); errors 0.02%, 0.16%, 0.17% in quadrature
  | .kaonPionRatio => [⟨1.336557, 0.003176, "pdg_2024"⟩]
  | .muonLifetimeSeconds => [⟨2.1969811e-6, 0.0000022e-6, "pdg_2024"⟩]
  | .neutralPionFiniteLifetimeSeconds => [⟨8.43e-17, 0.13e-17, "pdg_2024"⟩]
  | .zEq => [⟨3387, 21, "planck_2018"⟩]
  | .ckmS13 => [⟨0.00382, 0.00020, "pdg_2024"⟩]
  | .ckmS23 => [⟨0.0415, 0.0008, "pdg_2024"⟩]
  | .ckmVcb => [⟨0.0415, 0.0008, "pdg_2024"⟩]
  | .wolfLambda => [⟨0.22431, 0.00085, "navas_review_2024"⟩]
  | .wolfA => [⟨0.826, 0.015, "navas_review_2024"⟩]
  | .wolfRho => [⟨0.1591, 0.0095, "navas_review_2024"⟩]
  | .wolfEta => [⟨0.348, 0.010, "navas_review_2024"⟩]
  | .sin2Theta12 => [⟨0.304, 0.012, "esteban_nufit-60_2024"⟩]
  | .sin2Theta23 => [⟨0.574, 0.016, "esteban_nufit-60_2024"⟩]
  | .sin2Theta13 => [⟨0.02225, 0.00056, "esteban_nufit-60_2024"⟩]
  | .pm3J => [⟨0.0000308, 0.0000015, "navas_review_2024"⟩]
  | .cabibbo => [⟨0.225, 0.00067, "navas_review_2024"⟩]
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
      ⟨80.3692, 0.0133, "pdg_2024_world"⟩,
      ⟨80.4335, 0.0094, "cdf_2022"⟩]
  | .zMassUnc => [⟨91.1876, 0.0021, "pdg_2024"⟩]
  | _ => []

/-- Whether a reference is **scored** in the audit summary. Unscored references are shown for
context, with `·` instead of a glyph:
* intermediate (tree-level / uncorrected) values, whose corrected counterparts are scored:
  `w_mass_uncorrected`, `z_mass_uncorrected` (→ `w_ratio`), `dark_raw` (→ `omega_ratio`);
* `baryon_pmJ`, the Paper IV Jarlskog proposal that `PMFlavor.CKM.papers_disagree` sets against
  Paper III's `baryon_pm3J` (the scored candidate);
* early-universe (CMB) references against late-universe values (`hubble_late`, `clustering_late`):
  that gap is the Hubble / `S₈` tension, not a model miss (DES Y1 + BAO + BBN is calibrated by the
  BBN sound horizon, so it is grouped with the early-universe references);
* `muon_lifetime_s`, the tree-level width: the measurement includes the SM QED factor, and the E8
  `G_F` it tests is already scored in `fermi_constant`. -/
def scoredRef (k : Key) (r : ExpRef) : Bool :=
  match k with
  | .wMassUnc | .zMassUnc | .darkRaw | .baryonPmJ | .muonLifetimeSeconds => false
  | .hubbleLate | .clusteringLate => r.citation != "planck_2018" && r.citation != "abbott_des_y1_2018"
  | _ => true

/-- Primary experimental reference for display compatibility (first recorded). -/
def expRef (k : Key) : Option ExpRef := (expRefs k).head?

end E8PConstants
