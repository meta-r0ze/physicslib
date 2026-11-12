import Init.Data.Rat.Basic

/-! Computable data shared by the reporter and `E8PConstantsProof`. No Real
evaluation or floating-point arithmetic occurs in this module. Every key has
a certificate against the current named model definition in that proof module. -/
namespace E8PConstants

inductive Key where
  | inverseAlpha | alpha | overhead | footprint | weakFraction | scalar | scalarToll
  | electronYukawa | strong | vevRatio | electronMassInput | vev | higgsMass | fermi
  | jarlskog | load | hubbleLate | clusteringLate
  | protonRatio | neutronRatio | muonRatio | hubbleSigma | s8Sigma | omegaRatio
  | wolfLambda | wolfA | wolfRho | wolfEta | sin2Theta12 | sin2Theta23 | sin2Theta13 | pmnsJ
  | delta | nu | sigma | chi | dimD | cap | mapT | protocol | governor | toll | margin
  | lIntrinsic | lEmbed | lSubstrate | nSites | rm | pm3J | cabibbo | nc | weinbergGut | alphaG | boundaryStorage | beta0
  | pmnsE11 | pmnsE12 | pmnsE13 | pmnsE21 | pmnsE22 | pmnsE23 | pmnsE31 | pmnsE32 | pmnsE33
  | tauRatio | protonRadius | pion0MeV | kaon0MeV | kaonPlusMeV | baryonPmJ | baryonPm3J
  | upMeV | downMeV | strangeMeV | charmMeV | bottomMeV | topMeV
  | pionPlusMeV | fPiMeV | fKMeV | wRatio
  | gaugeHyper | gaugeColour | zEq | darkRaw
  | cLight | vonKlitzing | planckChargeAtt | planckChargeRatio | planckMass | ckmS13 | ckmS23 | ckmVcb
  | wMassUnc | zMassUnc | gWeak | gPrime | electronClosure
  | vud | vudDressed | bRes | neutrinoFloor | tauLifetimeFs
  | muonLifetimeFinite | tauLifetimeE8Natural | neutronSpectralFraction
  | neutronLifetimeE8 | muonLifetimeSeconds | neutronLifetimeSeconds | neutronLifetimePredicted
  | pionLifetimePredicted | kaonPionRatio | neutronLifetimeUnified
  | pionFiniteWidth | pionFiniteLifetime
  | kaonFiniteWidth | kaonFiniteLifetime
  | neutralPionFiniteWidth | neutralPionFiniteLifetime
  | pionFiniteLifetimeSeconds | kaonFiniteLifetimeSeconds
  | neutralPionFiniteLifetimeSeconds
  | rydbergEV | bohrRadius | shell4
  deriving BEq, DecidableEq, Repr

def keys : List Key := [.inverseAlpha, .alpha, .overhead, .footprint, .weakFraction,
  .scalar, .scalarToll, .electronYukawa, .strong, .vevRatio, .electronMassInput,
  .vev, .higgsMass, .fermi, .jarlskog, .load, .hubbleLate, .clusteringLate,
  .protonRatio, .neutronRatio, .muonRatio, .hubbleSigma, .s8Sigma, .omegaRatio,
  .wolfLambda, .wolfA, .wolfRho, .wolfEta, .sin2Theta12, .sin2Theta23, .sin2Theta13, .pmnsJ,
  .delta, .nu, .sigma, .chi, .dimD, .cap, .mapT, .protocol, .governor, .toll, .margin,
  .lIntrinsic, .lEmbed, .lSubstrate, .nSites, .rm, .pm3J, .cabibbo, .nc, .weinbergGut, .alphaG, .boundaryStorage, .beta0,
  .pmnsE11, .pmnsE12, .pmnsE13, .pmnsE21, .pmnsE22, .pmnsE23, .pmnsE31, .pmnsE32, .pmnsE33,
  .tauRatio, .protonRadius, .pion0MeV, .kaon0MeV, .kaonPlusMeV, .baryonPmJ, .baryonPm3J,
  .upMeV, .downMeV, .strangeMeV, .charmMeV, .bottomMeV, .topMeV,
  .pionPlusMeV, .fPiMeV, .fKMeV, .wRatio,
  .gaugeHyper, .gaugeColour, .zEq, .darkRaw,
  .cLight, .vonKlitzing, .planckChargeAtt, .planckChargeRatio, .planckMass, .ckmS13, .ckmS23, .ckmVcb,
  .wMassUnc, .zMassUnc, .gWeak, .gPrime, .electronClosure,
  .vud, .vudDressed, .bRes, .neutrinoFloor, .tauLifetimeFs, .muonLifetimeFinite,
  .tauLifetimeE8Natural, .neutronSpectralFraction, .neutronLifetimeE8,
  .muonLifetimeSeconds, .neutronLifetimeSeconds, .neutronLifetimePredicted,
  .pionLifetimePredicted, .kaonPionRatio, .neutronLifetimeUnified,
  .pionFiniteWidth, .pionFiniteLifetime,
  .kaonFiniteWidth, .kaonFiniteLifetime,
  .neutralPionFiniteWidth, .neutralPionFiniteLifetime,
  .pionFiniteLifetimeSeconds, .kaonFiniteLifetimeSeconds,
  .neutralPionFiniteLifetimeSeconds,
  .rydbergEV, .bohrRadius, .shell4]

def Key.id : Key → String
  | .inverseAlpha => "alpha_inv" | .alpha => "alpha" | .overhead => "eta"
  | .footprint => "footprint" | .weakFraction => "weak_fraction" | .scalar => "lambda"
  | .scalarToll => "scalar_toll" | .electronYukawa => "electron_yukawa"
  | .strong => "alpha_s" | .vevRatio => "vev_over_me" | .electronMassInput => "electron_mass_input"
  | .vev => "vev" | .higgsMass => "higgs_mass" | .fermi => "fermi_constant"
  | .jarlskog => "jarlskog" | .load => "load"
  | .hubbleLate => "hubble_late" | .clusteringLate => "clustering_late"
  | .protonRatio => "proton_ratio" | .neutronRatio => "neutron_ratio"
  | .muonRatio => "muon_ratio"
  | .hubbleSigma => "hubble_sigma" | .s8Sigma => "s8_sigma" | .omegaRatio => "omega_ratio"
  | .wolfLambda => "wolf_lambda" | .wolfA => "wolf_A" | .wolfRho => "wolf_rho" | .wolfEta => "wolf_eta"
  | .sin2Theta12 => "sin2_theta12" | .sin2Theta23 => "sin2_theta23" | .sin2Theta13 => "sin2_theta13"
  | .pmnsJ => "pmns_jarlskog"
  | .delta => "delta" | .nu => "nu" | .sigma => "sigma" | .chi => "chi" | .dimD => "D"
  | .cap => "cap" | .mapT => "map" | .protocol => "protocol" | .governor => "governor"
  | .toll => "toll" | .margin => "margin"
  | .lIntrinsic => "l_intrinsic" | .lEmbed => "l_embed" | .lSubstrate => "l_substrate"
  | .nSites => "n" | .rm => "rm"
  | .pm3J => "jarlskog_geo" | .cabibbo => "cabibbo" | .nc => "nc"
  | .weinbergGut => "weinberg_gut" | .alphaG => "alpha_G" | .boundaryStorage => "boundary_storage"
  | .beta0 => "beta_0"
  | .pmnsE11 => "pmns_e11"
  | .pmnsE12 => "pmns_e12"
  | .pmnsE13 => "pmns_e13"
  | .pmnsE21 => "pmns_e21"
  | .pmnsE22 => "pmns_e22"
  | .pmnsE23 => "pmns_e23"
  | .pmnsE31 => "pmns_e31"
  | .pmnsE32 => "pmns_e32"
  | .pmnsE33 => "pmns_e33"
  | .tauRatio => "tau_ratio"
  | .protonRadius => "proton_radius"
  | .pion0MeV => "pion0_mev"
  | .kaon0MeV => "kaon0_mev"
  | .kaonPlusMeV => "kaon_plus_mev"
  | .baryonPmJ => "baryon_pmJ"
  | .baryonPm3J => "baryon_pm3J"
  | .upMeV => "up_mev"
  | .downMeV => "down_mev"
  | .strangeMeV => "strange_mev"
  | .charmMeV => "charm_mev"
  | .bottomMeV => "bottom_mev"
  | .topMeV => "top_mev"
  | .pionPlusMeV => "pion_plus_mev"
  | .fPiMeV => "f_pi_mev"
  | .fKMeV => "f_k_mev"
  | .wRatio => "w_ratio"
  | .gaugeHyper => "gauge_hyper"
  | .gaugeColour => "gauge_colour"
  | .zEq => "z_eq"
  | .darkRaw => "dark_raw"
  | .cLight => "c_light"
  | .vonKlitzing => "von_klitzing"
  | .planckChargeAtt => "planck_charge_attenuation"
  | .planckChargeRatio => "planck_charge_ratio"
  | .planckMass => "planck_mass"
  | .ckmS13 => "ckm_s13"
  | .ckmS23 => "ckm_s23"
  | .ckmVcb => "ckm_vcb"
  | .wMassUnc => "w_mass_uncorrected"
  | .zMassUnc => "z_mass_uncorrected"
  | .gWeak => "g_weak"
  | .gPrime => "g_prime"
  | .electronClosure => "electron_closure"
  | .vud => "vud"
  | .vudDressed => "vud_dressed"
  | .bRes => "b_res"
  | .neutrinoFloor => "neutrino_floor_mass"
  | .tauLifetimeFs => "tau_lifetime_fs"
  | .muonLifetimeFinite => "muon_lifetime_finite"
  | .tauLifetimeE8Natural => "tau_lifetime_e8_natural"
  | .neutronSpectralFraction => "neutron_spectral_fraction"
  | .neutronLifetimeE8 => "neutron_lifetime_e8"
  | .muonLifetimeSeconds => "muon_lifetime_s"
  | .neutronLifetimeSeconds => "neutron_lifetime_s"
  | .neutronLifetimePredicted => "neutron_lifetime_predicted_s"
  | .pionLifetimePredicted => "pion_lifetime_predicted_s"
  | .kaonPionRatio => "kaon_pion_width_ratio"
  | .neutronLifetimeUnified => "neutron_lifetime_unified_s"
  | .pionFiniteWidth => "pion_finite_width"
  | .pionFiniteLifetime => "pion_finite_lifetime"
  | .kaonFiniteWidth => "kaon_finite_width"
  | .kaonFiniteLifetime => "kaon_finite_lifetime"
  | .neutralPionFiniteWidth => "neutral_pion_finite_width"
  | .neutralPionFiniteLifetime => "neutral_pion_finite_lifetime"
  | .pionFiniteLifetimeSeconds => "pion_finite_lifetime_s"
  | .kaonFiniteLifetimeSeconds => "kaon_finite_lifetime_s"
  | .neutralPionFiniteLifetimeSeconds => "neutral_pion_finite_lifetime_s"
  | .rydbergEV => "rydberg_ev"
  | .bohrRadius => "bohr_radius"
  | .shell4 => "shell_capacity_n4"

/-- Exact rational bounds, including exact values as equal endpoints. These
are closed enclosures; the underlying theorems often prove strict inequalities. -/
def bounds : Key → Rat × Rat
  | .inverseAlpha => (137.035999212381397211, 137.035999212381397213)
  | .alpha => (0.007297352562, 0.007297352563)
  | .overhead => (171/172, 171/172)
  | .footprint => (8295/43, 8295/43)
  | .weakFraction => (1849/8295, 1849/8295)
  | .scalar => (128/989, 128/989)
  | .scalarToll => (256/989, 256/989)
  | .electronYukawa => (0.00000293502845, 0.00000293502847)
  | .strong => (0.11799520370, 0.11799520373)
  | .vevRatio => (481839.81165, 481839.81166)
  | .electronMassInput => (0.00051099895, 0.00051099895)
  | .vev => (246.2196378, 246.2196379)
  | .higgsMass => (125.2692637, 125.2692639)
  | .fermi => (0.00001166378, 0.00001166380)
  | .jarlskog => (0.0000302, 0.0000303)
  | .load => (1491/1376, 1491/1376)
  | .hubbleLate => (502467/6880, 502467/6880)
  | .clusteringLate => (143104/186375, 143104/186375)
  | .protonRatio => (1836.152673444, 1836.152673445)
  | .muonRatio => (206.7682716, 206.7682718)
  | .neutronRatio => (1838.6836620, 1838.6836621)
  | .hubbleSigma => (1491/2752, 1491/2752)
  | .s8Sigma => (2236/186375, 2236/186375)
  | .omegaRatio => (5.3775, 5.3776)
  | .wolfLambda => (0.22439, 0.22440)
  | .wolfA => (0.80, 0.85)
  | .wolfRho => (0.137, 0.150)
  | .wolfEta => (0.343, 0.374)
  | .sin2Theta12 => (0.30901, 0.30902)
  | .sin2Theta23 => (0.57479, 0.57481)
  | .sin2Theta13 => (0.0218920, 0.0218921)
  | .pmnsJ => (-0.0217, -0.0215)
  | .delta => (43, 43) | .nu => (16, 16) | .sigma => (5, 5) | .chi => (2, 2) | .dimD => (4, 4)
  | .cap => (135.0884, 135.0885)
  | .mapT => (2, 2) | .protocol => (-1/167, -1/167) | .governor => (-2/43, -2/43)
  | .toll => (334/(32^3*5*172), 334/(32^3*5*172))
  | .margin => (1/(31*6*43^2), 1/(31*6*43^2))
  | .lIntrinsic => (23, 23) | .lEmbed => (31, 31) | .lSubstrate => (188, 188)
  | .nSites => (32, 32) | .rm => (172, 172)
  | .pm3J => (0.000030848, 0.000030850) | .cabibbo => (0.2243994, 0.2243995)
  | .nc => (3, 3) | .weinbergGut => (0.375, 0.375)
  | .alphaG => ((17517995 : Rat) / (10 : Rat)^52, (17517996 : Rat) / (10 : Rat)^52)
  | .boundaryStorage => (2/3, 2/3)
  | .beta0 => (9, 9)
  | .pmnsE11 => (0.6758, 0.6759)
  | .pmnsE12 => (0.3022, 0.3023)
  | .pmnsE13 => (0.0218, 0.0219)
  | .pmnsE21 => (0.0888, 0.089)
  | .pmnsE22 => (0.3488, 0.349)
  | .pmnsE23 => (0.5622, 0.5623)
  | .pmnsE31 => (0.2352, 0.2353)
  | .pmnsE32 => (0.3488, 0.349)
  | .pmnsE33 => (0.4158, 0.416)
  | .tauRatio => (3477, 3477)
  | .protonRadius => (0.8412356, 0.8412357)
  | .pion0MeV => (134.977014, 134.977015)
  | .kaon0MeV => (497.612411, 497.612412)
  | .kaonPlusMeV => (493.676245, 493.676246)
  | .baryonPmJ => (5.94e-10, 5.97e-10)
  | .baryonPm3J => (6.07e-10, 6.08e-10)
  | .upMeV => (2.055, 2.062)
  | .downMeV => (4.623, 4.63)
  | .strangeMeV => (93.5, 93.58)
  | .charmMeV => (1267.02, 1267.48)
  | .bottomMeV => (4180.9, 4182.3)
  | .topMeV => (172657, 172686)
  | .pionPlusMeV => (139.570411, 139.570412)
  | .fPiMeV => (130.27, 130.28)
  | .fKMeV => (154.56, 154.57)
  | .wRatio => (0.8815297, 0.8815298)
  | .gaugeHyper => (6446/43, 6446/43)
  | .gaugeColour => (513/43, 513/43)
  | .zEq => (3377.2121, 3377.2122)
  | .darkRaw => (31/6, 31/6)
  | .cLight => (149896229/5000000, 149896229/5000000)
  | .vonKlitzing => (25812.8074694137, 25812.8074694138)
  | .planckChargeAtt => (11.70623761984957, 11.70623761984958)
  | .planckChargeRatio => (0.0854245430918, 0.0854245430919)
  | .planckMass => (1.22089354e+19, 1.22089358e+19)
  | .ckmS13 => (0.0036073, 0.0036074)
  | .ckmS23 => (0.041308, 0.0413084)
  | .ckmVcb => (0.041308, 0.0413081)
  | .wMassUnc => (78.96, 78.97)
  | .zMassUnc => (89.57, 89.58)
  | .gWeak => (0.6413, 0.6415)
  | .gPrime => (0.3435, 0.3436)
  | .electronClosure => (0.99972687, 0.99972689)
  | .vud => (0.97449, 0.974499)
  | .vudDressed => (0.97377, 0.97380)
  | .bRes => (15.3260359807, 15.3260359808)
  | .neutrinoFloor => (0.009208, 0.00921)
  | .tauLifetimeFs => (291.15, 291.17)
  | .muonLifetimeFinite => (1.25e15, 2.5e15)
  | .tauLifetimeE8Natural => (1.6e8, 3.4e8)
  | .neutronSpectralFraction => (0.45, 1)
  | .neutronLifetimeE8 => (2.9e23, 8.0e23)
  | .muonLifetimeSeconds => (2.187343e-6, 2.187352e-6)
  | .neutronLifetimeSeconds => (3.7e2, 1.04e3)
  | .neutronLifetimePredicted => (923.37, 923.39)
  | .pionLifetimePredicted => (2.60188e-8, 2.60192e-8)
  | .kaonPionRatio => (1.318922, 1.318923)
  | .neutronLifetimeUnified => (948.69, 948.70)
  | .pionFiniteWidth => (4.9e-14, 5.16e-14)
  | .pionFiniteLifetime => (1.9e13, 2.05e13)
  | .kaonFiniteWidth => (6.1e-14, 6.47e-14)
  | .kaonFiniteLifetime => (1.54e13, 1.64e13)
  | .neutralPionFiniteWidth => (1.52e-5, 1.523e-5)
  | .neutralPionFiniteLifetime => (6.56e4, 6.58e4)
  | .pionFiniteLifetimeSeconds => (2.44e-8, 2.65e-8)
  | .kaonFiniteLifetimeSeconds => (1.98e-8, 2.12e-8)
  | .neutralPionFiniteLifetimeSeconds => (8.44e-17, 8.48e-17)
  | .rydbergEV => (13.6056931158, 13.6056931159)
  | .bohrRadius => (0.5291772106829, 0.5291772106830)
  | .shell4 => (32, 32)

def Key.unit : Key → String
  | .electronMassInput | .vev | .higgsMass => "GeV"
  | .pion0MeV | .kaon0MeV | .kaonPlusMeV | .pionPlusMeV | .fPiMeV | .fKMeV | .upMeV | .downMeV | .strangeMeV | .charmMeV | .bottomMeV | .topMeV => "MeV"
  | .protonRadius => "fm"
  | .cLight => "10^7 m/s" | .vonKlitzing => "Ω" | .planckMass => "GeV"
  | .wMassUnc | .zMassUnc => "GeV"
  | .neutrinoFloor => "eV"
  | .tauLifetimeFs => "fs"
  | .muonLifetimeFinite | .tauLifetimeE8Natural | .neutronLifetimeE8 => "m_e^-1"
  | .neutronSpectralFraction => "1"
  | .muonLifetimeSeconds | .neutronLifetimeSeconds | .neutronLifetimePredicted
  | .pionLifetimePredicted | .neutronLifetimeUnified
  | .pionFiniteLifetimeSeconds | .kaonFiniteLifetimeSeconds
  | .neutralPionFiniteLifetimeSeconds => "s"
  | .pionFiniteWidth | .kaonFiniteWidth | .neutralPionFiniteWidth => "m_e"
  | .pionFiniteLifetime | .kaonFiniteLifetime | .neutralPionFiniteLifetime => "m_e^-1"
  | .hubbleLate => "km/s/Mpc"
  | .rydbergEV => "eV" | .bohrRadius => "Å" | .shell4 => "states"
  | .fermi => "GeV^-2"
  | _ => "dimensionless"

def Key.inputs : Key → List String
  | .vev | .higgsMass | .fermi => ["electron_mass_input"]
  | .planckMass => ["electron_mass_input"]
  | .wMassUnc | .zMassUnc => ["electron_mass_input"]
  | .rydbergEV | .bohrRadius => ["electron_mass_input"]
  | .pion0MeV | .kaon0MeV | .kaonPlusMeV | .pionPlusMeV | .fPiMeV | .fKMeV => ["electron_mass_input"]
  | .upMeV | .downMeV | .strangeMeV | .charmMeV | .bottomMeV | .topMeV => ["electron_mass_input"]
  | .protonRadius => ["electron_mass_input"]
  | .tauLifetimeFs => ["measured_muon_lifetime", "B_e"]
  | .vonKlitzing => ["c_light"]
  | .hubbleLate => ["h0_anchor"]
  | .clusteringLate => ["s8_anchor"]
  | .hubbleSigma => ["h0_sigma_anchor"]
  | .s8Sigma => ["s8_sigma_anchor"]
  | _ => []

def Key.role : Key → String
  | .electronMassInput | .cLight => "external_input"
  | _ => "conditional_model_value"

def Key.theoremName : Key → String
  | .inverseAlpha => "PMSubstrate.geometricIndex_bounds"
  | .alpha => "PMConstants.CertifiedConstants.alpha_bounds"
  | .overhead | .footprint | .weakFraction | .scalar | .scalarToll => "PMConstants.exact_partition_values"
  | .electronYukawa => "PMConstants.CurrentConstants.electron_bounds"
  | .strong => "PMConstants.CurrentConstants.strong_bounds"
  | .vevRatio => "PMConstants.JointConstants.vev_ratio_bounds"
  | .electronMassInput => "PMConstants.ElectroweakBounds.electronGeV (supplied benchmark)"
  | .vev => "PMConstants.ElectroweakBounds.vev_bounds"
  | .higgsMass => "PMConstants.ElectroweakBounds.higgs_bounds"
  | .fermi => "PMConstants.ElectroweakBounds.fermi_bounds"
  | .jarlskog => "PMFlavor.Values.jarlskog_bounds"
  | .load => "PMCosmology.Scaling.exact_ratios"
  | .hubbleLate | .clusteringLate => "PMCosmology.SubstrateLoad.revised_numerical_outputs"
  | .protonRatio => "PMHadrons.CompositeMasses.proton_value"
  | .muonRatio => "PMElementaryParticles.LeptonMasses.muon_value"
  | .neutronRatio => "PMHadrons.CompositeMasses.neutron_value"
  | .hubbleSigma => "PMCosmology.Tensions.hubbleInputSigma_exact"
  | .s8Sigma => "PMCosmology.Tensions.s8InputSigma_exact"
  | .omegaRatio => "PMCosmology.Tensions.omegaRatio_bounds"
  | .wolfLambda => "PMFlavor.Wolfenstein.wLam_bounds"
  | .wolfA => "PMFlavor.Wolfenstein.wA_bounds"
  | .wolfRho => "PMFlavor.Wolfenstein.wRho_bounds"
  | .wolfEta => "PMFlavor.Wolfenstein.wEta_bounds"
  | .sin2Theta12 | .sin2Theta23 | .sin2Theta13 => "PMFlavor.PMNSIntervals.input_bounds"
  | .pmnsJ => "PMFlavor.PMNSIntervals.jarlskog_bounds"
  | .delta | .nu | .sigma | .chi | .dimD => "PMSubstrate.Derived.parameters_forced"
  | .cap => "PMSubstrate.capacityTerm" | .mapT => "PMSubstrate.mapTerm"
  | .protocol => "PMSubstrate.protocolTerm" | .governor => "PMSubstrate.governorTerm"
  | .toll => "PMSubstrate.tollTerm" | .margin => "PMSubstrate.marginTerm"
  | .lIntrinsic | .lEmbed | .lSubstrate | .nSites | .rm => "PMSubstrate.Derived.parameters_forced"
  | .pm3J => "PMFlavor.Values.jarlskogGeo_bounds" | .cabibbo => "PMFlavor.Values.s12_bounds"
  | .nc | .weinbergGut | .boundaryStorage => "PMSubstrate.Derived.parameters_forced"
  | .alphaG => "PMConstants.GravityAccounting.channels_as_frame"
  | .beta0 => "PMConstants.beta_positive_iff"
  | .pmnsE11 => "PMFlavor.PMNSIntervals.squared_entry_bounds"
  | .pmnsE12 => "PMFlavor.PMNSIntervals.squared_entry_bounds"
  | .pmnsE13 => "PMFlavor.PMNSIntervals.squared_entry_bounds"
  | .pmnsE21 => "PMFlavor.PMNSIntervals.squared_entry_bounds"
  | .pmnsE22 => "PMFlavor.PMNSIntervals.squared_entry_bounds"
  | .pmnsE23 => "PMFlavor.PMNSIntervals.squared_entry_bounds"
  | .pmnsE31 => "PMFlavor.PMNSIntervals.squared_entry_bounds"
  | .pmnsE32 => "PMFlavor.PMNSIntervals.squared_entry_bounds"
  | .pmnsE33 => "PMFlavor.PMNSIntervals.squared_entry_bounds"
  | .tauRatio => "PMElementaryParticles.LeptonMasses.tau_value"
  | .protonRadius => "PMHadrons.CompositeMasses.protonRadius_value"
  | .pion0MeV => "PMHadrons.CompositeMasses.pion0_mev_value"
  | .kaon0MeV => "PMHadrons.CompositeMasses.kaon0_mev_value"
  | .kaonPlusMeV => "PMHadrons.CompositeMasses.kaonPlus_mev_value"
  | .baryonPmJ => "PMCosmology.Primordial.baryon_windows"
  | .baryonPm3J => "PMCosmology.Primordial.baryon_windows"
  | .upMeV => "PMElementaryParticles.QuarkMasses.up_value"
  | .pionPlusMeV => "PMHadrons.MesonMasses.pionPlus_mev_value"
  | .fPiMeV => "PMHadrons.PionWidth.pionDecayConstantMeV_bounds"
  | .fKMeV => "PMHadrons.KaonWidth.kaonDecayConstantMeV_bounds"
  | .wRatio => "PMConstants.WMassTest.ratio_bounds"
  | .gaugeHyper => "PMConstants.GaugeLedgers.hyper_value"
  | .gaugeColour => "PMConstants.ColourChannels.colour_ledger"
  | .zEq => "PMCosmology.Background.z_eq_bounds"
  | .darkRaw => "PMCosmology.Scaling.exact_ratios"
  | .cLight => "PMSubstrate.speedOfLight_value"
  | .vonKlitzing => "PMSubstrate.vonKlitzing_bounds"
  | .planckChargeAtt => "PMSubstrate.planckChargeAttenuation_bounds"
  | .planckChargeRatio => "PMSubstrate.planckChargeRatio_bounds"
  | .planckMass => "PMConstants.PlanckReadout.planckMass_bounds"
  | .ckmS13 => "PMFlavor.Values.s13_bounds"
  | .ckmS23 => "PMFlavor.Values.s23_bounds"
  | .ckmVcb => "PMFlavor.Values.vcb_bounds"
  | .wMassUnc => "PMConstants.ElectroweakBounds.w_mass_bounds"
  | .zMassUnc => "PMConstants.ElectroweakBounds.z_mass_bounds"
  | .gWeak => "PMConstants.ElectroweakBounds.coupling_bounds"
  | .gPrime => "PMConstants.ElectroweakBounds.coupling_bounds"
  | .electronClosure => "PMConstants.JointConstants.electron_closure_bounds"
  | .vud => "PMFlavor.Values.vud_bounds"
  | .vudDressed => "PMFlavor.Values.vudDressed_bounds"
  | .bRes => "PMConstants.GravityAccounting.residual_tight_bounds"
  | .tauLifetimeFs => "PMElementaryParticles.TauLifetime.tau_lifetime_tree"
  | .muonLifetimeFinite => "PMElementaryParticles.muonFiniteLifetime_bounds"
  | .tauLifetimeE8Natural => "PMElementaryParticles.TauE8.tauLifetimeE8_bounds"
  | .neutronSpectralFraction => "PMHadrons.neutronSpectralFraction_bounds"
  | .neutronLifetimeE8 => "PMHadrons.neutronLifetimeE8_bounds"
  | .muonLifetimeSeconds => "PMElementaryParticles.PhysicalUnits.muonLifetimeSeconds_tight"
  | .neutronLifetimeSeconds => "PMHadrons.neutronLifetimeSeconds_bounds"
  | .neutronLifetimePredicted => "PMHadrons.NeutronContinuum.neutronLifetimeContinuumCoulombSeconds_bounds"
  | .pionLifetimePredicted => "PMHadrons.pionLifetimeCorrectedSeconds_bounds"
  | .kaonPionRatio => "PMHadrons.KaonPionRatio.kaonPionWidthRatio_bounds"
  | .neutronLifetimeUnified => "PMHadrons.DecayInstantiation.neutronLifetimeUnifiedSeconds_bounds"
  | .pionFiniteWidth => "PMHadrons.pionFiniteWidth_bounds"
  | .pionFiniteLifetime => "PMHadrons.pionFiniteLifetime_bounds"
  | .kaonFiniteWidth => "PMHadrons.kaonFiniteWidth_bounds"
  | .kaonFiniteLifetime => "PMHadrons.kaonFiniteLifetime_bounds"
  | .neutralPionFiniteWidth => "PMHadrons.neutralPionFiniteWidth_bounds"
  | .neutralPionFiniteLifetime => "PMHadrons.neutralPionFiniteLifetime_bounds"
  | .pionFiniteLifetimeSeconds => "PMHadrons.pionFiniteLifetimeSeconds_bounds"
  | .kaonFiniteLifetimeSeconds => "PMHadrons.kaonFiniteLifetimeSeconds_bounds"
  | .neutralPionFiniteLifetimeSeconds => "PMHadrons.neutralPionFiniteLifetimeSeconds_bounds"
  | .neutrinoFloor => "PMConstants.FloorNeutrino.floor_bounds"
  | .rydbergEV => "PMAtoms.rydbergEV_bounds"
  | .bohrRadius => "PMAtoms.bohrRadius_bounds"
  | .shell4 => "PMAtoms.shell_capacities"
  | .downMeV => "PMElementaryParticles.QuarkMasses.down_value"
  | .strangeMeV => "PMElementaryParticles.QuarkMasses.strange_value"
  | .charmMeV => "PMElementaryParticles.QuarkMasses.charm_value"
  | .bottomMeV => "PMElementaryParticles.QuarkMasses.bottom_value"
  | .topMeV => "PMElementaryParticles.QuarkMasses.top_value"

/-- The paper that derives the value (for `--paper=N` filtering). -/
def Key.paper : Key → Nat
  | .delta | .nu | .sigma | .chi | .dimD => 0
  | .cap | .mapT | .protocol | .governor | .toll | .margin => 1
  | .lIntrinsic | .lEmbed | .lSubstrate | .nSites | .rm => 0
  | .nc | .weinbergGut | .boundaryStorage => 0
  | .alphaG => 3
  | .beta0 => 3
  | .pmnsE11 => 4
  | .pmnsE12 => 4
  | .pmnsE13 => 4
  | .pmnsE21 => 4
  | .pmnsE22 => 4
  | .pmnsE23 => 4
  | .pmnsE31 => 4
  | .pmnsE32 => 4
  | .pmnsE33 => 4
  | .tauRatio => 5
  | .protonRadius => 5
  | .pion0MeV => 5
  | .kaon0MeV => 5
  | .kaonPlusMeV => 5
  | .baryonPmJ => 6
  | .baryonPm3J => 6
  | .upMeV => 5
  | .pionPlusMeV => 5
  | .fPiMeV | .fKMeV => 5
  | .wRatio => 3
  | .gaugeHyper => 3
  | .gaugeColour => 3
  | .zEq => 6
  | .darkRaw => 6
  | .cLight => 1
  | .vonKlitzing => 1
  | .planckChargeAtt => 1
  | .planckChargeRatio => 1
  | .planckMass => 1
  | .ckmS13 => 4
  | .ckmS23 => 4
  | .ckmVcb => 4
  | .wMassUnc => 3
  | .zMassUnc => 3
  | .gWeak => 3
  | .gPrime => 3
  | .electronClosure => 3
  | .vud | .vudDressed => 4
  | .bRes => 3
  | .neutrinoFloor => 5
  | .tauLifetimeFs | .muonLifetimeFinite | .tauLifetimeE8Natural
  | .neutronSpectralFraction | .neutronLifetimeE8
  | .muonLifetimeSeconds | .neutronLifetimeSeconds | .neutronLifetimePredicted
  | .pionLifetimePredicted | .kaonPionRatio | .neutronLifetimeUnified => 5
  | .pionFiniteWidth | .pionFiniteLifetime
  | .kaonFiniteWidth | .kaonFiniteLifetime
  | .neutralPionFiniteWidth | .neutralPionFiniteLifetime => 5
  | .pionFiniteLifetimeSeconds | .kaonFiniteLifetimeSeconds
  | .neutralPionFiniteLifetimeSeconds => 5
  | .rydbergEV => 5
  | .bohrRadius => 5
  | .shell4 => 5
  | .downMeV => 5
  | .strangeMeV => 5
  | .charmMeV => 5
  | .bottomMeV => 5
  | .topMeV => 5
  | .pm3J | .cabibbo => 4
  | .inverseAlpha | .alpha => 1
  | .jarlskog | .wolfLambda | .wolfA | .wolfRho | .wolfEta | .sin2Theta12 | .sin2Theta23 | .sin2Theta13 | .pmnsJ => 4
  | .protonRatio | .neutronRatio | .muonRatio => 5
  | .load | .hubbleLate | .clusteringLate | .hubbleSigma | .s8Sigma | .omegaRatio => 6
  | _ => 3

/-- Display section names, independent of the paper number. -/
def Key.section (k : Key) : String :=
  match k with
  | .rydbergEV | .bohrRadius | .shell4 => "Atoms"
  | _ => match k.paper with
    | 0 | 1 => "Substrate"
    | 3 => "Constants"
    | 4 => "Flavor"
    | 5 => "Elementary Particles"
    | 6 => "Cosmology"
    | _ => s!"Paper {k.paper}"

/-- A best-effort LaTeX formula for the value, for `--latex`. Empty if not recorded. -/
def Key.formula : Key → String
  | .inverseAlpha => "\\pi\\Delta+\\chi-\\frac{1}{D\\Delta-\\sigma}-\\frac{\\chi}{\\Delta}+T+PM"
  | .alpha => "1/\\alpha^{-1}"
  | .overhead => "\\frac{D\\Delta-1}{D\\Delta}"
  | .weakFraction => "\\frac{\\Delta}{D\\Delta+\\nu+\\sigma}"
  | .strong => "\\frac{\\nu\\cdot\\eta+1/D}{\\alpha^{-1}}"
  | .electronYukawa => "PM_{geo}\\left(1+\\frac{\\sigma}{D}\\alpha\\right)"
  | .vev => "v_{geo}\\left(1+\\frac{\\alpha}{D+\\chi/4\\pi}\\right)"
  | .higgsMass => "\\sqrt{2\\lambda}\\,v"
  | .jarlskog => "\\phi^2\\cdot T_{geo}"
  | .load => "1+\\frac{1}{2\\nu}+\\frac{\\chi}{\\Delta}+\\frac{1}{D\\Delta}"
  | .muonRatio => "\\Delta\\sigma-\\chi-2\\pi+\\frac{\\alpha(\\chi+\\sigma)}{1-\\alpha}"
  | .protonRatio => "\\Delta^2-\\pi D-\\frac{1}{D}+5Z_{TOL}-\\frac{Z_{MAR}}{\\chi}-\\alpha(D+\\frac1D)"
  | .neutronRatio => "\\Delta^2-\\pi D-\\frac1D+\\frac{\\sigma}{2}+3Z_{TOL}-Z_{MAR}"
  | .omegaRatio => "\\frac{248}{3\\nu(1-\\chi/\\Delta+\\alpha)}"
  | .wolfLambda => "|V_{us}|" | .wolfA => "|V_{cb}|/\\lambda^2"
  | .wolfRho => "\\bar\\rho" | .wolfEta => "\\bar\\eta"
  | .sin2Theta12 => "\\sin^2\\theta_{12}" | .sin2Theta23 => "\\sin^2\\theta_{23}"
  | .sin2Theta13 => "\\sin^2\\theta_{13}" | .pmnsJ => "J_{PMNS}"
  | .delta => "\\Delta" | .nu => "\\nu" | .sigma => "\\sigma"
  | .chi => "\\chi" | .dimD => "D"
  | .cap => "\\pi\\Delta" | .mapT => "\\chi"
  | .protocol => "-\\frac{1}{D\\Delta-\\sigma}"
  | .governor => "-\\frac{\\chi}{\\Delta}"
  | .toll => "\\frac{\\chi(D\\Delta-\\sigma)}{(2\\nu)^3\\sigma D\\Delta}"
  | .margin => "\\frac{1}{(2D+\\sigma+2\\chi)(\\sigma+1)\\Delta^2}"
  | .lIntrinsic => "\\chi+\\nu+\\sigma" | .lEmbed => "2D+\\chi+\\nu+\\sigma"
  | .lSubstrate => "D\\Delta+\\nu" | .nSites => "2\\nu" | .rm => "D\\Delta"
  | .pm3J => "\\phi^2 T_{geo}" | .cabibbo => "\\pi/(\\nu-\\chi)"
  | .nc => "\\sigma-\\chi" | .weinbergGut => "\\frac{N_c}{2D}"
  | .alphaG => "B_{res}\\,\\alpha^{\\Delta/2}" | .boundaryStorage => "\\chi/(\\sigma-\\chi)"
  | .beta0 => "11-\\frac{2}{3}n_f"
  | .pmnsE11 => "|U_{ee}|^2"
  | .pmnsE12 => "|U_{emu}|^2"
  | .pmnsE13 => "|U_{etau}|^2"
  | .pmnsE21 => "|U_{mue}|^2"
  | .pmnsE22 => "|U_{mumu}|^2"
  | .pmnsE23 => "|U_{mutau}|^2"
  | .pmnsE31 => "|U_{taue}|^2"
  | .pmnsE32 => "|U_{taumu}|^2"
  | .pmnsE33 => "|U_{tautau}|^2"
  | .tauRatio => "\\Delta^2\\chi-\\Delta\\sigma-\\chi-D"
  | .protonRadius => "4\\hbar/(m_p c)"
  | .pion0MeV => "2\\alpha^{-1}-\\sigma\\chi+1/(\\nu-\\chi)"
  | .kaon0MeV => "(\\sigma+\\chi)\\alpha^{-1}-\\sigma+D\\sigma-2\\pi/(\\nu-\\chi)"
  | .kaonPlusMeV => "(\\sigma+\\chi)\\alpha^{-1}-\\sigma+D\\pi-1/\\sqrt2-\\alpha(\\sigma-\\chi)/\\chi"
  | .baryonPmJ => "B(\\mathrm{pm}J)"
  | .baryonPm3J => "B(\\mathrm{pm3}J)"
  | .upMeV => "m_{u}"
  | .downMeV => "m_{d}"
  | .strangeMeV => "m_{s}"
  | .charmMeV => "m_{c}"
  | .bottomMeV => "m_{b}"
  | .topMeV => "m_{t}"
  | .pionPlusMeV => "2\\alpha^{-1}-\\sigma\\chi+1/(\\nu-\\chi)+\\sigma+D-\\alpha(\\sigma-\\chi)/\\chi"
  | .fPiMeV => "f_\\pi=v/(\\Delta^2+\\Delta-\\chi)"
  | .fKMeV => "f_K=v/(\\Delta^2-\\nu^2)"
  | .wRatio => "\\sqrt{1-\\Delta/N_{sys}}"
  | .gaugeHyper => "129+5+16\\eta"
  | .gaugeColour => "12\\eta"
  | .zEq => "1075\\pi"
  | .darkRaw => "31/6"
  | .cLight => "c"
  | .vonKlitzing => "2\\pi c/\\alpha"
  | .planckChargeAtt => "\\sqrt{\\alpha^{-1}}"
  | .planckChargeRatio => "1/\\sqrt{\\alpha^{-1}}"
  | .planckMass => "m_e/\\sqrt{\\alpha_G}"
  | .ckmS13 => "s_{13}"
  | .ckmS23 => "s_{23}"
  | .ckmVcb => "|V_{cb}|"
  | .wMassUnc => "\\sqrt{g^2}\\,v/2\\;(\\mathrm{uncorrected})"
  | .zMassUnc => "\\sqrt{g^2+g'^2}\\,v/2\\;(\\mathrm{uncorrected})"
  | .gWeak => "g"
  | .gPrime => "g'"
  | .electronClosure => "y_e v/(\\sqrt2\\,m_e)"
  | .vud => "|V_{ud}|=c_{12}c_{13}"
  | .bRes => "B_{res}=\\nu-\\chi/(\\sigma-\\chi)-\\alpha"
  | .neutrinoFloor => "m_\\nu^{floor}"
  | .rydbergEV => "R_\\infty=\\alpha^2 m_e c^2/2"
  | .bohrRadius => "a_0=\\hbar c/(\\alpha m_e c^2)"
  | .shell4 => "\\sum_{\\ell=0}^{n-1}2(2\\ell+1)=2n^2"
  | .muonLifetimeSeconds => "\\tau_\\mu=192\\pi^3/(G_F^2 m_\\mu^5)"
  | .kaonPionRatio => "\\frac{\\Gamma_K}{\\Gamma_\\pi}=\\frac{\\pi^2}{196-\\pi^2}\\left(\\frac{70}{59}\\right)^2\\frac{m_K}{m_\\pi}\\frac{(1-m_\\mu^2/m_K^2)^2}{(1-m_\\mu^2/m_\\pi^2)^2}"
  | .pionLifetimePredicted => "\\frac{33}{32}\\,\\frac{8\\pi}{G_F^2 f_\\pi^2 m_\\pi m_\\mu^2(1-m_\\mu^2/m_\\pi^2)^2}"
  | .neutronLifetimePredicted => "\\frac{2\\pi^3}{G_F^2 |V_{ud}|^2 R\\,(1+3g_A^2)\\,(f_0+\\pi\\alpha P)},\\ g_A=5/4"
  | _ => ""

/-- Known interpretation caveats shown alongside an audit row. -/
def Key.caveat : Key → String
  | .wMassUnc => "uncorrected (tree-level); not scored, compare w_ratio"
  | .zMassUnc => "uncorrected (tree-level); not scored, compare w_ratio"
  | .darkRaw => "raw ratio before correction; not scored, compare omega_ratio"
  | .baryonPmJ => "Paper IV J; disagrees with Paper III (papers_disagree); not scored, compare baryon_pm3J"
  | .hubbleLate => "late-universe value; the CMB and BBN-calibrated DES references show the Hubble tension and are not scored"
  | .clusteringLate => "late-universe value; the CMB reference shows the S8 tension and is not scored"
  | .vud => "undressed; compare vud_dressed"
  | .muonRatio => "documented ~2.4σ model tension"
  | .tauRatio => "documented ~2.1σ model tension"
  | .upMeV | .downMeV | .charmMeV => "documented model tension"
  | .fKMeV => "FLAG 2024 lattice ~3.8σ low; assigned fK formula"
  | .fPiMeV => "FLAG 2024 lattice agrees"
  | .tauLifetimeFs => "uses measured muon lifetime and B_e"
  | .muonLifetimeFinite => "finite 3x3x3 channel; all modes open; broad natural-unit interval"
  | .tauLifetimeE8Natural => "E8 muon input; broad natural-unit interval"
  | .neutronSpectralFraction => "finite 3x3x3 channel; only lowest mode open; crude bounds"
  | .neutronLifetimeE8 => "finite 3x3x3 channel; broad natural-unit interval"
  | .muonLifetimeSeconds => "tree level, E8 G_F and m_mu; the measured value includes the QED factor 1-(alpha/2pi)(pi^2-25/4) and the m_e^2/m_mu^2 phase space (together 0.99562); reference not scored"
  | .kaonPionRatio => "G_F, m_mu^2 and any common correction cancel; |V_ud|^2 on the pion as |V_us|^2 on the kaon (without it: -6.3%); the measured ratio includes the SM electromagnetic difference (about -0.7%); the rest is f_K/f_pi = 70/59 (FLAG 1.1934)"
  | .pionLifetimePredicted => "E8 two-body width with the 32/33 pion-channel margin (SM: |V_ud|^2(1+delta_rad) = 0.970); m_e and hbar c are unit inputs; pi->mu nu is 99.988% of the total width"
  | .neutronLifetimeSeconds => "unmargined finite channel; unit conversion using measured m_e and hbar c; broad interval (see neutron_lifetime_predicted_s)"
  | .neutronLifetimePredicted => "continuum route: the emitted electron is not confined, so its modes are the continuum limit of the lattice; phase space as for the muon, Fermi factor to first order (full factor 922.9 s); remaining gap: g_A (5/4 vs 1.2754) and the low-energy radiative correction"
  | .neutronLifetimeUnified => "3x3x3 spectral template (comparison): the continuum route without Coulomb to 0.6%; see neutron_lifetime_predicted_s"
  | .pionFiniteWidth | .pionFiniteLifetime
  | .kaonFiniteWidth | .kaonFiniteLifetime
  | .neutralPionFiniteWidth | .neutralPionFiniteLifetime =>
      "finite 3x3x3 channel; all modes open; broad interval"
  | .rydbergEV | .bohrRadius => "atoms comparison; unit-sensitive"
  | _ => ""

end E8PConstants
