import PMConstants.CurrentConstants
import PMSubstrate.Impedance
import PMConstants.GravityAccounting
import PMConstants.Depth
import PMFlavor.PMNSIntervals
import PMFlavor.CKM
import PMFlavor.CabibboDressing
import PMCosmology.Scaling
import PMCosmology.SubstrateLoad
import PMCosmology.Tensions
import PMCosmology.Primordial
import PMElementaryParticles.CompositeMasses
import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.QuarkMasses
import PMElementaryParticles.TauLifetime
import PMConstants.WMassTest
import PMConstants.GaugeLedgers
import PMConstants.ColourChannels
import PMCosmology.Background
import PMSubstrate.Readouts
import E8PConstants.PlanckReadout
import E8PConstants.ExperimentalComparison
import E8PConstants.AlphaClockComparison
import E8PConstants.E8TickUnit
import E8PConstants.ExperimentalPulls
import E8PConstants.ScalarAccounting
import E8PConstants.FlavourPulls
import E8PConstants.CompositeMassPulls
import E8PConstants.HyperScope
import PMConstants.ElectroweakBounds
import PMConstants.ElectroweakE8
import PMConstants.JointConstants
import PMConstants.FloorNeutrino
import PMAtoms
import PMFlavor.Wolfenstein
import PMFlavor.PMNSIntervals
import E8PConstants

/-! Build-time certificates for the executable's exact shared catalog.
This module is a required build dependency of `pm-constants`, but is not
linked into its lightweight runtime. No Real definition is evaluated there. -/
noncomputable section
namespace PMConstants.ConstantReport
open E8PConstants

def value : Key → ℝ
  | .inverseAlpha => PMSubstrate.geometricIndex
  | .alpha => CurrentConstants.alpha
  | .overhead => overhead
  | .footprint => footprint
  | .weakFraction => CurrentConstants.weakFraction
  | .scalar => CurrentConstants.scalar
  | .scalarToll => scalarToll
  | .electronYukawa => CurrentConstants.electronYukawa
  | .strong => CurrentConstants.strong
  | .vevRatio => ElectroweakE8.vevRatio CertifiedConstants.α
  | .electronMassInput => ElectroweakBounds.electronGeV
  | .vev => ElectroweakE8.vev CertifiedConstants.α ElectroweakBounds.electronGeV
  | .higgsMass => ElectroweakE8.higgsMass CertifiedConstants.α ElectroweakBounds.electronGeV
  | .fermi => ElectroweakE8.fermi CertifiedConstants.α ElectroweakBounds.electronGeV
  | .jarlskog => PMFlavor.CKM.pmJ
  | .load => PMCosmology.loadFactor
  | .hubbleLate => (674 : ℝ) / 10 * PMCosmology.loadFactor
  | .clusteringLate => (832 : ℝ) / 1000 / PMCosmology.loadFactor
  | .protonRatio => PMElementaryParticles.CompositeMasses.proton
  | .neutronRatio => PMElementaryParticles.CompositeMasses.neutron
  | .muonRatio => PMElementaryParticles.LeptonMasses.muon
  | .hubbleSigma => (1 / 2 : ℝ) * PMCosmology.loadFactor
  | .s8Sigma => ((13 : ℝ) / 1000) / PMCosmology.loadFactor
  | .omegaRatio => PMCosmology.Tensions.omegaRatio
  | .wolfLambda => PMFlavor.Wolfenstein.wLam
  | .wolfA => PMFlavor.Wolfenstein.wA
  | .wolfRho => PMFlavor.Wolfenstein.wRho
  | .wolfEta => PMFlavor.Wolfenstein.wEta
  | .sin2Theta12 => PMFlavor.PMNS.sineSquared 0
  | .sin2Theta23 => PMFlavor.PMNS.sineSquared 1
  | .sin2Theta13 => PMFlavor.PMNS.sineSquared 2
  | .pmnsJ => PMFlavor.CKM.jarlskog PMFlavor.PMNS.matrix
  | .delta => (PMSubstrate.baseline.period : ℝ)
  | .nu => (PMSubstrate.baseline.sectorChannels : ℝ)
  | .sigma => (PMSubstrate.baseline.embeddingDimension : ℝ)
  | .chi => (PMSubstrate.baseline.eulerCharacteristic : ℝ)
  | .dimD => (PMSubstrate.baseline.dimension : ℝ)
  | .cap => PMSubstrate.capacityTerm PMSubstrate.baseline
  | .mapT => PMSubstrate.mapTerm PMSubstrate.baseline
  | .protocol => PMSubstrate.protocolTerm PMSubstrate.baseline
  | .governor => PMSubstrate.governorTerm PMSubstrate.baseline
  | .toll => PMSubstrate.tollTerm PMSubstrate.baseline
  | .margin => PMSubstrate.marginTerm PMSubstrate.baseline
  | .lIntrinsic => (PMSubstrate.baseline.intrinsicLoad : ℝ)
  | .lEmbed => (PMSubstrate.baseline.embeddingLoad : ℝ)
  | .lSubstrate => (PMSubstrate.baseline.substrateLoad : ℝ)
  | .nSites => (PMSubstrate.baseline.nodeCapacity : ℝ)
  | .rm => (PMSubstrate.baseline.resolution : ℝ)
  | .pm3J => PMFlavor.CKM.pm3J
  | .cabibbo => PMFlavor.CKM.s12
  | .nc => ((PMSubstrate.baseline.embeddingDimension - PMSubstrate.baseline.eulerCharacteristic : ℕ) : ℝ)
  | .weinbergGut => ((PMSubstrate.baseline.embeddingDimension - PMSubstrate.baseline.eulerCharacteristic : ℕ) : ℝ) / (2 * (PMSubstrate.baseline.dimension : ℝ))
  | .alphaG => PMConstants.Depth.gravity PMConstants.CertifiedConstants.α
  | .boundaryStorage => (PMSubstrate.baseline.eulerCharacteristic : ℝ) / ((PMSubstrate.baseline.embeddingDimension : ℝ) - PMSubstrate.baseline.eulerCharacteristic)
  | .beta0 => PMConstants.beta0 3
  | .pmnsE11 => Complex.normSq (PMFlavor.PMNS.matrix 0 0)
  | .pmnsE12 => Complex.normSq (PMFlavor.PMNS.matrix 0 1)
  | .pmnsE13 => Complex.normSq (PMFlavor.PMNS.matrix 0 2)
  | .pmnsE21 => Complex.normSq (PMFlavor.PMNS.matrix 1 0)
  | .pmnsE22 => Complex.normSq (PMFlavor.PMNS.matrix 1 1)
  | .pmnsE23 => Complex.normSq (PMFlavor.PMNS.matrix 1 2)
  | .pmnsE31 => Complex.normSq (PMFlavor.PMNS.matrix 2 0)
  | .pmnsE32 => Complex.normSq (PMFlavor.PMNS.matrix 2 1)
  | .pmnsE33 => Complex.normSq (PMFlavor.PMNS.matrix 2 2)
  | .tauRatio => PMElementaryParticles.LeptonMasses.tau
  | .protonRadius => 4 * PMElementaryParticles.CompositeMasses.hbarc / (PMElementaryParticles.CompositeMasses.proton * PMElementaryParticles.CompositeMasses.me)
  | .pion0MeV => PMElementaryParticles.CompositeMasses.pion0 * PMElementaryParticles.CompositeMasses.me
  | .kaon0MeV => PMElementaryParticles.CompositeMasses.kaon0 * PMElementaryParticles.CompositeMasses.me
  | .kaonPlusMeV => PMElementaryParticles.CompositeMasses.kaonPlus * PMElementaryParticles.CompositeMasses.me
  | .baryonPmJ => PMCosmology.Primordial.baryonRatio PMFlavor.CKM.pmJ
  | .baryonPm3J => PMCosmology.Primordial.baryonRatio PMFlavor.CKM.pm3J
  | .upMeV => PMElementaryParticles.QuarkMasses.up * PMElementaryParticles.CompositeMasses.me
  | .downMeV => PMElementaryParticles.QuarkMasses.down * PMElementaryParticles.CompositeMasses.me
  | .strangeMeV => PMElementaryParticles.QuarkMasses.strange * PMElementaryParticles.CompositeMasses.me
  | .charmMeV => PMElementaryParticles.QuarkMasses.charm * PMElementaryParticles.CompositeMasses.me
  | .bottomMeV => PMElementaryParticles.QuarkMasses.bottom * PMElementaryParticles.CompositeMasses.me
  | .topMeV => PMElementaryParticles.QuarkMasses.top * PMElementaryParticles.CompositeMasses.me
  | .pionPlusMeV => PMElementaryParticles.LeptonMasses.pionPlus * PMElementaryParticles.CompositeMasses.me
  | .wRatio => Real.sqrt (1 - PMConstants.clockRatio)
  | .gaugeHyper => PMConstants.GaugeLedgers.ledger PMConstants.GaugeLedgers.reqY
  | .gaugeColour => PMConstants.ColourChannels.colourLedger
  | .zEq => 1075 * Real.pi
  | .darkRaw => PMCosmology.darkRatio
  | .cLight => PMSubstrate.speedOfLight
  | .vonKlitzing => PMSubstrate.vonKlitzing
  | .planckChargeAtt => PMSubstrate.planckChargeAttenuation
  | .planckChargeRatio => PMSubstrate.planckChargeRatio
  | .planckMass => E8PConstants.PlanckReadout.planckMass
  | .ckmS13 => PMFlavor.CKM.s13
  | .ckmS23 => PMFlavor.CKM.s23
  | .ckmVcb => PMFlavor.CKM.vcb
  | .wMassUnc => Real.sqrt (PMConstants.GaugeSpectrum.wMassSquared PMConstants.CertifiedConstants.α PMConstants.ElectroweakBounds.electronGeV)
  | .zMassUnc => Real.sqrt (PMConstants.GaugeSpectrum.zMassSquared PMConstants.CertifiedConstants.α PMConstants.ElectroweakBounds.electronGeV)
  | .gWeak => Real.sqrt (PMConstants.ElectroweakE8.weakSquared PMConstants.CertifiedConstants.α)
  | .gPrime => Real.sqrt (PMConstants.ElectroweakE8.hyperchargeSquared PMConstants.CertifiedConstants.α)
  | .electronClosure => PMConstants.JointConstants.electronClosureRatio
  | .vud => PMFlavor.CKM.c12 * PMFlavor.CKM.c13
  | .vudDressed => PMFlavor.CabibboDressing.vudDressed
  | .tauLifetimeFs => PMElementaryParticles.TauLifetime.tauLife
  | .muonLifetimeFinite => PMAtoms.muonFiniteLifetime
  | .tauLifetimeE8Natural => PMElementaryParticles.TauE8.tauLifetimeE8
  | .neutronSpectralFraction => PMAtoms.neutronSpectralFraction
  | .neutronLifetimeE8 => PMAtoms.neutronLifetimeE8
  | .muonLifetimeSeconds => PMElementaryParticles.PhysicalUnits.muonLifetimeSeconds
  | .neutronLifetimeSeconds => PMAtoms.neutronLifetimeSeconds
  | .pionFiniteWidth => PMAtoms.pionFiniteWidth
  | .pionFiniteLifetime => PMAtoms.pionFiniteLifetime
  | .kaonFiniteWidth => PMAtoms.kaonFiniteWidth
  | .kaonFiniteLifetime => PMAtoms.kaonFiniteLifetime
  | .neutralPionFiniteWidth => PMAtoms.neutralPionFiniteWidth
  | .neutralPionFiniteLifetime => PMAtoms.neutralPionFiniteLifetime
  | .pionFiniteLifetimeSeconds => PMAtoms.pionFiniteLifetimeSeconds
  | .kaonFiniteLifetimeSeconds => PMAtoms.kaonFiniteLifetimeSeconds
  | .neutralPionFiniteLifetimeSeconds => PMAtoms.neutralPionFiniteLifetimeSeconds
  | .bRes => PMConstants.residual PMConstants.CertifiedConstants.α
  | .neutrinoFloor => PMConstants.Bulk.floorMass PMConstants.CertifiedConstants.α PMConstants.FloorNeutrino.meEV
  | .rydbergEV => PMAtoms.rydbergEV
  | .bohrRadius => PMAtoms.bohrRadiusAngstrom
  | .shell4 => PMAtoms.shellCapacity 4

/-- Every runtime row is certified against the named current model definition. -/
theorem catalog_sound (k : Key) : ((bounds k).1 : ℝ) ≤ value k ∧ value k ≤ ((bounds k).2 : ℝ) := by
  cases k with
  | inverseAlpha =>
    have h := PMSubstrate.geometricIndex_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | alpha =>
    have h := CertifiedConstants.alpha_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | electronYukawa =>
    have h := CurrentConstants.electron_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | strong =>
    have h := CurrentConstants.strong_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | vevRatio =>
    have h := JointConstants.vev_ratio_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | vev =>
    have h := ElectroweakBounds.vev_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | higgsMass =>
    have h := ElectroweakBounds.higgs_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | fermi =>
    have h := ElectroweakBounds.fermi_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | jarlskog =>
    have h := PMFlavor.CKM.pmJ_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | protonRatio =>
    have h := PMElementaryParticles.CompositeMasses.proton_value
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | neutronRatio =>
    have h := PMElementaryParticles.CompositeMasses.neutron_value
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | muonRatio =>
    have h := PMElementaryParticles.LeptonMasses.muon_value
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | omegaRatio =>
    have h := PMCosmology.Tensions.omegaRatio_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | wolfLambda =>
    have h := PMFlavor.Wolfenstein.wLam_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | wolfA =>
    have h := PMFlavor.Wolfenstein.wA_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | wolfRho =>
    have h := PMFlavor.Wolfenstein.wRho_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | wolfEta =>
    have h := PMFlavor.Wolfenstein.wEta_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | sin2Theta12 =>
    have h := PMFlavor.PMNSIntervals.input_bounds (0 : Fin 3)
    have h1 : (0.30901 : ℝ) < PMFlavor.PMNS.sineSquared (0 : Fin 3) := by simpa using h.1
    have h2 : PMFlavor.PMNS.sineSquared (0 : Fin 3) < (0.30902 : ℝ) := by simpa using h.2
    norm_num [bounds, value]
    exact ⟨by linarith, by linarith⟩
  | sin2Theta23 =>
    have h := PMFlavor.PMNSIntervals.input_bounds (1 : Fin 3)
    have h1 : (0.57479 : ℝ) < PMFlavor.PMNS.sineSquared (1 : Fin 3) := by simpa using h.1
    have h2 : PMFlavor.PMNS.sineSquared (1 : Fin 3) < (0.57481 : ℝ) := by simpa using h.2
    norm_num [bounds, value]
    exact ⟨by linarith, by linarith⟩
  | sin2Theta13 =>
    have h := PMFlavor.PMNSIntervals.input_bounds (2 : Fin 3)
    have h1 : (0.0218920 : ℝ) < PMFlavor.PMNS.sineSquared (2 : Fin 3) := by simpa using h.1
    have h2 : PMFlavor.PMNS.sineSquared (2 : Fin 3) < (0.0218921 : ℝ) := by simpa using h.2
    norm_num [bounds, value]
    exact ⟨by linarith, by linarith⟩
  | pmnsJ =>
    have h := PMFlavor.PMNSIntervals.jarlskog_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | delta => norm_num [bounds, value, PMSubstrate.baseline]
  | nu => norm_num [bounds, value, PMSubstrate.baseline]
  | sigma => norm_num [bounds, value, PMSubstrate.baseline]
  | chi => norm_num [bounds, value, PMSubstrate.baseline]
  | dimD => norm_num [bounds, value, PMSubstrate.baseline]
  | cap =>
    have h1 := Real.pi_gt_d20
    have h2 := Real.pi_lt_d20
    norm_num [bounds, value, PMSubstrate.capacityTerm, PMSubstrate.baseline] at ⊢
    constructor <;> nlinarith
  | mapT => norm_num [bounds, value, PMSubstrate.mapTerm, PMSubstrate.baseline]
  | protocol => norm_num [bounds, value, PMSubstrate.protocolTerm, PMSubstrate.baseline,
      PMSubstrate.Parameters.resolution]
  | governor => norm_num [bounds, value, PMSubstrate.governorTerm, PMSubstrate.baseline]
  | toll => norm_num [bounds, value, PMSubstrate.tollTerm, PMSubstrate.baseline,
      PMSubstrate.Parameters.nodeCapacity, PMSubstrate.Parameters.resolution]
  | margin => norm_num [bounds, value, PMSubstrate.marginTerm, PMSubstrate.baseline,
      PMSubstrate.Parameters.embeddingLoad, PMSubstrate.Parameters.intrinsicLoad]
  | lIntrinsic => norm_num [bounds, value, PMSubstrate.baseline, PMSubstrate.Parameters.intrinsicLoad]
  | lEmbed => norm_num [bounds, value, PMSubstrate.baseline, PMSubstrate.Parameters.embeddingLoad, PMSubstrate.Parameters.intrinsicLoad]
  | lSubstrate => norm_num [bounds, value, PMSubstrate.baseline, PMSubstrate.Parameters.substrateLoad, PMSubstrate.Parameters.resolution]
  | nSites => norm_num [bounds, value, PMSubstrate.baseline, PMSubstrate.Parameters.nodeCapacity]
  | rm => norm_num [bounds, value, PMSubstrate.baseline, PMSubstrate.Parameters.resolution]
  | nc => norm_num [bounds, value, PMSubstrate.baseline]
  | weinbergGut => norm_num [bounds, value, PMSubstrate.baseline]
  | boundaryStorage => norm_num [bounds, value, PMSubstrate.baseline]
  | pm3J =>
    have h := PMFlavor.CKM.pm3J_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | cabibbo =>
    have h := PMFlavor.CKM.s12_bounds
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | beta0 => norm_num [bounds, value, PMConstants.beta0]
  | pmnsE11 =>
    have h := PMFlavor.PMNSIntervals.squared_entry_bounds 0 0
    norm_num [bounds, value, PMFlavor.PMNSIntervals.lower, PMFlavor.PMNSIntervals.upper] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | pmnsE12 =>
    have h := PMFlavor.PMNSIntervals.squared_entry_bounds 0 1
    norm_num [bounds, value, PMFlavor.PMNSIntervals.lower, PMFlavor.PMNSIntervals.upper] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | pmnsE13 =>
    have h := PMFlavor.PMNSIntervals.squared_entry_bounds 0 2
    norm_num [bounds, value, PMFlavor.PMNSIntervals.lower, PMFlavor.PMNSIntervals.upper] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | pmnsE21 =>
    have h := PMFlavor.PMNSIntervals.squared_entry_bounds 1 0
    norm_num [bounds, value, PMFlavor.PMNSIntervals.lower, PMFlavor.PMNSIntervals.upper] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | pmnsE22 =>
    have h := PMFlavor.PMNSIntervals.squared_entry_bounds 1 1
    norm_num [bounds, value, PMFlavor.PMNSIntervals.lower, PMFlavor.PMNSIntervals.upper] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | pmnsE23 =>
    have h := PMFlavor.PMNSIntervals.squared_entry_bounds 1 2
    norm_num [bounds, value, PMFlavor.PMNSIntervals.lower, PMFlavor.PMNSIntervals.upper] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | pmnsE31 =>
    have h := PMFlavor.PMNSIntervals.squared_entry_bounds 2 0
    norm_num [bounds, value, PMFlavor.PMNSIntervals.lower, PMFlavor.PMNSIntervals.upper] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | pmnsE32 =>
    have h := PMFlavor.PMNSIntervals.squared_entry_bounds 2 1
    norm_num [bounds, value, PMFlavor.PMNSIntervals.lower, PMFlavor.PMNSIntervals.upper] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | upMeV =>
    have h := PMElementaryParticles.QuarkMasses.pulls
    norm_num [bounds, value, PMElementaryParticles.QuarkMasses.up, PMElementaryParticles.QuarkMasses.down,
      PMElementaryParticles.QuarkMasses.strange, PMElementaryParticles.QuarkMasses.charm, PMElementaryParticles.QuarkMasses.bottom,
      PMElementaryParticles.QuarkMasses.top, PMElementaryParticles.QuarkMasses.η, PMElementaryParticles.CompositeMasses.me] at h ⊢
  | downMeV =>
    have h := PMElementaryParticles.QuarkMasses.pulls
    norm_num [bounds, value, PMElementaryParticles.QuarkMasses.up, PMElementaryParticles.QuarkMasses.down,
      PMElementaryParticles.QuarkMasses.strange, PMElementaryParticles.QuarkMasses.charm, PMElementaryParticles.QuarkMasses.bottom,
      PMElementaryParticles.QuarkMasses.top, PMElementaryParticles.QuarkMasses.η, PMElementaryParticles.CompositeMasses.me] at h ⊢
  | strangeMeV =>
    have h := PMElementaryParticles.QuarkMasses.pulls
    norm_num [bounds, value, PMElementaryParticles.QuarkMasses.up, PMElementaryParticles.QuarkMasses.down,
      PMElementaryParticles.QuarkMasses.strange, PMElementaryParticles.QuarkMasses.charm, PMElementaryParticles.QuarkMasses.bottom,
      PMElementaryParticles.QuarkMasses.top, PMElementaryParticles.QuarkMasses.η, PMElementaryParticles.CompositeMasses.me] at h ⊢
  | charmMeV =>
    have h := PMElementaryParticles.QuarkMasses.pulls
    norm_num [bounds, value, PMElementaryParticles.QuarkMasses.up, PMElementaryParticles.QuarkMasses.down,
      PMElementaryParticles.QuarkMasses.strange, PMElementaryParticles.QuarkMasses.charm, PMElementaryParticles.QuarkMasses.bottom,
      PMElementaryParticles.QuarkMasses.top, PMElementaryParticles.QuarkMasses.η, PMElementaryParticles.CompositeMasses.me] at h ⊢
  | bottomMeV =>
    have h := PMElementaryParticles.QuarkMasses.pulls
    norm_num [bounds, value, PMElementaryParticles.QuarkMasses.up, PMElementaryParticles.QuarkMasses.down,
      PMElementaryParticles.QuarkMasses.strange, PMElementaryParticles.QuarkMasses.charm, PMElementaryParticles.QuarkMasses.bottom,
      PMElementaryParticles.QuarkMasses.top, PMElementaryParticles.QuarkMasses.η, PMElementaryParticles.CompositeMasses.me] at h ⊢
  | topMeV =>
    have h := PMElementaryParticles.QuarkMasses.pulls
    norm_num [bounds, value, PMElementaryParticles.QuarkMasses.up, PMElementaryParticles.QuarkMasses.down,
      PMElementaryParticles.QuarkMasses.strange, PMElementaryParticles.QuarkMasses.charm, PMElementaryParticles.QuarkMasses.bottom,
      PMElementaryParticles.QuarkMasses.top, PMElementaryParticles.QuarkMasses.η, PMElementaryParticles.CompositeMasses.me] at h ⊢
  | rydbergEV =>
    have h := PMAtoms.rydbergEV_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | bohrRadius =>
    have h := PMAtoms.bohrRadius_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | shell4 =>
    have h := PMAtoms.shell_capacities
    norm_num [bounds, value] at h ⊢
    exact ⟨h.2.2.2.le, h.2.2.2.le⟩
  | vud =>
    have h := PMFlavor.CKM.vud_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | vudDressed =>
    have h := PMFlavor.CabibboDressing.vudDressed_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | tauLifetimeFs =>
    have h := PMElementaryParticles.TauLifetime.tau_lifetime_tree
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | muonLifetimeFinite =>
    have h := PMAtoms.muonFiniteLifetime_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | tauLifetimeE8Natural =>
    have h := PMElementaryParticles.TauE8.tauLifetimeE8_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | neutronSpectralFraction =>
    have h := PMAtoms.neutronSpectralFraction_bounds_weighted
    norm_num [bounds, value] at h ⊢
    exact h
  | neutronLifetimeE8 =>
    have h := PMAtoms.neutronLifetimeE8_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | muonLifetimeSeconds =>
    have h := PMElementaryParticles.PhysicalUnits.muonLifetimeSeconds_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | neutronLifetimeSeconds =>
    have h := PMAtoms.neutronLifetimeSeconds_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | pionFiniteWidth =>
    have h := PMAtoms.pionFiniteWidth_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | pionFiniteLifetime =>
    have h := PMAtoms.pionFiniteLifetime_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | kaonFiniteWidth =>
    have h := PMAtoms.kaonFiniteWidth_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | kaonFiniteLifetime =>
    have h := PMAtoms.kaonFiniteLifetime_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | neutralPionFiniteWidth =>
    have h := PMAtoms.neutralPionFiniteWidth_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | neutralPionFiniteLifetime =>
    have h := PMAtoms.neutralPionFiniteLifetime_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | pionFiniteLifetimeSeconds =>
    have h := PMAtoms.pionFiniteLifetimeSeconds_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | kaonFiniteLifetimeSeconds =>
    have h := PMAtoms.kaonFiniteLifetimeSeconds_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | neutralPionFiniteLifetimeSeconds =>
    have h := PMAtoms.neutralPionFiniteLifetimeSeconds_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | bRes =>
    have h := PMConstants.GravityAccounting.residual_tight_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | neutrinoFloor =>
    have h := PMConstants.FloorNeutrino.floor_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | wMassUnc =>
    have h := PMConstants.ElectroweakBounds.w_mass_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | zMassUnc =>
    have h := PMConstants.ElectroweakBounds.z_mass_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | gWeak =>
    have h := PMConstants.ElectroweakBounds.coupling_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.1.le, h.1.2.le⟩
  | gPrime =>
    have h := PMConstants.ElectroweakBounds.coupling_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.2.1.1.le, h.2.1.2.le⟩
  | electronClosure =>
    have h := PMConstants.JointConstants.electron_closure_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | cLight => norm_num [bounds, value, PMSubstrate.speedOfLight]
  | vonKlitzing =>
    have h := PMSubstrate.vonKlitzing_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | planckChargeAtt =>
    have h := PMSubstrate.planckChargeAttenuation_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | planckChargeRatio =>
    have h := PMSubstrate.planckChargeRatio_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | planckMass =>
    have h := E8PConstants.PlanckReadout.planckMass_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | ckmS13 =>
    have h := PMFlavor.CKM.s13_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | ckmS23 =>
    have h := PMFlavor.CKM.s23_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | ckmVcb =>
    have h := PMFlavor.CKM.vcb_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | gaugeHyper =>
    have h : PMConstants.GaugeLedgers.ledger PMConstants.GaugeLedgers.reqY = 6446/43 := by
      rw [PMConstants.GaugeLedgers.hyper_value]; norm_num [PMConstants.overhead]
    simp only [value]; rw [h]; norm_num [bounds]
  | gaugeColour =>
    simp [bounds, value, PMConstants.ColourChannels.colour_ledger]
  | zEq =>
    have h := PMCosmology.Background.z_eq_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | darkRaw =>
    norm_num [bounds, value, PMCosmology.darkRatio]
  | pionPlusMeV =>
    have h := PMElementaryParticles.LeptonMasses.pionPlus_mass
    rw [abs_lt] at h
    norm_num [bounds, value] at h ⊢
    constructor <;> linarith [h.1, h.2]
  | wRatio =>
    have h := PMConstants.WMassTest.ratio_bounds
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | tauRatio => norm_num [bounds, value, PMElementaryParticles.LeptonMasses.tau]
  | protonRadius =>
    have h := PMElementaryParticles.CompositeMasses.proton_radius
    rw [abs_lt] at h
    norm_num [bounds, value] at h ⊢
    constructor <;> linarith [h.1, h.2]
  | pion0MeV =>
    have h := PMElementaryParticles.CompositeMasses.pion_mass
    rw [abs_lt] at h
    norm_num [bounds, value] at h ⊢
    constructor <;> linarith [h.1, h.2]
  | kaon0MeV =>
    have h := PMElementaryParticles.CompositeMasses.kaon0_mass
    rw [abs_lt] at h
    norm_num [bounds, value] at h ⊢
    constructor <;> linarith [h.1, h.2]
  | kaonPlusMeV =>
    have h := PMElementaryParticles.CompositeMasses.kaonPlus_mass
    rw [abs_lt] at h
    norm_num [bounds, value] at h ⊢
    constructor <;> linarith [h.1, h.2]
  | baryonPmJ =>
    have h := PMCosmology.Primordial.baryon_windows
    norm_num [bounds, value] at h ⊢
    exact ⟨h.1.le, h.2.1.le⟩
  | baryonPm3J =>
    have h := PMCosmology.Primordial.baryon_windows
    norm_num [bounds, value] at h ⊢
    exact ⟨h.2.2.1.le, h.2.2.2.le⟩
  | pmnsE33 =>
    have h := PMFlavor.PMNSIntervals.squared_entry_bounds 2 2
    norm_num [bounds, value, PMFlavor.PMNSIntervals.lower, PMFlavor.PMNSIntervals.upper] at h ⊢
    exact ⟨h.1.le, h.2.le⟩
  | alphaG =>
    have h := PMConstants.GravityAccounting.channels_as_frame
    norm_num [bounds, value] at ⊢
    constructor <;> linarith [h.1, h.2]
  | hubbleSigma => norm_num [bounds, value, PMCosmology.loadFactor]
  | s8Sigma => norm_num [bounds, value, PMCosmology.loadFactor]
  | load => norm_num [bounds, value, PMCosmology.loadFactor]
  | hubbleLate => norm_num [bounds, value, PMCosmology.loadFactor]
  | clusteringLate => norm_num [bounds, value, PMCosmology.loadFactor]
  | overhead | footprint | weakFraction | scalar | scalarToll | electronMassInput =>
    norm_num [bounds, value, CurrentConstants.weakFraction, CurrentConstants.scalar,
      overhead, footprint, clockRatio, selfCoupling, scalarToll, ElectroweakBounds.electronGeV]

theorem keys_complete (k : Key) : k ∈ keys := by cases k <;> simp [keys]
theorem keys_unique : keys.Nodup := by decide

/-- Exact outward rounding of arbitrary rational endpoints, including negatives. -/
theorem rounded_lower (q : Rat) (digits : Nat) :
    (lowerScaled q digits : Rat) / scale digits ≤ q := by
  have hs : (0 : Rat) < scale digits := by unfold scale; positivity
  apply (div_le_iff₀ hs).mpr
  exact Rat.floor_le (q * scale digits)

theorem rounded_upper (q : Rat) (digits : Nat) :
    q ≤ (upperScaled q digits : Rat) / scale digits := by
  have hs : (0 : Rat) < scale digits := by unfold scale; positivity
  apply (le_div_iff₀ hs).mpr
  exact Rat.le_ceil

/-- The exact fractions represented by the printed decimal bounds enclose the
model value for every requested precision; extra digits do not tighten the catalog. -/
theorem rounded_catalog_sound (k : Key) (digits : Nat) :
    (((lowerScaled (bounds k).1 digits : Rat) / scale digits : Rat) : ℝ) ≤ value k ∧
      value k ≤ (((upperScaled (bounds k).2 digits : Rat) / scale digits : Rat) : ℝ) := by
  have hl : (((lowerScaled (bounds k).1 digits : Rat) / scale digits : Rat) : ℝ) ≤
      ((bounds k).1 : ℝ) := by exact_mod_cast rounded_lower (bounds k).1 digits
  have hu : ((bounds k).2 : ℝ) ≤
      (((upperScaled (bounds k).2 digits : Rat) / scale digits : Rat) : ℝ) := by
    exact_mod_cast rounded_upper (bounds k).2 digits
  exact ⟨hl.trans (catalog_sound k).1, (catalog_sound k).2.trans hu⟩

end PMConstants.ConstantReport
