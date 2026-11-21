import PMAtoms.Nucleus
import PMAtoms.Hydrogen
import PMAtoms.ElectronCloud
import PMAtoms.Aufbau
import PMAtoms.ShellGaps
import PMAtoms.E8Tick
import PMAtoms.FissionYield
import PMAtoms.AlphaFinite
import PMAtoms.ClockHierarchy
import PMAtoms.CertifiedEnclosure
import PMAtoms.NuclearRegime
import PMAtoms.HundRule
import PMAtoms.NuclearGraph
import PMAtoms.NuclearLine
import PMAtoms.NuclearCharge

/-!
# PMAtoms canonical values

Single import for the atomic and nuclear values used by `e8p`. These are
re-exports of the owning PMAtoms definitions and theorems; no new computation
is introduced here.

* Nuclear types and graph data: `Nuclide`, `h3Label`, `he3Label`, `he4Label`,
  `completeEdgeCount`, `lineCounts`.
* Hydrogen and atomic units: `rydbergEV`, `bohrRadius`, `electronMassEV`,
  `hbarCEVAngstrom`, and their bounds.
* Electron cloud: `cloudSum`, `bindingEV_fillCloud`, `fillCloud`, `orbitalList`.
* Aufbau and shell structure: `configuration`, `nilssonE8CostQ`, `hoShell`,
  `nilssonE8_gaps`, `largestGapFills`, `largestGapFills_eq`.
* Nuclear ledger: `certifiedMass`, `cmLo`, `cmHi`, `certifiedMass_bounds`,
  `regimeOf`, `deformedFrontierB`, `Hund.groundMultiplicity`.
* Ticks and decay scales: `e8Tick`, `lifetimeTicks`, `fissionFullLifetime`,
  `alphaFlux`, `alphaWorkload`, `alphaAttempt`, `nestedPeriod`.
-/

namespace PMAtoms.Values

export PMAtoms
  (Nuclide h3Label he3Label he4Label completeEdgeCount lineCounts
    chargeEnergy3 chargeEnergy3_H3 chargeEnergy3_He3
    chargeEnergy4 chargeEnergy4_He4)
export PMAtoms
  (rydbergEV rydbergEV_bounds bohrRadius bohrRadius_bounds bohrRadiusAngstrom
    electronMassEV hbarCEVAngstrom)
export PMAtoms
  (cloudSum bindingEV_fillCloud fillCloud orbitalList)
export PMAtoms.Aufbau (configuration)
export PMAtoms.Cloud (bindingEV binding_nonpos massCorrectionME)
export PMAtoms
  (NuclearOrbital nilssonE8CostQ hoShell nilssonE8_gaps
    nilssonE8_spinOrbit_closures nilssonKappa_eq_channel nilssonMu_eq_latency
    shellOrbitals shellLadder largestGapFills largestGapFills_eq)
export PMAtoms
  (cmLo cmHi certifiedMass certifiedMass_bounds regimeOf deformedFrontier
    deformedFrontierB)
export PMAtoms.Hund (groundMultiplicity configSpin2 observedMultiplicity)
export PMAtoms
  (e8Tick e8Tick_eq lifetimeTicks lifetimeTicks_eq
    u238 cm244 cf252 fissionFullLifetime
    alphaFlux alphaFlux_eq alphaWorkload alphaWorkload_pos
    alphaAttempt alphaAttempt_pos nestedPeriod)

end PMAtoms.Values
