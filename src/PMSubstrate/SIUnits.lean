import Mathlib.Tactic

/-!
# SI unit conversions (measured, not predicted)

Every mass PM predicts is a pure number in units of the electron mass (`m_μ/m_e`, the quark
masses, `G_F` in `m_e⁻²`, lifetimes in `m_e⁻¹`). The electron mass itself is the unit, not an open
prediction: a continuous scale cannot be the unique minimum of a scale-invariant cost
(`PersistenceMechanics.SelectionSymmetry.scale_no_unique_min`), so it is an anchor by proof.

The values below only turn those pure numbers into MeV, eV, fm, Å and seconds for comparison
with measurement. They are the single source for these conversions; other modules refer here.

* `electronMassMeV`, `electronMassEV`, `electronMassGeV`: CODATA 2022, `0.51099895069(16)` MeV.
* `hbarcMeVFm`, `hbarcEVAngstrom`: `ħc`, exact in the SI (`h`, `c`, `e` fixed), 19 digits kept.
* `cFmPerSecond`: `c`, exact in the SI.
* `*_eq`: the unit forms agree.

`ElectroweakBounds.electronGeV`, `FloorNeutrino.meEV` and `StrongRunning.mZ` were on CODATA 2018
(`0.51099895000` MeV) and now point here; the VEV window moved from `(246.2196378, 246.2196379)`
to `(246.2196381, 246.2196382)` GeV and the Higgs window to `(125.2692638, 125.2692640)` GeV.
-/

noncomputable section
namespace PMSubstrate.SIUnits

/-- Electron rest energy in MeV (CODATA 2022). -/
def electronMassMeV : ℝ := 0.51099895069
/-- Electron rest energy in eV (CODATA 2022). -/
def electronMassEV : ℝ := 510998.95069
/-- Electron rest energy in GeV (CODATA 2022). -/
def electronMassGeV : ℝ := 0.00051099895069

/-- `ħc` in MeV·fm (exact in the SI; 19 digits). -/
def hbarcMeVFm : ℝ := 197.3269804593024659
/-- `ħc` in eV·Å (exact in the SI; 19 digits). -/
def hbarcEVAngstrom : ℝ := 1973.269804593024659

/-- `c` in fm/s (exact in the SI). -/
def cFmPerSecond : ℝ := 2.99792458e23

theorem electronMassEV_eq : electronMassEV = electronMassMeV * 10 ^ 6 := by
  norm_num [electronMassEV, electronMassMeV]

theorem electronMassGeV_eq : electronMassGeV = electronMassMeV / 1000 := by
  norm_num [electronMassGeV, electronMassMeV]

theorem hbarcEVAngstrom_eq : hbarcEVAngstrom = 10 * hbarcMeVFm := by
  norm_num [hbarcEVAngstrom, hbarcMeVFm]

end PMSubstrate.SIUnits
