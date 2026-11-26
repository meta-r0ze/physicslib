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
abbrev electronMassMeVRat : ℚ := 51099895069 / 10^11

/-- Electron mass in atomic mass units (CODATA 2022). -/
def electronMassU : ℚ := 548579909065 / 10^15

-- Materialize the rational sources as real numerals. Arithmetic tactics can
-- then use the coefficients without a separate rational-cast rewrite.
def electronMassMeV : ℝ :=
  OfScientific.ofScientific
    (eval% electronMassMeVRat.num.natAbs) true (eval% Nat.log 10 electronMassMeVRat.den)

def electronMassEV : ℝ :=
  OfScientific.ofScientific
    (eval% electronMassMeVRat.num.natAbs) true (eval% Nat.log 10 electronMassMeVRat.den - 6)

def electronMassGeV : ℝ :=
  OfScientific.ofScientific
    (eval% electronMassMeVRat.num.natAbs) true (eval% Nat.log 10 electronMassMeVRat.den + 3)

/-- The retained SI precision for ħc in MeV·fm. -/
abbrev hbarcMeVFmRat : ℚ := 1973269804593024659 / 10^16

def hbarcMeVFm : ℝ :=
  OfScientific.ofScientific
    (eval% hbarcMeVFmRat.num.natAbs) true (eval% Nat.log 10 hbarcMeVFmRat.den)

def hbarcEVAngstrom : ℝ :=
  OfScientific.ofScientific
    (eval% hbarcMeVFmRat.num.natAbs) true (eval% Nat.log 10 hbarcMeVFmRat.den - 1)

/-- Exact speed of light in fm/s. -/
abbrev cFmPerSecondRat : ℚ := 299792458 * 10 ^ 15

def cFmPerSecond : ℝ :=
  (eval% cFmPerSecondRat.num.natAbs : ℕ)

theorem electronMassMeVRat_cast : (electronMassMeVRat : ℝ) = electronMassMeV := by
  norm_num [electronMassMeVRat, electronMassMeV]

theorem hbarcMeVFmRat_cast : (hbarcMeVFmRat : ℝ) = hbarcMeVFm := by
  norm_num [hbarcMeVFmRat, hbarcMeVFm]

theorem cFmPerSecondRat_cast : (cFmPerSecondRat : ℝ) = cFmPerSecond := by
  norm_num [cFmPerSecondRat, cFmPerSecond]

theorem electronMassEV_eq : electronMassEV = electronMassMeV * 10 ^ 6 := by
  norm_num [electronMassEV, electronMassMeV]

theorem electronMassGeV_eq : electronMassGeV = electronMassMeV / 1000 := by
  norm_num [electronMassGeV, electronMassMeV]

theorem hbarcEVAngstrom_eq : hbarcEVAngstrom = 10 * hbarcMeVFm := by
  norm_num [hbarcEVAngstrom, hbarcMeVFm]

end PMSubstrate.SIUnits
