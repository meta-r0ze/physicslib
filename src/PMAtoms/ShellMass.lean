import PMAtoms.ShellSystem
import PMAtoms.NuclearLedger
import Mathlib.Tactic

/-!
# The shell correction in the nuclear mass

`certifiedMass` (`NuclearLedger`) is the **smooth** E8 nuclear ledger.  The single-particle shell
system (`ShellSystem`) contributes a correction.  This module wires them so the shell structure is
part of the mass and any change to the shell spectrum or its E8 scale propagates:

`certifiedMassFull = certifiedMass + shellMassCorrection`,

where the correction is the Strutinsky term of the proton and neutron spectra in the E8 unit
`ℏω = χ·m_p/Δ` (`shellEnergyUnit`).  `certifiedMass` is the smooth truncation.

The mass term is a `ℝ` expression; `shellMassCorrection_mem` gives its rational enclosure (for a
printer such as `e8p`).

**Scale.** This module still multiplies by the one-cell unit `shellEnergyUnit`; the nucleus
quantum is `ShellSystem.shellQuantum (z+n)` (`= shellEnergyUnit / A^{1/3}`). Switch when the
smooth reference is rebuilt; the rational enclosure then needs an `A^{1/3}` bound
(`CertifiedNumerics.cbrt`).

**Comparison (`REVIEW-AND-NEXT.md` §1).** With either E8 level scheme the shell term is 3–4×
the `certifiedMass` residual and uncorrelated with it. The E8 ledger is not a liquid drop plus a
shell correction; its smooth part already carries that structure. So `certifiedMassFull` is kept
as the dependency edge for the comparison, not as a published mass.

**Placeholder.**  `SingleParticle.strutinskyCorrection` is *crude*: for a uniform spectrum
`e_i = i` it gives `cum(n) − smooth(n) = −n²/2`, i.e. a drifting trend, not a zero-mean shell
correction.  So `certifiedMassFull` is a **placeholder** — the dependency edge is correct (a
change to the shell spectrum or its E8 scale propagates here), but the shell term needs a proper
(zero-mean, curvature-corrected) Strutinsky before its value can be published.
-/

noncomputable section
namespace PMAtoms

/-- The E8 shell mass correction (m_e): the Strutinsky correction of the proton and neutron
single-particle spectra, in the E8 unit `ℏω = χ·m_p/Δ`. -/
noncomputable def shellMassCorrection (z n w : Nat) : ℝ :=
  shellEnergyUnit *
    (shellStrutinskyCorrection nuclearOrbitals184 z w +
      shellStrutinskyCorrection nuclearOrbitals184 n w)

/-- **The full E8 nuclear mass**: the smooth certified ledger plus the shell correction. -/
noncomputable def certifiedMassFull (z n w : Nat) : ℝ :=
  certifiedMass z n + shellMassCorrection z n w

theorem shellMassCorrection_eq (z n w : Nat) :
    shellMassCorrection z n w =
      shellEnergyUnit * (shellStrutinskyCorrection nuclearOrbitals184 z w +
        shellStrutinskyCorrection nuclearOrbitals184 n w) := rfl

theorem certifiedMassFull_eq (z n w : Nat) :
    certifiedMassFull z n w = certifiedMass z n + shellMassCorrection z n w := rfl

/-- **The smooth ledger is the truncation** of the full mass at zero shell correction. -/
theorem certifiedMassFull_eq_smooth (z n w : Nat) (h : shellMassCorrection z n w = 0) :
    certifiedMassFull z n w = certifiedMass z n := by
  rw [certifiedMassFull_eq, h, add_zero]

/-- The shell correction is linear in the E8 scale `ℏω` — so deriving the scale propagates. -/
theorem shellMassCorrection_eq_unit (z n w : Nat) (c : ℝ) (h : shellEnergyUnit = c) :
    shellMassCorrection z n w =
      c * (shellStrutinskyCorrection nuclearOrbitals184 z w +
        shellStrutinskyCorrection nuclearOrbitals184 n w) := by
  rw [shellMassCorrection_eq, h]

/-! ## Rational shell shape (for a printer)

The orbital energies are rational, so the Strutinsky shape is a `ℚ` — the scale `ℏω` carries the
only `ℝ` content, and its enclosure (`proton = E8`) gives a rational enclosure of
`certifiedMassFull`. -/

/-- `ℚ` orbital energy (mirror of `SingleParticle.orbitalEnergy`). -/
def orbitalEnergyQ (o : NuclearOrbital) : ℚ :=
  (o.n : ℚ) + (o.l : ℚ) / 10 - (o.j2 : ℚ) / 20

theorem orbitalEnergy_eq_Q (o : NuclearOrbital) : orbitalEnergy o = (orbitalEnergyQ o : ℝ) := by
  unfold orbitalEnergy orbitalEnergyQ; push_cast; ring

def orbitalLevelsQ (xs : List NuclearOrbital) : List ℚ :=
  xs.flatMap (fun o => List.replicate o.occupation (orbitalEnergyQ o))

theorem orbitalLevels_eq_Q (xs : List NuclearOrbital) :
    orbitalLevels xs = (orbitalLevelsQ xs).map (Rat.cast) := by
  unfold orbitalLevels orbitalLevelsQ
  induction xs with
  | nil => rfl
  | cons o rest ih =>
    simp only [List.flatMap_cons, List.map_append]
    rw [ih]
    congr 1
    rw [orbitalEnergy_eq_Q]
    clear ih
    induction o.occupation with
    | zero => rfl
    | succ k ihk => rw [List.replicate_succ, List.replicate_succ, List.map_cons, ihk]

def cumulativeEnergyQ (xs : List NuclearOrbital) (N : Nat) : ℚ :=
  ((orbitalLevelsQ xs).take N).sum

def smoothEnergyQ (xs : List NuclearOrbital) (N w : Nat) : ℚ :=
  if w = 0 then 0
  else (N : ℚ) * ((cumulativeEnergyQ xs (N + w) -
    (if w ≤ N then cumulativeEnergyQ xs (N - w) else 0)) / (2 * (w : ℚ)))

def shellStrutinskyQ (xs : List NuclearOrbital) (N w : Nat) : ℚ :=
  cumulativeEnergyQ xs N - smoothEnergyQ xs N w

theorem cumulativeEnergy_eq_Q (xs : List NuclearOrbital) (N : Nat) :
    cumulativeEnergy xs N = (cumulativeEnergyQ xs N : ℝ) := by
  unfold cumulativeEnergy cumulativeEnergyQ
  rw [orbitalLevels_eq_Q, ← List.map_take]
  have hsum : ∀ l : List ℚ, (l.map (Rat.cast)).sum = ((l.sum : ℚ) : ℝ) := by
    intro l; induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, Rat.cast_add]
  exact hsum _

theorem smoothEnergy_eq_Q (xs : List NuclearOrbital) (N w : Nat) :
    smoothEnergy xs N w = (smoothEnergyQ xs N w : ℝ) := by
  unfold smoothEnergy smoothEnergyQ
  by_cases hw : w = 0
  · simp [hw]
  · simp only [hw, ite_false]
    rw [cumulativeEnergy_eq_Q, cumulativeEnergy_eq_Q]
    by_cases hle : w ≤ N
    · simp only [hle, ite_true]; push_cast; ring
    · simp only [hle, ite_false]; push_cast; ring

theorem shellStrutinsky_eq_Q (xs : List NuclearOrbital) (N w : Nat) :
    shellStrutinskyCorrection xs N w = (shellStrutinskyQ xs N w : ℝ) := by
  unfold shellStrutinskyCorrection strutinskyCorrection shellStrutinskyQ
  rw [cumulativeEnergy_eq_Q, smoothEnergy_eq_Q]
  push_cast; ring

/-- **The shell mass correction is the E8 scale times a rational shape.** -/
theorem shellMassCorrection_eq_Q (z n w : Nat) :
    shellMassCorrection z n w =
      shellEnergyUnit *
        ((shellStrutinskyQ nuclearOrbitals184 z w +
          shellStrutinskyQ nuclearOrbitals184 n w : ℚ) : ℝ) := by
  unfold shellMassCorrection
  rw [shellStrutinsky_eq_Q, shellStrutinsky_eq_Q]
  push_cast
  ring

/-- The rational shell shape `S(z,n,w)` — the Strutinsky sum. -/
def shellShapeQ (z n w : Nat) : ℚ :=
  shellStrutinskyQ nuclearOrbitals184 z w + shellStrutinskyQ nuclearOrbitals184 n w

theorem shellMassCorrection_eq_shapeQ (z n w : Nat) :
    shellMassCorrection z n w = shellEnergyUnit * (shellShapeQ z n w : ℝ) := by
  simpa [shellShapeQ] using shellMassCorrection_eq_Q z n w

/-- Rational enclosure of the E8 scale `ℏω = proton·χ/Δ`. -/
def shellUnitLo : ℚ := (1836152673444 / 10 ^ 9) * 2 / 43
def shellUnitHi : ℚ := (1836152673445 / 10 ^ 9) * 2 / 43

theorem shellEnergyUnit_mem :
    (shellUnitLo : ℝ) ≤ shellEnergyUnit ∧ shellEnergyUnit ≤ (shellUnitHi : ℝ) := by
  have hp := PMHadrons.CompositeMasses.proton_value
  have hL : (shellUnitLo : ℝ) = (1836.152673444 : ℝ) * (2 / 43) := by norm_num [shellUnitLo]
  have hH : (shellUnitHi : ℝ) = (1836.152673445 : ℝ) * (2 / 43) := by norm_num [shellUnitHi]
  rw [shellEnergyUnit_eq, hL, hH]
  constructor <;> nlinarith [hp.1, hp.2]

def shellMassLo (z n w : Nat) : ℚ :=
  min (shellUnitLo * shellShapeQ z n w) (shellUnitHi * shellShapeQ z n w)
def shellMassHi (z n w : Nat) : ℚ :=
  max (shellUnitLo * shellShapeQ z n w) (shellUnitHi * shellShapeQ z n w)

/-- **Rational enclosure of the shell mass correction.** -/
theorem shellMassCorrection_mem (z n w : Nat) :
    (shellMassLo z n w : ℝ) ≤ shellMassCorrection z n w ∧
    shellMassCorrection z n w ≤ (shellMassHi z n w : ℝ) := by
  have hu := shellEnergyUnit_mem
  have hLo : (shellMassLo z n w : ℝ) =
      min ((shellUnitLo : ℝ) * (shellShapeQ z n w : ℝ)) ((shellUnitHi : ℝ) * (shellShapeQ z n w : ℝ)) := by
    unfold shellMassLo; push_cast; ring
  have hHi : (shellMassHi z n w : ℝ) =
      max ((shellUnitLo : ℝ) * (shellShapeQ z n w : ℝ)) ((shellUnitHi : ℝ) * (shellShapeQ z n w : ℝ)) := by
    unfold shellMassHi; push_cast; ring
  rw [shellMassCorrection_eq_shapeQ, hLo, hHi]
  have huLH : (shellUnitLo : ℝ) ≤ (shellUnitHi : ℝ) := le_trans hu.1 hu.2
  rcases le_total 0 (shellShapeQ z n w : ℝ) with hs | hs
  · rw [min_eq_left (mul_le_mul_of_nonneg_right huLH hs),
        max_eq_right (mul_le_mul_of_nonneg_right huLH hs)]
    exact ⟨mul_le_mul_of_nonneg_right hu.1 hs, mul_le_mul_of_nonneg_right hu.2 hs⟩
  · rw [min_eq_right (mul_le_mul_of_nonpos_right huLH hs),
        max_eq_left (mul_le_mul_of_nonpos_right huLH hs)]
    exact ⟨mul_le_mul_of_nonpos_right hu.2 hs, mul_le_mul_of_nonpos_right hu.1 hs⟩

end PMAtoms
