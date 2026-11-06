import PMAtoms.AlphaFinite
import PMAtoms.SingleParticle
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Spin-parity hindrance for alpha decay

The smooth E8 alpha cost misses a level-structure term.  This module records the
spin-parity input explicitly:

```
C_alpha = C_smooth + hindranceScale · (spin mismatch + parity change).
```

`hindranceScale` is supplied; it must be derived from the E8 level ladder before
this can be called a prediction.
-/

noncomputable section
namespace PMAtoms

/-- Nuclear spin and parity.  `spin2` is twice the spin. -/
structure AlphaLevel where
  spin2 : Nat
  parity : Bool
  deriving DecidableEq, Repr

/-- Absolute spin mismatch. -/
def AlphaLevel.spinMismatch (parent daughter : AlphaLevel) : Nat :=
  if parent.spin2 ≤ daughter.spin2 then daughter.spin2 - parent.spin2
  else parent.spin2 - daughter.spin2

/-- Parity change. -/
def AlphaLevel.parityChange (parent daughter : AlphaLevel) : Nat :=
  if parent.parity = daughter.parity then 0 else 1

/-- Supplied hindrance scale. -/
def alphaHindranceScale : ℝ := 1

/-- Spin-parity hindrance. -/
def alphaHindrance (parent daughter : AlphaLevel) : ℝ :=
  alphaHindranceScale *
    ((parent.spinMismatch daughter : Nat) + (parent.parityChange daughter : Nat) : ℝ)

/-- Smooth cost plus level hindrance. -/
noncomputable def alphaCostHindered (hindranceScale : ℝ)
    (parent daughter : AlphaLevel) (p : Nuclide) : ℝ :=
  alphaCostQ2 p + hindranceScale *
    ((parent.spinMismatch daughter : Nat) + (parent.parityChange daughter : Nat) : ℝ)

noncomputable def alphaActivationHindered (hindranceScale : ℝ)
    (parent daughter : AlphaLevel) (p : Nuclide) : ℝ :=
  Real.exp (-(alphaCostHindered hindranceScale parent daughter p))

theorem alphaActivationHindered_pos (hindranceScale : ℝ)
    (parent daughter : AlphaLevel) (p : Nuclide) :
    0 < alphaActivationHindered hindranceScale parent daughter p := by
  unfold alphaActivationHindered
  positivity

noncomputable def alphaRateHindered (hindranceScale : ℝ)
    (parent daughter : AlphaLevel) (p : Nuclide) : ℝ :=
  alphaAttempt p * alphaActivationHindered hindranceScale parent daughter p

theorem alphaRateHindered_pos (hindranceScale : ℝ)
    (parent daughter : AlphaLevel) (p : Nuclide)
    (hZ : 0 < p.Z) (hN : 0 < p.N) :
    0 < alphaRateHindered hindranceScale parent daughter p :=
  mul_pos (alphaAttempt_pos hZ hN)
    (alphaActivationHindered_pos hindranceScale parent daughter p)

noncomputable def alphaLifetimeHindered (hindranceScale : ℝ)
    (parent daughter : AlphaLevel) (p : Nuclide) : ℝ :=
  1 / alphaRateHindered hindranceScale parent daughter p

/-- Even-even ground-state transition. -/
def evenEvenLevel : AlphaLevel := ⟨0, true⟩

/-- Convert an E8 `nlj` orbital to a spin-parity level. -/
def AlphaLevel.ofOrbital (o : NuclearOrbital) : AlphaLevel :=
  ⟨o.j2, o.l % 2 = 0⟩

/-- Parity is positive for even `l`. -/
theorem AlphaLevel.ofOrbital_parity (o : NuclearOrbital) :
    (AlphaLevel.ofOrbital o).parity = (o.l % 2 = 0) := by simp [AlphaLevel.ofOrbital]

/-- Example even-even ground state. -/
theorem evenEvenLevel_spin : evenEvenLevel.spin2 = 0 := by simp [evenEvenLevel]
theorem evenEvenLevel_parity : evenEvenLevel.parity = true := by simp [evenEvenLevel]

/-- Actual spin-parity assignments for the odd-A diagnostics. -/
def u235Level : AlphaLevel := ⟨7, false⟩
def th231Level : AlphaLevel := ⟨5, true⟩
def pu239Level : AlphaLevel := ⟨1, true⟩
def u235DaughterLevel : AlphaLevel := ⟨7, false⟩

def u235Nuclide : Nuclide := ⟨92, 143⟩
def pu239Nuclide : Nuclide := ⟨94, 145⟩

theorem u235_hindrance_units (h : ℝ) :
    alphaCostHindered h u235Level th231Level u235Nuclide =
      alphaCostQ2 u235Nuclide + 3 * h := by
  unfold alphaCostHindered AlphaLevel.spinMismatch AlphaLevel.parityChange
  norm_num [u235Level, th231Level]
  ring

theorem pu239_hindrance_units (h : ℝ) :
    alphaCostHindered h pu239Level u235DaughterLevel pu239Nuclide =
      alphaCostQ2 pu239Nuclide + 7 * h := by
  unfold alphaCostHindered AlphaLevel.spinMismatch AlphaLevel.parityChange
  norm_num [pu239Level, u235DaughterLevel]
  ring

/-- Spin degeneracy `2J+1`. -/
def AlphaLevel.degeneracy (l : AlphaLevel) : Nat := l.spin2 + 1

/-- Log spin degeneracy of the parent/daughter pair. -/
noncomputable def spinDegeneracy (parent daughter : AlphaLevel) : ℝ :=
  Real.log (((parent.degeneracy * daughter.degeneracy : Nat)) : ℝ)

/-- Smooth cost plus a supplied spin-degeneracy coefficient. -/
noncomputable def alphaCostSpin (coefficient : ℝ)
    (parent daughter : AlphaLevel) (p : Nuclide) : ℝ :=
  alphaCostQ2 p + coefficient * spinDegeneracy parent daughter

theorem alphaCostSpin_evenEven (coefficient : ℝ) (p : Nuclide) :
    alphaCostSpin coefficient evenEvenLevel evenEvenLevel p = alphaCostQ2 p := by
  unfold alphaCostSpin spinDegeneracy AlphaLevel.degeneracy evenEvenLevel
  norm_num

/-- Number of unpaired valence nucleons. -/
def alphaBlockedNucleons (p : Nuclide) : Nat :=
  (p.Z % 2) + (p.N % 2)

/-- Open alpha capacity after removing unpaired nucleons. -/
def alphaOpenCapacity (p : Nuclide) : ℝ :=
  alphaCapacity p.Z p.N - (alphaBlockedNucleons p : ℝ)

/-- Blocking hindrance `log(capacity/open)`. -/
noncomputable def alphaBlockingHindrance (p : Nuclide) : ℝ :=
  if _h : 0 < alphaOpenCapacity p then
    Real.log (alphaCapacity p.Z p.N / alphaOpenCapacity p)
  else 0

theorem alphaBlockingHindrance_evenEven {p : Nuclide}
    (hZ : p.Z % 2 = 0) (hN : p.N % 2 = 0) :
    alphaBlockingHindrance p = 0 := by
  unfold alphaBlockingHindrance alphaOpenCapacity alphaBlockedNucleons
  rw [hZ, hN]
  norm_num

/-- Smooth cost plus blocking hindrance. -/
noncomputable def alphaCostBlocked (p : Nuclide) : ℝ :=
  alphaCostQ2 p + alphaBlockingHindrance p

/-- E8 orbital assignments for the odd-A diagnostics. -/
def u235ParentOrbital : NuclearOrbital := ⟨2, 3, 7, 8⟩
def th231DaughterOrbital : NuclearOrbital := ⟨2, 2, 5, 6⟩
def pu239ParentOrbital : NuclearOrbital := ⟨3, 0, 1, 2⟩
def u235DaughterOrbital : NuclearOrbital := ⟨2, 3, 7, 8⟩

theorem u235ParentOrbital_level :
    AlphaLevel.ofOrbital u235ParentOrbital = u235Level := by
  decide

theorem th231DaughterOrbital_level :
    AlphaLevel.ofOrbital th231DaughterOrbital = th231Level := by
  decide

theorem pu239ParentOrbital_level :
    AlphaLevel.ofOrbital pu239ParentOrbital = pu239Level := by
  decide

theorem u235DaughterOrbital_level :
    AlphaLevel.ofOrbital u235DaughterOrbital = u235DaughterLevel := by
  decide

end PMAtoms
