import PMAtoms.CollectiveE8
import PMAtoms.Invariants
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Finite alpha channel

The alpha exit uses the same finite-channel form as beta:

```
rate = attempt · P · F · exp(−B)
```

with the E8 daughter-shell preformation `P`, closure hindrance `F`, and
Geiger–Nuttall barrier `B`.  The attempt frequency cancels in relative
lifetimes; its absolute E8 value is still open.
-/

noncomputable section
namespace PMAtoms

/-- Finite alpha channel rate for a supplied attempt frequency. -/
noncomputable def alphaFiniteRate (attempt : ℝ) (p : Nuclide) : ℝ :=
  attempt * alphaWidthE8 1 p

theorem alphaFiniteRate_eq (attempt : ℝ) (p : Nuclide) :
    alphaFiniteRate attempt p = attempt * alphaWidthE8 1 p := rfl

theorem alphaFiniteRate_pos (attempt : ℝ) (p : Nuclide) (h : 0 < attempt) :
    0 < alphaFiniteRate attempt p := by
  unfold alphaFiniteRate
  exact mul_pos h (alphaWidthE8_pos 1 p (by norm_num))

/-- Finite alpha mean life. -/
noncomputable def alphaFiniteLifetime (attempt : ℝ) (p : Nuclide) : ℝ :=
  MeanLife (alphaFiniteRate attempt p)

theorem alphaFiniteLifetime_eq (attempt : ℝ) (p : Nuclide) :
    alphaFiniteLifetime attempt p = 1 / alphaFiniteRate attempt p := rfl

theorem alphaFiniteLifetime_pos (attempt : ℝ) (p : Nuclide) (h : 0 < attempt) :
    0 < alphaFiniteLifetime attempt p :=
  MeanLife_pos (alphaFiniteRate_pos attempt p h)

/-- Representative alpha emitters. -/
def u238 : Nuclide := ⟨92, 146⟩
def cm244 : Nuclide := ⟨96, 148⟩
def cf252 : Nuclide := ⟨98, 154⟩


/-- The finite alpha width written as phase space times the full barrier. -/
theorem alphaWidthE8_eq_phase_barrier (p : Nuclide) :
    alphaWidthE8 1 p =
      alphaPhaseSpace p * Real.exp (-(alphaBarrierShellPreformed p)) := by
  unfold alphaWidthE8 alphaPhaseSpace alphaPreformationShell
    alphaBarrierShellPreformed
  rw [show -(alphaBarrierGeiger p.Z (alphaQ p) +
      (σ : ℝ) / 2 * daughterShellDistance p) =
      (-(σ : ℝ) / 2 * daughterShellDistance p) +
        (-(alphaBarrierGeiger p.Z (alphaQ p))) by ring]
  rw [Real.exp_add]
  ring_nf

/-- Relative finite alpha lifetime: the attempt frequency cancels. -/
theorem alphaFiniteLifetime_ratio (attempt : ℝ) (p ref : Nuclide)
    (h : attempt ≠ 0) :
    alphaFiniteLifetime attempt p / alphaFiniteLifetime attempt ref =
      alphaRelativeLifetimeE8 p ref := by
  unfold alphaFiniteLifetime alphaFiniteRate alphaRelativeLifetimeE8 MeanLife
  rw [alphaWidthE8_eq_phase_barrier p, alphaWidthE8_eq_phase_barrier ref]
  have hFp : alphaPhaseSpace p ≠ 0 := ne_of_gt (alphaPhaseSpace_pos p)
  have hFr : alphaPhaseSpace ref ≠ 0 := ne_of_gt (alphaPhaseSpace_pos ref)
  have hBp : Real.exp (-(alphaBarrierShellPreformed p)) ≠ 0 := Real.exp_ne_zero _
  have hBr : Real.exp (-(alphaBarrierShellPreformed ref)) ≠ 0 := Real.exp_ne_zero _
  field_simp [h, hFp, hFr, hBp, hBr]
  rw [← Real.exp_add]
  ring_nf

/-- Alpha structural workload: the alpha capacity `min(Z,N)/2`. -/
def alphaWorkload (p : Nuclide) : ℝ :=
  alphaCapacity p.Z p.N

theorem alphaWorkload_pos {p : Nuclide} (hZ : 0 < p.Z) (hN : 0 < p.N) :
    0 < alphaWorkload p := by
  unfold alphaWorkload alphaCapacity
  have hmin : 0 < min p.Z p.N := Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_min hZ hN)
  positivity

/-- E8 clock flux in inverse `m_e` units. -/
def alphaFlux : ℝ :=
  1 / (PMSubstrate.E8Values.Delta : ℝ)

theorem alphaFlux_eq : alphaFlux = 1 / 43 := by
  unfold alphaFlux
  norm_num [PMSubstrate.E8Values.Delta, PMSubstrate.baseline]

theorem alphaFlux_pos : 0 < alphaFlux := by
  rw [alphaFlux_eq]; norm_num

/-- `cKf` alpha attempt rate with unit toll. -/
def alphaAttempt (p : Nuclide) : ℝ :=
  alphaWorkload p * alphaFlux

theorem alphaAttempt_pos {p : Nuclide} (hZ : 0 < p.Z) (hN : 0 < p.N) :
    0 < alphaAttempt p :=
  mul_pos (alphaWorkload_pos hZ hN) alphaFlux_pos

/-- Alpha rate from the E8 `cKf` ledger. -/
noncomputable def alphaFiniteRateE8 (p : Nuclide) : ℝ :=
  alphaFiniteRate (alphaAttempt p) p

theorem alphaFiniteRateE8_pos {p : Nuclide} (hZ : 0 < p.Z) (hN : 0 < p.N) :
    0 < alphaFiniteRateE8 p :=
  alphaFiniteRate_pos (alphaAttempt p) p (alphaAttempt_pos hZ hN)

/-- Alpha lifetime from the E8 `cKf` ledger. -/
noncomputable def alphaFiniteLifetimeE8 (p : Nuclide) : ℝ :=
  alphaFiniteLifetime (alphaAttempt p) p

theorem alphaFiniteLifetimeE8_pos {p : Nuclide} (hZ : 0 < p.Z) (hN : 0 < p.N) :
    0 < alphaFiniteLifetimeE8 p :=
  alphaFiniteLifetime_pos (alphaAttempt p) p (alphaAttempt_pos hZ hN)

/-- Leading E8 collective cost scale `Δ²/(ν+σ)`. -/
def alphaCostScale : ℝ :=
  ((Δ : ℝ) ^ 2) / (((ν + σ : Nat)) : ℝ)

theorem alphaCostScale_eq : alphaCostScale = 1849 / 21 := by
  unfold alphaCostScale
  norm_num [Δ, ν, σ, PMSubstrate.baseline]

theorem alphaCostScale_pos : 0 < alphaCostScale := by
  rw [alphaCostScale_eq]; norm_num

/-- Leading E8 activation weight. -/
noncomputable def alphaActivation : ℝ :=
  Real.exp (-alphaCostScale)

theorem alphaActivation_pos : 0 < alphaActivation := by
  unfold alphaActivation
  positivity

/-- Leading-cost alpha rate (no Q-dependent term yet). -/
noncomputable def alphaRateScale (p : Nuclide) : ℝ :=
  alphaAttempt p * alphaActivation

theorem alphaRateScale_pos {p : Nuclide} (hZ : 0 < p.Z) (hN : 0 < p.N) :
    0 < alphaRateScale p :=
  mul_pos (alphaAttempt_pos hZ hN) alphaActivation_pos

/-- Lifetime from the leading E8 cost scale. -/
noncomputable def alphaLifetimeScale (p : Nuclide) : ℝ :=
  1 / alphaRateScale p

theorem alphaLifetimeScale_eq (p : Nuclide) :
    alphaLifetimeScale p = 1 / alphaRateScale p := rfl

/-- Q-dependent E8 collective cost:
`(Δ/(σ+χ))·Z/√Q − (Δ/2)·σ`. -/
noncomputable def alphaCostQ (p : Nuclide) : ℝ :=
  ((Δ : ℝ) / (((σ + χ : Nat)) : ℝ)) * (p.Z : ℝ) /
      Real.sqrt (alphaQ p) -
    ((Δ : ℝ) / 2) * (σ : ℝ)

theorem alphaCostQ_eq (p : Nuclide) :
    alphaCostQ p =
      (43 / 7 : ℝ) * (p.Z : ℝ) / Real.sqrt (alphaQ p) -
        (43 / 2 : ℝ) * 5 := by
  unfold alphaCostQ
  norm_num [Δ, σ, χ, PMSubstrate.baseline]

/-- Q-dependent activation weight. -/
noncomputable def alphaActivationQ (p : Nuclide) : ℝ :=
  Real.exp (-(alphaCostQ p))

theorem alphaActivationQ_pos (p : Nuclide) : 0 < alphaActivationQ p := by
  unfold alphaActivationQ
  positivity

/-- Q-dependent alpha rate. -/
noncomputable def alphaRateQ (p : Nuclide) : ℝ :=
  alphaAttempt p * alphaActivationQ p

theorem alphaRateQ_pos {p : Nuclide} (hZ : 0 < p.Z) (hN : 0 < p.N) :
    0 < alphaRateQ p :=
  mul_pos (alphaAttempt_pos hZ hN) (alphaActivationQ_pos p)

/-- Q-dependent alpha lifetime. -/
noncomputable def alphaLifetimeQ (p : Nuclide) : ℝ :=
  1 / alphaRateQ p

/-- Improved E8 Q-dependent cost:
`(Δ/(D+2χ))·Z/√Q − (2Δ−χ)` = `(43/8)·Z/√Q − 84`. -/
noncomputable def alphaCostQ2 (p : Nuclide) : ℝ :=
  ((Δ : ℝ) / (((D + 2 * χ : Nat)) : ℝ)) * (p.Z : ℝ) /
      Real.sqrt (alphaQ p) -
    (((2 * Δ - χ : Nat)) : ℝ)

theorem alphaCostQ2_eq (p : Nuclide) :
    alphaCostQ2 p =
      (43 / 8 : ℝ) * (p.Z : ℝ) / Real.sqrt (alphaQ p) - 84 := by
  unfold alphaCostQ2
  norm_num [Δ, D, χ, PMSubstrate.baseline]

noncomputable def alphaActivationQ2 (p : Nuclide) : ℝ :=
  Real.exp (-(alphaCostQ2 p))

theorem alphaActivationQ2_pos (p : Nuclide) : 0 < alphaActivationQ2 p := by
  unfold alphaActivationQ2
  positivity

noncomputable def alphaRateQ2 (p : Nuclide) : ℝ :=
  alphaAttempt p * alphaActivationQ2 p

theorem alphaRateQ2_pos {p : Nuclide} (hZ : 0 < p.Z) (hN : 0 < p.N) :
    0 < alphaRateQ2 p :=
  mul_pos (alphaAttempt_pos hZ hN) (alphaActivationQ2_pos p)

noncomputable def alphaLifetimeQ2 (p : Nuclide) : ℝ :=
  1 / alphaRateQ2 p

end PMAtoms
