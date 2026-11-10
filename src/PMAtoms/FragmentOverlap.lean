import PMHadrons.Emission
import PMAtoms.CollectiveRate
import Mathlib.Tactic

/-!

# The α / fission fragment overlap

An α decay (`nucleus → α + daughter`) and fission (`nucleus → fragments`) are composite →
fragment-cohort transitions. Their amplitude is a **fragment overlap** — the same object as the
hadron `PMHadrons.BoundStateOverlap` / `Emission`:

```
Γ = boundary × |overlap|² × phase space ,
```

where the boundary factor is the collective **barrier** (`PMAtoms.barrierRate barrier =
exp(−barrier)`; the α barrier is `CollectiveE8.alphaBarrier_eq = 43`, fission
`fissionBarrier_eq = 43/6`), and the overlap is the fragment configuration against the parent
nucleus.

This mirrors the hadron construction exactly, with the barrier playing the role of the Toll
boundary. What remains is the fragment configuration (the overlap value): on this side the
hindrance is currently *supplied* (`AlphaHindrance.alphaHindranceScale`,
`AlphaConfiguration` mixing, `CollectiveE8.fissionBarrier`), so computing the overlap replaces it.
-/

namespace PMAtoms.FragmentOverlap

open PMHadrons.BoundStateOverlap

/-- The α / fission fragment overlap: the fragment configuration against the parent nucleus. -/
def fragmentOverlap {ι : Type*} [Fintype ι] (parent fragments : Wavefunction ι) : ℂ :=
  overlap parent fragments

/-- The fragment partial width: the collective barrier weight times the overlap-squared times the
phase space — the same `|T|²·phaseSpace` form as `Emission.emissionWidth`. -/
noncomputable def fragmentWidth {ι : Type*} [Fintype ι] (parent fragments : Wavefunction ι)
    (barrier phase : ℝ) : ℝ :=
  PMAtoms.barrierRate barrier * Complex.normSq (fragmentOverlap parent fragments) * phase

theorem fragmentWidth_eq {ι : Type*} [Fintype ι] (parent fragments : Wavefunction ι)
    (barrier phase : ℝ) :
    fragmentWidth parent fragments barrier phase =
      PMAtoms.barrierRate barrier * Complex.normSq (overlap parent fragments) * phase := rfl

theorem fragmentWidth_nonneg {ι : Type*} [Fintype ι] (parent fragments : Wavefunction ι)
    {barrier phase : ℝ} (hphase : 0 ≤ phase) :
    0 ≤ fragmentWidth parent fragments barrier phase := by
  unfold fragmentWidth
  exact mul_nonneg
    (mul_nonneg (le_of_lt (PMAtoms.barrierRate_pos barrier)) (Complex.normSq_nonneg _)) hphase

/-- **The fragment decay is the general rate form.** `Γ = |T|²·phaseSpace` with the operator
`T = √barrierRate · overlap`. -/
theorem fragmentWidth_eq_partialWidth {ι : Type*} [Fintype ι] (parent fragments : Wavefunction ι)
    (barrier phase : ℝ) :
    fragmentWidth parent fragments barrier phase =
      Complex.normSq ((Real.sqrt (PMAtoms.barrierRate barrier) : ℂ) * fragmentOverlap parent fragments) *
        phase := by
  unfold fragmentWidth
  rw [Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (le_of_lt (PMAtoms.barrierRate_pos barrier))]

end PMAtoms.FragmentOverlap
