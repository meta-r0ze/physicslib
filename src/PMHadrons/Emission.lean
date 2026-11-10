import PMHadrons.TollGovernor
import PMHadrons.BoundStateOverlap
import PMHadrons.CompositeStates
import PMElementaryParticles.SubstrateTransition
import Mathlib.Tactic

/-!

# The composite emission overlap and width

A composite's decay is a **boundary transition** (`TollGovernor`): it sheds a carrier through its
boundary. The rate factorises into the three pieces the framework already names:

```
Γ = (Toll boundary weight) × |composite–carrier overlap|² × phase space .
```

* the **Toll boundary weight** is `TollGovernor.emissionWeight = tollTerm` — the probability that
  the boundary transition persists (`χ` orientations, non-aliasing target);
* the **overlap** is the composite's configuration against the outgoing single carrier
  (`BoundStateOverlap.overlap`); this is the object the Standard-Model comparison calls the decay
  constant `fπ`/`fK`;
* the **phase space** is the two-body factor (`CompositePhaseSpace`).

`emissionWidth_eq_partialWidth` writes `Γ` in the general `SubstrateTransition` form
`|T|²·phaseSpace` with `T = √emissionWeight · overlap`, so the composite decay is an instance of
the generic rate. The absolute `fπ` needs the composite's configuration (the overlap value) — the
remaining open piece of item 2.
-/

namespace PMHadrons.Emission

open PMHadrons.BoundStateOverlap

/-- The composite–carrier emission overlap: the composite's configuration against the outgoing
single carrier. The SM comparison reads the overlap as the decay constant `fπ`/`fK`. -/
def emissionOverlap {ι : Type*} [Fintype ι] (ψ φ : Wavefunction ι) : ℂ :=
  overlap ψ φ

/-- The composite's emission width: the Toll boundary weight times the overlap-squared times the
phase space. -/
noncomputable def emissionWidth {ι : Type*} [Fintype ι] (ψ φ : Wavefunction ι)
    (phase : ℝ) : ℝ :=
  PMHadrons.TollGovernor.emissionWeight * Complex.normSq (emissionOverlap ψ φ) * phase

theorem emissionWidth_eq {ι : Type*} [Fintype ι] (ψ φ : Wavefunction ι) (phase : ℝ) :
    emissionWidth ψ φ phase =
      PMHadrons.TollGovernor.emissionWeight * Complex.normSq (overlap ψ φ) * phase := rfl

theorem emissionWidth_nonneg {ι : Type*} [Fintype ι] (ψ φ : Wavefunction ι) {phase : ℝ}
    (hphase : 0 ≤ phase) : 0 ≤ emissionWidth ψ φ phase := by
  unfold emissionWidth emissionOverlap
  exact mul_nonneg
    (mul_nonneg PMHadrons.TollGovernor.emissionWeight_pos.le (Complex.normSq_nonneg _)) hphase

/-- **The composite decay is the general rate form.** `Γ = |T|²·phaseSpace` with the operator
`T = √emissionWeight · overlap` (`SubstrateTransition.partialWidth`). -/
theorem emissionWidth_eq_partialWidth {ι : Type*} [Fintype ι] (ψ φ : Wavefunction ι) (phase : ℝ) :
    emissionWidth ψ φ phase =
      Complex.normSq ((Real.sqrt PMHadrons.TollGovernor.emissionWeight : ℂ) * emissionOverlap ψ φ) *
        phase := by
  unfold emissionWidth
  rw [Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt PMHadrons.TollGovernor.emissionWeight_pos.le]

end PMHadrons.Emission
