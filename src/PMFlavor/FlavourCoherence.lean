import PMFlavor.ChordBranch
import PersistenceMechanics.CoherentAction

/-! **Experimental/candidate module.**

# Flavour coherence

The chord-branch condition is a phase-coherence condition:

```
phaseDrift e t = t · (e₂ − e₀)
coherentBranch e t ↔ phaseDrift e t ≤ π
```

The substrate clock `Δ = 43` lies inside the coherence window when the energy
spread is at most `π/43`.  Per-step restoration is the stronger condition that
the phase step is a full `2π` multiple.
-/

noncomputable section
namespace PMFlavor.FlavourCoherence

open PMFlavor.ChordBranch

/-- Phase drift over a tick. -/
def phaseDrift (e : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  t * (e 2 - e 0)

/-- Coherent branch: phase drift stays within one half-turn. -/
def coherentBranch (e : Fin 3 → ℝ) (t : ℝ) : Prop :=
  phaseDrift e t ≤ Real.pi

theorem coherentBranch_iff_tStar (e : Fin 3 → ℝ) (t : ℝ)
    (ht : 0 < t) (h02 : e 0 < e 2) :
    coherentBranch e t ↔ t ≤ tStar e := by
  unfold coherentBranch phaseDrift
  exact branch_iff_tick_le e t ht h02

/-- The substrate clock is coherent when the spread is at most `π/43`. -/
theorem oneTickCoherent (e : Fin 3 → ℝ) (h02 : e 0 < e 2)
    (hspread : e 2 - e 0 ≤ Real.pi / clock) :
    coherentBranch e clock := by
  unfold coherentBranch phaseDrift
  exact substrate_branch_condition e h02 hspread

/-- Exact per-step restoration: the phase step is a full `2π` multiple. -/
def perStepRestores (phaseStep : ℝ) : Prop :=
  ∃ n : ℤ, phaseStep = 2 * Real.pi * (n : ℝ)

theorem zero_restores : perStepRestores 0 :=
  ⟨0, by norm_num⟩

/-- A phase-preserving update has unit modulus. -/
theorem phaseWeight_unit (phase : ℝ) :
    Complex.normSq (PersistenceMechanics.CoherentAction.phaseWeight phase) = 1 :=
  PersistenceMechanics.CoherentAction.phaseWeight_normSq phase

end PMFlavor.FlavourCoherence
