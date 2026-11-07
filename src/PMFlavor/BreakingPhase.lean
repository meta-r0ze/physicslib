import PMFlavor.BreakingLink
import PersistenceMechanics.CoherentAction
import PMFlavor.MixingMatrix

/-! **Experimental/candidate module.**

# Broken-link phase and cost

The broken-link parameters are interpreted as:

```
δ = phase mismatch of the wall link
ε = attenuation/cost of the wall link
```

The amplitude is `exp(iδ − (β/2)ε)`.  Numerical values of `δ, ε` remain physical
wall inputs.
-/

noncomputable section
namespace PMFlavor.BreakingWall

open PMFlavor.BreakingLink
open PersistenceMechanics.CoherentAction

structure BreakingPhase where
  delta : ℝ
  epsilon : ℝ

/-- Broken link from the phase mismatch. -/
def brokenLinkOfPhase (w : BreakingPhase) : Matrix (Fin 3) (Fin 3) ℂ :=
  brokenLink w.delta

/-- Coherent/incoherent wall amplitude. -/
def wallAmplitude (β : ℝ) (w : BreakingPhase) : ℂ :=
  combinedWeight w.delta β w.epsilon


/-- The exceptional mixing curve in phase/cost variables. -/
def ExceptionalWall (w : BreakingPhase) : Prop :=
  w.delta = PMFlavor.MixingMatrix.rootMInv
    (5 - PMFlavor.MixingMatrix.rootM w.epsilon)

/-- The physical wall point must lie off the exceptional curve. -/
def PhysicalWallInput (w : BreakingPhase) : Prop := ¬ ExceptionalWall w

/-- For `0 < ε < 2`, the lower eigenvalue is between `1` and `2`. -/
theorem rootM_between {ε : ℝ} (h0 : 0 < ε) (h2 : ε < 2) :
    1 < PMFlavor.MixingMatrix.rootM ε ∧ PMFlavor.MixingMatrix.rootM ε < 2 := by
  have hs : 0 ≤ (ε - 1) ^ 2 + 8 := by positivity
  have hspos : 0 < Real.sqrt ((ε - 1) ^ 2 + 8) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · unfold PMFlavor.MixingMatrix.rootM
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.sq_sqrt hs]
  · unfold PMFlavor.MixingMatrix.rootM
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.sq_sqrt hs]

/-- For `3 < y < 4`, the inverse exceptional value is negative. -/
theorem rootMInv_neg {y : ℝ} (h3 : 3 < y) (h4 : y < 4) :
    PMFlavor.MixingMatrix.rootMInv y < 0 := by
  unfold PMFlavor.MixingMatrix.rootMInv
  have hden : 3 - y < 0 := by linarith
  have hnum : 0 < (y - 1) * (4 - y) := by
    apply mul_pos <;> linarith
  exact div_neg_of_pos_of_neg hnum hden

/-- A physical wall point with positive phase mismatch and cost below `χ=2`
lies off the exceptional mixing curve. -/
theorem positive_delta_off_exceptional {δ ε : ℝ}
    (hδ : 0 < δ) (hε0 : 0 < ε) (hε2 : ε < 2) :
    PhysicalWallInput ⟨δ, ε⟩ := by
  unfold PhysicalWallInput ExceptionalWall
  have hb := rootM_between hε0 hε2
  have hy3 : 3 < 5 - PMFlavor.MixingMatrix.rootM ε := by linarith
  have hy4 : 5 - PMFlavor.MixingMatrix.rootM ε < 4 := by linarith
  have hneg := rootMInv_neg hy3 hy4
  intro h
  linarith

/-- Physical wall range: positive phase mismatch, positive cost below `χ=2`. -/
def PhysicalWall (w : BreakingPhase) : Prop :=
  0 < w.delta ∧ 0 < w.epsilon ∧ w.epsilon < 2

theorem physicalWall_off_exceptional {w : BreakingPhase} (h : PhysicalWall w) :
    PhysicalWallInput w := by
  rcases w with ⟨δ, ε⟩
  exact positive_delta_off_exceptional h.1 h.2.1 h.2.2

end PMFlavor.BreakingWall
