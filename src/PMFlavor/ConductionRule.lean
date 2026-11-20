import PMFlavor.HalfTurnAperture
import PMFlavor.TransferGraph
import PMFlavor.FlavourConstants
import PMFlavor.CKM

/-!
# One rule for the in-cycle transfer in both sectors

`TransferGraph`: the in-cycle transfer is boundary conduction. `HalfTurnAperture` (candidate, premises
there) gives each type-preserving channel the conductance `π/N` of the half-turn aperture:
`N = 14` for quarks, `10` for leptons (`in_cycle_quark`, `in_cycle_lepton`).

How a conductance becomes a mixing observable is the rule the node crossings already use:
* a quark coupling is the admittance between the two generations, and that admittance is the mixing
  amplitude itself (`KronSeries`: the reduced coupling is the series admittance, no further function
  applied);
* a lepton-axis coupling is a conductance read as a probability (`NodeElimination.one_leg`,
  Landauer).

Applied to the in-cycle share with no sine: `quark_rule`, `s₁₂ = π/14` (`= CKM.s12`), and
`lepton_rule`, `sin²θ₁₂ = π/10`.

The supplied solar value `1/(2φ)` is `sin(π/10)` (`HalfTurnMixing.half_turn_golden`): it applies a
sine to the share, which the quark side does not do (`sine_reading_differs`: `π/10 − sin(π/10)` lies
in `(0.005, 0.006)`). So with one rule for both sectors the in-cycle transfer predicts
`sin²θ₁₂ = π/10 = 0.3142`, not `1/(2φ) = 0.3090`. The pentagon source of `φ` (`GoldenGeometry`,
`SixHundredCell`) is geometry without a transfer mechanism. Falsification: a measured `sin²θ₁₂`
resolved below `π/10` (JUNO's full precision separates the two values).

Premises inherited: the aperture reading and its normalization (`HalfTurnAperture`), and that the
quark/lepton amplitude-versus-probability split of the node crossings applies to the in-cycle
transfer as well.
-/

noncomputable section
namespace PMFlavor.ConductionRule

/-- The in-cycle channel share for `N` channels. -/
def share (N : ℕ) : ℝ := Real.pi / N

/-- **Quark rule: the share is the mixing amplitude, `s₁₂ = π/14`.** -/
theorem quark_rule : share 14 = CKM.s12 := by
  unfold share CKM.s12; norm_num

/-- **Lepton rule: the share is the mixing probability, `sin²θ₁₂ = π/10`.** -/
theorem lepton_rule : share 10 = Real.pi / 10 := by
  unfold share; norm_num

/-- **The supplied solar value applies a sine to the share.** -/
theorem sine_reading_differs :
    Real.sin (Real.pi / 10) = 1 / (2 * FlavourConstants.φ) ∧
      0.005 < Real.pi / 10 - Real.sin (Real.pi / 10) ∧
      Real.pi / 10 - Real.sin (Real.pi / 10) < 0.006 := by
  have hg := HalfTurnMixing.half_turn_golden
  have hs := HalfTurnMixing.half_turn_sine
  have h5 := FlavourConstants.sqrt5_b
  have hp1 := Real.pi_gt_d4; have hp2 := Real.pi_lt_d4
  refine ⟨by rw [hg]; rfl, ?_, ?_⟩ <;> rw [hs] <;> linarith

end PMFlavor.ConductionRule
