import Mathlib.Tactic

/-!
# The node passage: probability for the reactor angle, amplitude for the quarks

`ExchangeAxis` and `ExchangeChirality` derived that two of the three generation pairs mix only
through the reference node. A node passage has through weight `α` per crossing
(`PMConstants.HandoffAdmittance.handoff_is_alpha`, Landauer's relation derived in
`node_current`), and under Closure every crossing sees that one impedance
(`HandoffAdmittance.closure_one_price`). So the price of a passage is derived. What is not fixed by
that is whether a mixing observable is a passage **probability** (conductance, `n α` for `n`
parallel open channels, as in `ReactorConductance`) or a link **amplitude** (an admittance entry
of `Y`, linear in `α`, entering the mixing angle itself).

The data separate the two for the quarks (PDG `|V_cb| = 0.0411 ± 0.0013`,
`|V_ub| = 0.00382 ± 0.00020`, `α = 1/137.036`):
* `quark_not_conductance`: at `3σ` above the central values, `|V_cb|²` and `|V_ub|²` lie below the
  transmission probability of a single open channel, so neither is a node conductance with a whole
  number of channels (that would need `|V| ≥ √α ≈ 0.085`).
* `vub_below_two_passages`: `|V_ub|²` lies below even `α²`, two passages in series.

So the quark node-crossing mixings are amplitudes linear in `α`, which is how the supplied forms
read: `|V_ub| = 1/(χα⁻¹ + π)`, `|V_cb| = (π + χ)/(α⁻¹ − Dπ)`.

For the lepton reactor angle the data do not separate them (NuFIT `sin²θ₁₃ = 0.02225 ± 0.00056`):
* `reactor_both_readings`: the probability form `3α` and the amplitude forms `sin θ₁₃ = 20α`,
  `21α` all lie within `3σ`; `19α` and `22α` do not. Only the probability form has a construction
  (`ReactorConductance`: the `D − 1` spatial-axis channels).

Open: why the quark mixings enter as link amplitudes while the lepton reactor angle (if the
construction holds) enters as a conductance.
-/

namespace PMFlavor.NodePassage

theorem quark_not_conductance (n : ℕ) (hn : 1 ≤ n) :
    (0.0411 + 3 * 0.0013 : ℝ) ^ 2 < n / 137.036 ∧
      (0.00382 + 3 * 0.00020 : ℝ) ^ 2 < n / 137.036 := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (1 : ℝ) / 137.036 ≤ n / 137.036 := by gcongr
  constructor <;> refine lt_of_lt_of_le ?_ h1 <;> norm_num

theorem vub_below_two_passages : (0.00382 + 3 * 0.00020 : ℝ) ^ 2 < (1 / 137.036) ^ 2 := by
  norm_num

theorem reactor_both_readings :
    |3 / 137.036 - (0.02225 : ℝ)| < 3 * 0.00056 ∧
      |(20 / 137.036) ^ 2 - (0.02225 : ℝ)| < 3 * 0.00056 ∧
      |(21 / 137.036) ^ 2 - (0.02225 : ℝ)| < 3 * 0.00056 ∧
      3 * 0.00056 < |(19 / 137.036) ^ 2 - (0.02225 : ℝ)| ∧
      3 * 0.00056 < |(22 / 137.036) ^ 2 - (0.02225 : ℝ)| := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_lt]; constructor <;> norm_num
  · rw [abs_lt]; constructor <;> norm_num
  · rw [abs_lt]; constructor <;> norm_num
  · rw [lt_abs]; right; norm_num
  · rw [lt_abs]; left; norm_num

end PMFlavor.NodePassage
