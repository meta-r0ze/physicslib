import Mathlib.Tactic

/-!
# Mixing through the node: two legs give an amplitude `α`, one leg a probability `α`

`ExchangeAxis`: for the two node-crossing generation pairs there is no in-cycle exchange, so the
direct link entry between them vanishes. `NodePassage`: the quark mixings for those pairs are
amplitudes linear in `α`, while the reactor angle fits a probability `3α`. This module shows what
eliminating the node does.

* `eliminate_node`: two generation states `x₁, x₂` (link entries `a, b`, direct coupling `c`)
  coupled to one node state with leg amplitudes `t₁, t₂`, node energy `E`. At any energy `e ≠ E`
  the node is eliminated exactly (Schur complement), and the effective link between the two
  generations is `c + t₁ t₂/(e − E)`. With `c = 0` (no in-cycle exchange) the whole coupling runs
  through the node, and it is the **product of two legs**.
* `two_legs`, `one_leg`: if each leg carries through weight `w` (`|t|² = w`, the node's
  conductance, `PMConstants.HandoffAdmittance.through_eq_conductance`), the two-leg coupling has
  size `w` and enters the mixing **amplitude**; a single leg has amplitude `√w`, so `w` is a
  mixing **probability**.

With `w = α` this is the split `NodePassage` found in the data: states that reach the node from
outside (colour carriers, off the reference axis) mix through two legs, amplitude `∝ α`
(`|V_ub|`, `|V_cb|`); a state that sits on the reference's own axis needs only one leg, probability
`∝ α` (`sin²θ₁₃ = 3α`, three spatial channels in parallel, `ReactorConductance`). The reading that
the lepton-axis states are one leg from the reference node uses the reference's axis being the
lepton axis (`PMConstants.ReferenceAxis`, `CarrierRepresentation`); the leg weight being the same
for every leg is the Closure statement `HandoffAdmittance.closure_one_price`.

**Refinement (`KronSeries`).** With a conserving (Laplacian) link the node's own conductance fixes
`e − E`, and the quark coupling is the Kron-reduced series admittance, `α/2` for two legs (plus the
boundary, `VubSeriesPath`), not the bare product `α`. The lepton side is the node passage itself,
whose probability is its conductance (Landauer, `HandoffAdmittance.through_eq_conductance`); the
`√w` amplitude of `one_leg` is that statement read as an amplitude.
-/

namespace PMFlavor.NodeElimination

theorem eliminate_node (a b c t₁ t₂ E e x₁ x₂ z : ℝ) (he : e ≠ E)
    (h₁ : a * x₁ + c * x₂ + t₁ * z = e * x₁)
    (h₂ : c * x₁ + b * x₂ + t₂ * z = e * x₂)
    (hn : t₁ * x₁ + t₂ * x₂ + E * z = e * z) :
    z = (t₁ * x₁ + t₂ * x₂) / (e - E) ∧
      (a + t₁ ^ 2 / (e - E)) * x₁ + (c + t₁ * t₂ / (e - E)) * x₂ = e * x₁ ∧
      (c + t₁ * t₂ / (e - E)) * x₁ + (b + t₂ ^ 2 / (e - E)) * x₂ = e * x₂ := by
  have hd : e - E ≠ 0 := sub_ne_zero.mpr he
  have hz : z = (t₁ * x₁ + t₂ * x₂) / (e - E) := by
    rw [eq_div_iff hd]
    linear_combination -hn
  have k₁ : t₁ ^ 2 / (e - E) * x₁ + t₁ * t₂ / (e - E) * x₂ = t₁ * z := by rw [hz]; ring
  have k₂ : t₁ * t₂ / (e - E) * x₁ + t₂ ^ 2 / (e - E) * x₂ = t₂ * z := by rw [hz]; ring
  refine ⟨hz, ?_, ?_⟩
  · linear_combination h₁ + k₁
  · linear_combination h₂ + k₂

theorem two_legs (t₁ t₂ w : ℝ) (hw : 0 ≤ w) (h₁ : t₁ ^ 2 = w) (h₂ : t₂ ^ 2 = w) :
    |t₁ * t₂| = w := by
  rw [abs_mul, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs, h₁, h₂,
    Real.mul_self_sqrt hw]

theorem one_leg (t w : ℝ) (h : t ^ 2 = w) : |t| = Real.sqrt w := by
  rw [← h, Real.sqrt_sq_eq_abs]

end PMFlavor.NodeElimination
