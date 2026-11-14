import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# A right angle at `α` needs a quarter turn; the substrate's weak refresh does not supply one

The paper's `δ = arctan(σ/χ)` puts the unitarity triangle's angle `α` at `89.5°`; `α = π/2` exactly
gives `δ = 67.7°`, indistinguishable at present precision (REVIEW). The paper is a draft; the
question here is what the `E8` substrate supplies.

**The right angle is a statement about two amplitudes.** In
`V_ud V_ub* + V_cd V_cb* + V_td V_tb* = 0`, `α` is the angle between the `u` and `t` terms.
`quadrature_pythagoras`: if one is the other turned by a quarter, `c = i t a` with `t` real, then
`|b|² = |a|² + |c|²`. So `α = π/2` says those two amplitudes are in quadrature.

**A tested mechanism, excluded by the substrate.** Both terms carry the 1–3 node crossing (`V_ub`
on the up side, `V_td` on the down side), which runs through the spinor classes (`ExchangeAxis`),
and up and down are related by the weak refresh. A half-turn in a single plane of the carrier space
would lift to spinors as `e_a e_b`, which squares to `−1` (`plane_lift_sq`): a quarter turn, and
`α = π/2`. But the substrate's weak refresh is not a single-plane half-turn: it is the sign
exchange of every carrier, `v ↦ −v` (`PMConstants.WeakUniform.refresh_uniform`; the single-axis
flip is excluded by the `D₄` roots). That is a half-turn in two orthogonal planes, which lifts to
`(e_a e_b)(e_c e_d)`, squaring to `+1` (`two_plane_lift_sq`): it acts on a spinor class as `±1`,
and the same class sits on both sides of the 1–3 crossing. So the refresh gives no relative quarter
turn, and this route to `α = π/2` is closed.

**Two further routes, both closed.**
* Non-interference (`noninterference_iff`): quadrature is exactly the statement that the `u` and `t`
  routes add their probabilities. But both routes join the same endpoints (`d` and `b`), so
  distinguishable intermediates (for instance opposite walls) do not stop them interfering; that
  reading gives no constraint.
* Maximal CP violation: with the derived magnitudes (`s₁₂`, `s₁₃ = |V_ub|`, `s₂₃` from `|V_cb|`) held
  fixed, `|J|` is largest at `δ = π/2`, which puts the right angle at `γ` (`γ = 90.0°`); HFLAV's
  `γ = 66.4°` excludes it. `α = π/2` maximizes `|J|` only if `|V_td|` is held fixed instead, which no
  construction supplies.

**The current link constraints do not decide it.** `MassMixing.positive_masses_allow_any_mixing`:
every unitary mixing, any `δ` included, is realized by Hermitian positive-definite links with the
same positive masses, and the structural constraints derived since (root moves diagonal,
`GenerationLabel`; which pairs mix in-cycle or through the node, `ExchangeAxis`; the
amplitude/probability rule, `KronSeries`) fix moduli, not the phases of the link entries. So the
quartet `Re(V_ud V_td* V_tb V_ub*)` is not forced to zero by anything in the library; a source of
the right angle has to constrain the phases of the inter-wall link `Y`.

Equivalently, `α = π/2` predicts `|V_td| = 0.00858` from the other magnitudes, against
`0.0086 ± 0.0002`: a regularity of the data and the draft, without a substrate source yet.
-/

namespace PMFlavor.CPQuarterTurn

/-- Two anticommuting unit generators of a Euclidean Clifford algebra: their product squares to
`−1`. A half-turn in their plane lifts to this element, a quarter turn on spinors. -/
theorem plane_lift_sq {R : Type*} [Ring R] (a b : R) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = -(b * a)) : (a * b) * (a * b) = -1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by noncomm_ring
    _ = a * (-(a * b)) * b := by rw [show b * a = -(a * b) by rw [hab, neg_neg]]
    _ = -((a * a) * (b * b)) := by noncomm_ring
    _ = -1 := by rw [ha, hb, one_mul]

/-- **Quadrature gives the right angle.** If `a + b + c = 0` and `c = i t a` with `t` real, then
`|b|² = |a|² + |c|²`. -/
theorem quadrature_pythagoras (a b c : ℂ) (t : ℝ) (hsum : a + b + c = 0)
    (hc : c = Complex.I * t * a) :
    Complex.normSq b = Complex.normSq a + Complex.normSq c := by
  have hb : b = -a - c := by linear_combination hsum
  subst hb; subst hc
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.neg_im]
  ring

/-- **The sign exchange lifts to `±1` on spinors.** `v ↦ −v` is a half-turn in two orthogonal
planes; its lift `(e_a e_b)(e_c e_d)` (the two plane lifts commute) squares to `+1`, so its
eigenvalues are `±1`: no quarter turn. -/
theorem two_plane_lift_sq {R : Type*} [Ring R] (p q : R) (hp : p * p = -1) (hq : q * q = -1)
    (hpq : p * q = q * p) : (p * q) * (p * q) = 1 := by
  calc (p * q) * (p * q) = p * (q * p) * q := by noncomm_ring
    _ = p * (p * q) * q := by rw [hpq]
    _ = (p * p) * (q * q) := by noncomm_ring
    _ = 1 := by rw [hp, hq, neg_mul_neg, one_mul]

/-- **Quadrature is non-interference.** Two route amplitudes add their probabilities exactly when
their interference term vanishes, `Re(a c̄) = 0`: the right angle at `α` says the `u`- and
`t`-mediated `d → b` routes do not interfere. -/
theorem noninterference_iff (a c : ℂ) :
    Complex.normSq (a + c) = Complex.normSq a + Complex.normSq c ↔
      (a * (starRingEnd ℂ) c).re = 0 := by
  rw [Complex.normSq_add]
  constructor <;> intro h <;> linarith

end PMFlavor.CPQuarterTurn
