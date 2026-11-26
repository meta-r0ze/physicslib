import PMConstants.ScaleResponse

/-!
# The opposite-sign interface term as custodial breaking of the link

`ScaleResponse` showed that the interface factor `k` on `α` must contain, besides screening
`Δα`, a positive term `X` of opposite sign: `1/k = 1 − Δα + X` with `0.0236 < X < 0.0242`.
This module identifies the structure of that term with the inter-sector link of `LinkMass`.

* `delta_r_window`: writing `1/k = 1 − Δr`, the Z-anchor requirement on `k` is
  `0.0349 < Δr < 0.0353`. So `k` is the on-shell relation between `α`, the Fermi readout and
  `m_W² s`, and `X = Δα − Δr`.
* `rho_tree`: the link cost gives `m_W²/m_Z² = g²/(g² + g'²)` exactly, for every `v`. The single
  doublet link is custodial at tree level (`ρ = 1`), so any deviation is a response effect.
* `veltman_pos`: for a link doublet whose two components carry squared masses `a, b > 0`, the
  custodial-breaking function
  `F(a,b) = (a+b)/2 − ab/(a−b) · log(a/b)` is strictly positive exactly when `a ≠ b`
  (`F(a,a) = 0`). A split doublet therefore contributes with one definite sign: the
  opposite-sign term `ScaleResponse` requires has the sign of link-doublet splitting.
* `leading_bounds`, `remainder_required`: with the one-loop normalization
  `Δρ = 3 G_F F/(8√2π²)` for a coloured doublet with one light member (`F → m_t²`), the
  leading term `(c²/s²)Δρ` with the paper's `s = 1849/8295`, Paper III's own `G_F`, and the
  comparison input for the top mass in e8p lies in `(0.0324, 0.0327)`. It overshoots the
  required `X`, so a remainder `R` with `X = (c²/s²)Δρ − R` must satisfy `0.0082 < R < 0.0091`.

Premises, labelled: the one-loop normalization `3/(8√2π²)` and the top mass are imported
comparison inputs, not substrate derivations, exactly as `Δα` is in `ScaleResponse`. What is
derived here is the tree-level custodial relation, the sign of the splitting term, and the
numerical size the non-leading remainder must have.

The measured comparison proofs are in `tools/e8p/E8PConstants/PMConstants/ScaleComparisons.lean`.
-/

noncomputable section
namespace PMConstants.LinkCustodial
open PMConstants ElectroweakE8 CertifiedConstants JointConstants GaugeSpectrum ElectroweakBounds

/-! ## `k` is the on-shell `Δr` -/

/-! ## Tree level: the doublet link is custodial -/

theorem rho_tree (g gp v : ℝ) (hg : 0 < g^2 + gp^2) (hv : v ≠ 0) :
    (g^2 * v^2 / 4) / ((g^2 + gp^2) * v^2 / 4) = g^2 / (g^2 + gp^2) := by
  have : v^2 ≠ 0 := pow_ne_zero 2 hv
  field_simp

/-! ## The splitting function has one sign -/

theorem log_lt_half_sub_inv {t : ℝ} (ht : 1 < t) : Real.log t < (t - t⁻¹)/2 := by
  have key : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun x : ℝ => (x - x⁻¹)/2 - Real.log x) ((1 - -(x^2)⁻¹)/2 - x⁻¹) x := by
    intro x hx
    exact (((hasDerivAt_id' x).sub (hasDerivAt_inv hx.ne')).div_const 2).sub
      (Real.hasDerivAt_log hx.ne')
  have hcont : ContinuousOn (fun x : ℝ => (x - x⁻¹)/2 - Real.log x) (Set.Ici 1) := by
    intro x hx
    have hx' : (0 : ℝ) < x := by have := Set.mem_Ici.mp hx; linarith
    exact (key x hx').continuousAt.continuousWithinAt
  have hpos : ∀ x ∈ interior (Set.Ici (1 : ℝ)),
      0 < deriv (fun x : ℝ => (x - x⁻¹)/2 - Real.log x) x := by
    intro x hx
    rw [interior_Ici] at hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : (0 : ℝ) < x := by linarith
    rw [(key x hx0).deriv]
    have he : (1 - -(x^2)⁻¹)/2 - x⁻¹ = (x - 1)^2 / (2 * x^2) := by
      field_simp; ring
    rw [he]
    apply div_pos
    · have : x - 1 ≠ 0 := by linarith
      positivity
    · positivity
  have hmono := strictMonoOn_of_deriv_pos (convex_Ici (1 : ℝ)) hcont hpos
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.le) ht
  simp only [inv_one, sub_self, zero_div, Real.log_one] at h
  linarith

/-- Custodial-breaking function of a doublet with squared masses `a`, `b`. -/
def veltman (a b : ℝ) : ℝ :=
  if a = b then 0 else (a + b)/2 - a*b/(a - b) * Real.log (a/b)

theorem veltman_comm (a b : ℝ) : veltman a b = veltman b a := by
  unfold veltman
  by_cases h : a = b
  · subst h; simp
  · simp only [h, Ne.symm h, ↓reduceIte]
    have hl : Real.log (b/a) = - Real.log (a/b) := by rw [← Real.log_inv, inv_div]
    rw [hl]
    have hne : a - b ≠ 0 := sub_ne_zero.mpr h
    have hne' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have : b*a/(b - a) = -(a*b/(a - b)) := by field_simp; ring
    rw [this]; ring

theorem veltman_pos_of_gt {a b : ℝ} (hb : 0 < b) (hab : b < a) : 0 < veltman a b := by
  have ha : 0 < a := by linarith
  have ht : 1 < a/b := (one_lt_div hb).mpr hab
  have hl := log_lt_half_sub_inv ht
  have hc : 0 < a*b/(a - b) := div_pos (mul_pos ha hb) (by linarith)
  have hm := mul_lt_mul_of_pos_left hl hc
  have hne : a - b ≠ 0 := by linarith
  have he : a*b/(a - b) * ((a/b - (a/b)⁻¹)/2) = (a + b)/2 := by
    field_simp; ring
  unfold veltman
  simp only [ne_of_gt hab, ↓reduceIte]
  linarith

theorem veltman_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < veltman a b ↔ a ≠ b := by
  constructor
  · intro h he; subst he; simp [veltman] at h
  · intro h
    rcases lt_or_gt_of_ne h with h' | h'
    · rw [veltman_comm]; exact veltman_pos_of_gt ha h'
    · exact veltman_pos_of_gt hb h'

/-! ## Size of the leading splitting term -/

/-- `(c²/s²) · 3 G_F m² / (8√2π²)`: the leading custodial term for a coloured doublet with
one light member. -/
def leadingTerm (s GF m : ℝ) : ℝ := (1 - s)/s * (3 * GF * m^2) / (8 * Real.sqrt 2 * Real.pi^2)

end PMConstants.LinkCustodial
