import PMAction.PolarizationAssembly

/-!
# The third-order rest of the lattice polarization is cubic in `q`

`PolarizationAssembly.Rg_bound` bounds the rest `R` by its terms. With magnitude bounds for every
order (`PolarizationMagnitudes`, with `t = n(q)`): `|p₀|, |v₀| ≤ A`, `|p₁|, |v₁| ≤ B t`,
`|p₂|, |v₂| ≤ C t²`, `|pₑ|, |vₑ| ≤ E t³`, `|d₁| ≤ F t`, `|d₂| ≤ G t²`, `|dₑ| ≤ H t³`,
`|cₑ| ≤ J t³`, and `σ ≤ S`, `σ/2 ≤ S + D` (`S + D = S(k + q)`), `cubic_bound` gives `|R| ≤ cubicBound`, every term of
which is at least cubic in `t`. Pure algebra over `ℝ`.
-/

noncomputable section
namespace PMAction.PolarizationCubic
open PolarizationAssembly

lemma mb {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- The bound on the third-order rest. -/
def cubicBound (A B C E F G H J t σ : ℝ) : ℝ :=
  let b1 := A * (E * t ^ 3) + B * t * (C * t ^ 2) + B * t * (E * t ^ 3) + C * t ^ 2 * (B * t) +
    C * t ^ 2 * (C * t ^ 2) + C * t ^ 2 * (E * t ^ 3) + E * t ^ 3 * A + E * t ^ 3 * (B * t) +
    E * t ^ 3 * (C * t ^ 2) + E * t ^ 3 * (E * t ^ 3)
  let πp := B * t + C * t ^ 2 + E * t ^ 3
  let b2a := B * t * (B * t) + A * (C * t ^ 2) + C * t ^ 2 * A + b1
  let b2b := A * πp + πp * A + πp * πp
  let π2 := (A + πp) * (A + πp)
  let δ := F * t + G * t ^ 2 + H * t ^ 3
  b1 / σ ^ 2 + (b2a * (F * t) + b2b * (G * t ^ 2) + π2 * (H * t ^ 3)) / σ ^ 3 +
    π2 * δ ^ 3 / (σ ^ 4 * (σ / 2)) + (b2b * δ ^ 2 + A * A * (G * t ^ 2 + H * t ^ 3) * (δ + F * t)) / σ ^ 4 +
    J * t ^ 3 / σ

theorem cubic_bound {S σ t A B C E F G H J p0 p1 p2 pe v0 v1 v2 ve d1 d2 de ce : ℝ}
    (hσ : 0 < σ) (hS : σ ≤ S) (hSD' : σ / 2 ≤ S + (d1 + d2 + de))
    (h0 : |p0| ≤ A) (h1 : |p1| ≤ B * t) (h2 : |p2| ≤ C * t ^ 2) (he : |pe| ≤ E * t ^ 3)
    (g0 : |v0| ≤ A) (g1 : |v1| ≤ B * t) (g2 : |v2| ≤ C * t ^ 2) (ge : |ve| ≤ E * t ^ 3)
    (k1 : |d1| ≤ F * t) (k2 : |d2| ≤ G * t ^ 2) (ke : |de| ≤ H * t ^ 3) (kc : |ce| ≤ J * t ^ 3) :
    |Rg S ((p0 + p1 + p2 + pe) * (v0 + v1 + v2 + ve)) (d1 + d2 + de) p0 p1 p2 v0 v1 v2 d1 d2 de ce|
      ≤ cubicBound A B C E F G H J t σ := by
  unfold cubicBound
  simp only []
  set PV := (p0 + p1 + p2 + pe) * (v0 + v1 + v2 + ve) with hPV
  set D := d1 + d2 + de with hDdef
  have hS0 : 0 < S := hσ.trans_le hS
  have hSD : σ / 2 ≤ S + D := hSD'
  have hSD0 : 0 < S + D := by linarith
  have base := Rg_bound S PV D p0 p1 p2 v0 v1 v2 d1 d2 de ce hS0 hSD0
  -- the ten third-order products
  have N1 : |PV - (p0 * v0 + p0 * v1 + p1 * v0 + p1 * v1 + p0 * v2 + p2 * v0)| ≤
      A * (E * t ^ 3) + B * t * (C * t ^ 2) + B * t * (E * t ^ 3) + C * t ^ 2 * (B * t) +
      C * t ^ 2 * (C * t ^ 2) + C * t ^ 2 * (E * t ^ 3) + E * t ^ 3 * A + E * t ^ 3 * (B * t) +
      E * t ^ 3 * (C * t ^ 2) + E * t ^ 3 * (E * t ^ 3) := by
    have e : PV - (p0 * v0 + p0 * v1 + p1 * v0 + p1 * v1 + p0 * v2 + p2 * v0) =
        p0 * ve + p1 * v2 + p1 * ve + p2 * v1 + p2 * v2 + p2 * ve + pe * v0 + pe * v1 + pe * v2 +
          pe * ve := by rw [hPV]; ring
    rw [e]
    have := abs_le.1 (mb h0 ge); have := abs_le.1 (mb h1 g2); have := abs_le.1 (mb h1 ge)
    have := abs_le.1 (mb h2 g1); have := abs_le.1 (mb h2 g2); have := abs_le.1 (mb h2 ge)
    have := abs_le.1 (mb he g0); have := abs_le.1 (mb he g1); have := abs_le.1 (mb he g2)
    have := abs_le.1 (mb he ge)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  set b1 := A * (E * t ^ 3) + B * t * (C * t ^ 2) + B * t * (E * t ^ 3) + C * t ^ 2 * (B * t) +
      C * t ^ 2 * (C * t ^ 2) + C * t ^ 2 * (E * t ^ 3) + E * t ^ 3 * A + E * t ^ 3 * (B * t) +
      E * t ^ 3 * (C * t ^ 2) + E * t ^ 3 * (E * t ^ 3) with hb1
  set πp := B * t + C * t ^ 2 + E * t ^ 3 with hπp
  have hP' : |p1 + p2 + pe| ≤ πp := by
    have := abs_le.1 h1; have := abs_le.1 h2; have := abs_le.1 he
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hV' : |v1 + v2 + ve| ≤ πp := by
    have := abs_le.1 g1; have := abs_le.1 g2; have := abs_le.1 ge
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have N2a : |PV - p0 * v0 - p0 * v1 - p1 * v0| ≤ B * t * (B * t) + A * (C * t ^ 2) + C * t ^ 2 * A + b1 := by
    have e : PV - p0 * v0 - p0 * v1 - p1 * v0 = p1 * v1 + p0 * v2 + p2 * v0 +
        (PV - (p0 * v0 + p0 * v1 + p1 * v0 + p1 * v1 + p0 * v2 + p2 * v0)) := by ring
    rw [e]
    have := abs_le.1 (mb h1 g1); have := abs_le.1 (mb h0 g2); have := abs_le.1 (mb h2 g0)
    have := abs_le.1 N1
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have N2b : |PV - p0 * v0| ≤ A * πp + πp * A + πp * πp := by
    have e : PV - p0 * v0 = p0 * (v1 + v2 + ve) + (p1 + p2 + pe) * v0 +
        (p1 + p2 + pe) * (v1 + v2 + ve) := by rw [hPV]; ring
    rw [e]
    have := abs_le.1 (mb h0 hV'); have := abs_le.1 (mb hP' g0); have := abs_le.1 (mb hP' hV')
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have NPV : |PV| ≤ (A + πp) * (A + πp) := by
    have e : PV = (p0 + (p1 + p2 + pe)) * (v0 + (v1 + v2 + ve)) := by rw [hPV]; ring
    rw [e]
    refine mb ?_ ?_
    · have := abs_le.1 h0; have := abs_le.1 hP'; exact abs_le.2 ⟨by linarith, by linarith⟩
    · have := abs_le.1 g0; have := abs_le.1 hV'; exact abs_le.2 ⟨by linarith, by linarith⟩
  set δ := F * t + G * t ^ 2 + H * t ^ 3 with hδ
  have ND : |D| ≤ δ := by
    have := abs_le.1 k1; have := abs_le.1 k2; have := abs_le.1 ke
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have Nde : |d2 + de| ≤ G * t ^ 2 + H * t ^ 3 := by
    have := abs_le.1 k2; have := abs_le.1 ke; exact abs_le.2 ⟨by linarith, by linarith⟩
  have NDd : |D + d1| ≤ δ + F * t := by
    have := abs_le.1 ND; have := abs_le.1 k1; exact abs_le.2 ⟨by linarith, by linarith⟩
  have N00 : |p0 * v0| ≤ A * A := mb h0 g0
  -- nonnegativity of the bounds
  have hb1n : 0 ≤ b1 := (abs_nonneg _).trans N1
  have hb2a : 0 ≤ B * t * (B * t) + A * (C * t ^ 2) + C * t ^ 2 * A + b1 := (abs_nonneg _).trans N2a
  have hb2b : 0 ≤ A * πp + πp * A + πp * πp := (abs_nonneg _).trans N2b
  have hπ2 : 0 ≤ (A + πp) * (A + πp) := (abs_nonneg _).trans NPV
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans ND
  have hFt : 0 ≤ F * t := (abs_nonneg _).trans k1
  have hGt : 0 ≤ G * t ^ 2 := (abs_nonneg _).trans k2
  have hHt : 0 ≤ H * t ^ 3 := (abs_nonneg _).trans ke
  have hJt : 0 ≤ J * t ^ 3 := (abs_nonneg _).trans kc
  have hAA : 0 ≤ A * A := (abs_nonneg _).trans N00
  -- term by term
  have p2le : σ ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hσ.le hS 2
  have p3le : σ ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ hσ.le hS 3
  have p4le : σ ^ 4 ≤ S ^ 4 := pow_le_pow_left₀ hσ.le hS 4
  have T1 : |PV - (p0 * v0 + p0 * v1 + p1 * v0 + p1 * v1 + p0 * v2 + p2 * v0)| / S ^ 2 ≤ b1 / σ ^ 2 :=
    div_le_div₀ hb1n N1 (by positivity) p2le
  have T2 : (|PV - p0 * v0 - p0 * v1 - p1 * v0| * |d1| + |PV - p0 * v0| * |d2| + |PV| * |de|) / S ^ 3
      ≤ ((B * t * (B * t) + A * (C * t ^ 2) + C * t ^ 2 * A + b1) * (F * t) +
          (A * πp + πp * A + πp * πp) * (G * t ^ 2) + (A + πp) * (A + πp) * (H * t ^ 3)) / σ ^ 3 := by
    refine div_le_div₀ (add_nonneg (add_nonneg (mul_nonneg hb2a hFt) (mul_nonneg hb2b hGt))
      (mul_nonneg hπ2 hHt)) ?_ (by positivity) p3le
    exact add_le_add (add_le_add (mul_le_mul N2a k1 (abs_nonneg _) hb2a)
      (mul_le_mul N2b k2 (abs_nonneg _) hb2b)) (mul_le_mul NPV ke (abs_nonneg _) hπ2)
  have T3 : |PV| * |D| ^ 3 / (S ^ 4 * (S + D)) ≤ (A + πp) * (A + πp) * δ ^ 3 / (σ ^ 4 * (σ / 2)) := by
    refine div_le_div₀ (mul_nonneg hπ2 (pow_nonneg hδ0 3)) ?_ (by positivity) ?_
    · exact mul_le_mul NPV (pow_le_pow_left₀ (abs_nonneg _) ND 3) (by positivity) hπ2
    · exact mul_le_mul p4le hSD (by positivity) (by positivity)
  have T4 : (|PV - p0 * v0| * D ^ 2 + |p0 * v0| * |d2 + de| * |D + d1|) / S ^ 4 ≤
      ((A * πp + πp * A + πp * πp) * δ ^ 2 + A * A * (G * t ^ 2 + H * t ^ 3) * (δ + F * t)) / σ ^ 4 := by
    have hD2 : D ^ 2 ≤ δ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ND 2
    refine div_le_div₀ (add_nonneg (mul_nonneg hb2b (sq_nonneg δ))
      (mul_nonneg (mul_nonneg hAA (add_nonneg hGt hHt)) (add_nonneg hδ0 hFt))) ?_ (by positivity) p4le
    exact add_le_add (mul_le_mul N2b hD2 (sq_nonneg _) hb2b)
      (mul_le_mul (mul_le_mul N00 Nde (abs_nonneg _) hAA) NDd (abs_nonneg _)
        (mul_nonneg hAA (add_nonneg hGt hHt)))
  have T5 : |ce| / S ≤ J * t ^ 3 / σ := div_le_div₀ hJt kc hσ hS
  linarith [base, T1, T2, T3, T4, T5]

end PMAction.PolarizationCubic
