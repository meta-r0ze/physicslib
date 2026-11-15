import PMAction.PolarizationQDiff
import PMAction.PolarizationShellCubic

/-!
# The second order on the shell: lattice against continuum is `O(a² |q|²/|k|²)`

`PolarizationQDiff.Q_diff` bounds `Q_lat − Q_cont` by the differences of its five terms. On the
shell (`κ = n(k)`, `t = n(q)`, unit probe directions) the gaps of `PolarizationOrders` are
`|l₀ − 2k·u| ≤ (2/3)a²κ³`, `|l₁ − q·u| ≤ a²κ² t`, `|l₂| ≤ (2/3)a²κ t²`, `|s₁ − 2k·q| ≤ (2/3)a²κ³ t`,
`|s₂ − q·q| ≤ a²κ² t²`, `|c₂| ≤ a² t²/3`, and `|S − |k|²| ≤ a²κ⁴/12` (`symbol_gap`); the magnitudes
are `4κ`, `2t`, `4κ t`, `2t²` (lattice) and `2κ`, `t`, `2κ t`, `t²` (continuum); `σ = κ²/8`,
`M = κ²`.

* `pd`: `|xy − XY| ≤ |x − X| |y| + |X| |y − Y|`, with bounds.
* `fb_mono`: the bound of `frac_diff` is monotone in its inputs.
* `Q_shell`: `|Q_lat − Q_cont| ≤ K a² t²/κ²`, `K = 271853128/3` (sympy, checked by `field_simp; ring`).
  The constant is crude; it multiplies `a² |q|²`, the factor the bound needs.
-/

noncomputable section
namespace PMAction.PolarizationShellQ
open PolarizationAssembly PolarizationQDiff PolarizationCubic

lemma pd {x X y Y ex Xb yb ey : ℝ} (hx : |x - X| ≤ ex) (hy : |y| ≤ yb) (hX : |X| ≤ Xb)
    (hyY : |y - Y| ≤ ey) : |x * y - X * Y| ≤ ex * yb + Xb * ey := by
  have e : x * y - X * Y = (x - X) * y + X * (y - Y) := by ring
  rw [e]; exact (abs_add_le _ _).trans (add_le_add (mb hx hy) (mb hX hyY))

lemma fb_mono {σ M dS dS' X X' Y Y' : ℝ} (n : ℕ) (hσ : 0 < σ) (hM : 0 ≤ M) (hdS0 : 0 ≤ dS)
    (hdS : dS ≤ dS') (hX : X ≤ X') (hY0 : 0 ≤ Y) (hY : Y ≤ Y') :
    fb σ M dS n X Y ≤ fb σ M dS' n X' Y' := by
  unfold fb
  have pσ : 0 < σ ^ n := pow_pos hσ n
  refine add_le_add (div_le_div_of_nonneg_right hX pσ.le) (div_le_div_of_nonneg_right ?_ (by positivity))
  refine mul_le_mul hY ?_ (by positivity) (hY0.trans hY)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdS (Nat.cast_nonneg _)) (pow_nonneg hM _)

theorem Q_shell {a κ t S Sc p0 p1 p2 v0 v1 v2 d1 d2 c2 P0 P1 V0 V1 D1 D2 : ℝ}
    (ha : 0 < a) (hκ : 0 < κ)
    (hS : κ ^ 2 / 8 ≤ S) (hSc : κ ^ 2 / 8 ≤ Sc) (hM : |S| ≤ κ ^ 2) (hMc : |Sc| ≤ κ ^ 2)
    (hdS : |S - Sc| ≤ a ^ 2 * κ ^ 4 / 12)
    (hp0 : |p0| ≤ 4 * κ) (hP0 : |P0| ≤ 2 * κ) (he0 : |p0 - P0| ≤ 2 / 3 * a ^ 2 * κ ^ 3)
    (hv0 : |v0| ≤ 4 * κ) (hV0 : |V0| ≤ 2 * κ) (hf0 : |v0 - V0| ≤ 2 / 3 * a ^ 2 * κ ^ 3)
    (hP1 : |P1| ≤ t) (he1 : |p1 - P1| ≤ a ^ 2 * κ ^ 2 * t)
    (hv1 : |v1| ≤ 2 * t) (hV1 : |V1| ≤ t) (hf1v : |v1 - V1| ≤ a ^ 2 * κ ^ 2 * t)
    (hp2 : |p2| ≤ 2 / 3 * a ^ 2 * κ * t ^ 2) (hv2 : |v2| ≤ 2 / 3 * a ^ 2 * κ * t ^ 2)
    (hd1 : |d1| ≤ 4 * κ * t) (hD1 : |D1| ≤ 2 * κ * t) (hg1 : |d1 - D1| ≤ 2 / 3 * a ^ 2 * κ ^ 3 * t)
    (hd2 : |d2| ≤ 2 * t ^ 2) (hD2 : |D2| ≤ t ^ 2) (hg2 : |d2 - D2| ≤ a ^ 2 * κ ^ 2 * t ^ 2)
    (hc2 : |c2| ≤ a ^ 2 * t ^ 2 / 3) :
    |Q S p0 p1 p2 v0 v1 v2 d1 d2 c2 - Q Sc P0 P1 0 V0 V1 0 D1 D2 0| ≤
      271853128 / 3 * a ^ 2 * t ^ 2 / κ ^ 2 := by
  have hσ : (0 : ℝ) < κ ^ 2 / 8 := by positivity
  have hM0 : (0 : ℝ) ≤ κ ^ 2 := by positivity
  have base := Q_diff (p0 := p0) (p1 := p1) (p2 := p2) (v0 := v0) (v1 := v1) (v2 := v2) (d1 := d1)
    (d2 := d2) (c2 := c2) (P0 := P0) (P1 := P1) (V0 := V0) (V1 := V1) (D1 := D1) (D2 := D2)
    hσ hS hSc hM hMc
  -- the numerators
  have hN2 : |(p1 * v1 + p0 * v2 + p2 * v0) - (P1 * V1 + P0 * 0 + 0 * V0)| ≤
      a ^ 2 * κ ^ 2 * t * (2 * t) + t * (a ^ 2 * κ ^ 2 * t) + 4 * κ * (2 / 3 * a ^ 2 * κ * t ^ 2) +
        2 / 3 * a ^ 2 * κ * t ^ 2 * (4 * κ) := by
    have e : (p1 * v1 + p0 * v2 + p2 * v0) - (P1 * V1 + P0 * 0 + 0 * V0) =
        (p1 * v1 - P1 * V1) + p0 * v2 + p2 * v0 := by ring
    rw [e]
    have := abs_le.1 (pd he1 hv1 hP1 hf1v); have := abs_le.1 (mb hp0 hv2)
    have := abs_le.1 (mb hp2 hv0)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hN2c : |P1 * V1 + P0 * 0 + 0 * V0| ≤ t * t := by
    rw [show P1 * V1 + P0 * 0 + 0 * V0 = P1 * V1 by ring]; exact mb hP1 hV1
  have hm : |(p0 * v1 + p1 * v0) - (P0 * V1 + P1 * V0)| ≤
      2 / 3 * a ^ 2 * κ ^ 3 * (2 * t) + 2 * κ * (a ^ 2 * κ ^ 2 * t) +
        (a ^ 2 * κ ^ 2 * t * (4 * κ) + t * (2 / 3 * a ^ 2 * κ ^ 3)) := by
    have e : (p0 * v1 + p1 * v0) - (P0 * V1 + P1 * V0) = (p0 * v1 - P0 * V1) + (p1 * v0 - P1 * V0) := by
      ring
    rw [e]
    have := abs_le.1 (pd he0 hv1 hP0 hf1v); have := abs_le.1 (pd he1 hv0 hP1 hf0)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hMm : |P0 * V1 + P1 * V0| ≤ 2 * κ * t + t * (2 * κ) := by
    have := abs_le.1 (mb hP0 hV1); have := abs_le.1 (mb hP1 hV0)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hN3 := pd hm hd1 hMm hg1
  have hN3c := mb hMm hD1
  have hpv : |p0 * v0 - P0 * V0| ≤ 2 / 3 * a ^ 2 * κ ^ 3 * (4 * κ) + 2 * κ * (2 / 3 * a ^ 2 * κ ^ 3) :=
    pd he0 hv0 hP0 hf0
  have hPV : |P0 * V0| ≤ 2 * κ * (2 * κ) := mb hP0 hV0
  have hM3 := pd hpv hd2 hPV hg2
  have hM3c := mb hPV hD2
  have hd1sq : |d1 ^ 2| ≤ (4 * κ * t) ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hd1 2
  have hdd : |d1 ^ 2 - D1 ^ 2| ≤ 2 / 3 * a ^ 2 * κ ^ 3 * t * (4 * κ * t + 2 * κ * t) := by
    rw [show d1 ^ 2 - D1 ^ 2 = (d1 - D1) * (d1 + D1) by ring]
    refine mb hg1 ?_
    have := abs_le.1 hd1; have := abs_le.1 hD1; exact abs_le.2 ⟨by linarith, by linarith⟩
  have hN4 := pd hpv hd1sq hPV hdd
  have hD1sq : |D1 ^ 2| ≤ (2 * κ * t) ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hD1 2
  have hN4c := mb hPV hD1sq
  have hc : |c2 - 0| ≤ a ^ 2 * t ^ 2 / 3 := by rw [sub_zero]; exact hc2
  have hdS0 : 0 ≤ |S - Sc| := abs_nonneg _
  refine base.trans ?_
  calc _ ≤ fb (κ ^ 2 / 8) (κ ^ 2) (a ^ 2 * κ ^ 4 / 12) 2
          (a ^ 2 * κ ^ 2 * t * (2 * t) + t * (a ^ 2 * κ ^ 2 * t) + 4 * κ * (2 / 3 * a ^ 2 * κ * t ^ 2) +
            2 / 3 * a ^ 2 * κ * t ^ 2 * (4 * κ)) (t * t) +
        fb (κ ^ 2 / 8) (κ ^ 2) (a ^ 2 * κ ^ 4 / 12) 3
          ((2 / 3 * a ^ 2 * κ ^ 3 * (2 * t) + 2 * κ * (a ^ 2 * κ ^ 2 * t) +
            (a ^ 2 * κ ^ 2 * t * (4 * κ) + t * (2 / 3 * a ^ 2 * κ ^ 3))) * (4 * κ * t) +
            (2 * κ * t + t * (2 * κ)) * (2 / 3 * a ^ 2 * κ ^ 3 * t))
          ((2 * κ * t + t * (2 * κ)) * (2 * κ * t)) +
        fb (κ ^ 2 / 8) (κ ^ 2) (a ^ 2 * κ ^ 4 / 12) 3
          ((2 / 3 * a ^ 2 * κ ^ 3 * (4 * κ) + 2 * κ * (2 / 3 * a ^ 2 * κ ^ 3)) * (2 * t ^ 2) +
            2 * κ * (2 * κ) * (a ^ 2 * κ ^ 2 * t ^ 2))
          (2 * κ * (2 * κ) * t ^ 2) +
        fb (κ ^ 2 / 8) (κ ^ 2) (a ^ 2 * κ ^ 4 / 12) 4
          ((2 / 3 * a ^ 2 * κ ^ 3 * (4 * κ) + 2 * κ * (2 / 3 * a ^ 2 * κ ^ 3)) * (4 * κ * t) ^ 2 +
            2 * κ * (2 * κ) * (2 / 3 * a ^ 2 * κ ^ 3 * t * (4 * κ * t + 2 * κ * t)))
          (2 * κ * (2 * κ) * (2 * κ * t) ^ 2) +
        fb (κ ^ 2 / 8) (κ ^ 2) (a ^ 2 * κ ^ 4 / 12) 1 (a ^ 2 * t ^ 2 / 3) 0 := by
        refine add_le_add (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_) ?_
        · exact fb_mono 2 hσ hM0 hdS0 hdS hN2 (abs_nonneg _) hN2c
        · exact fb_mono 3 hσ hM0 hdS0 hdS hN3 (abs_nonneg _) hN3c
        · exact fb_mono 3 hσ hM0 hdS0 hdS hM3 (abs_nonneg _) hM3c
        · exact fb_mono 4 hσ hM0 hdS0 hdS hN4 (abs_nonneg _) hN4c
        · exact fb_mono 1 hσ hM0 hdS0 hdS hc (abs_nonneg _) (by rw [abs_zero])
    _ = 271853128 / 3 * a ^ 2 * t ^ 2 / κ ^ 2 := by
        simp only [fb, Nat.cast_ofNat, Nat.cast_one, Nat.reduceSub, pow_zero, pow_one]
        field_simp
        ring

end PMAction.PolarizationShellQ
