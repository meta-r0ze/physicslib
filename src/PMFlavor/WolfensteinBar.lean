import PMFlavor.Wolfenstein

/-!
# The barred Wolfenstein parameters `ρ̄`, `η̄` (the PDG definition), and a tight `A`

`Wolfenstein.wRho`, `wEta` are the paper's `ρ + iη = conj(V_ub)/(Aλ³)`, the *unbarred* pair. The PDG
global fit quotes the *barred* pair, `ρ̄ + iη̄ = −V_ud V_ub* / (V_cd V_cb*)` (PDG 2024, eq. 12.4),
with `ρ̄ = ρ(1 − λ²/2 + …)`. Comparing the unbarred values with the PDG's barred ones mixes two
definitions (about `2.5 %`). This module defines the barred pair on the same matrix.

With the standard parametrization (`V_ud = c₁₂c₁₃`, `V_ub* = s₁₃ e^{iδ}`, `V_cb = s₂₃c₁₃`,
`V_cd = −s₁₂c₂₃ − c₁₂s₂₃s₁₃ e^{iδ}`), write `P = s₁₂c₂₃`, `R = c₁₂s₂₃s₁₃`. Then

  `ρ̄ + iη̄ = c₁₂ s₁₃ e^{iδ} / (s₂₃ (P + R e^{iδ}))`,

so with `D = P² + 2PR cos δ + R²`:

  `ρ̄ = c₁₂ s₁₃ (P cos δ + R) / (s₂₃ D)`,  `η̄ = c₁₂ s₁₃ P sin δ / (s₂₃ D)`.

* `zbar_eq`: the closed form equals the PDG ratio `−V_ud V_ub*/(V_cd V_cb*)` on `Wolfenstein.matrix`.
* `rhoBar_bounds`, `etaBar_bounds`, `wA_tight`: enclosures narrow enough for e8p's σ.
-/

noncomputable section
namespace PMFlavor.WolfensteinBar
open CKM Wolfenstein ComplexConjugate

/-- `P = s₁₂ c₂₃`. -/
def P : ℝ := s12 * c23
/-- `R = c₁₂ s₂₃ s₁₃`. -/
def R : ℝ := c12 * s23 * s13
/-- `D = |P + R e^{iδ}|²`. -/
def D : ℝ := P ^ 2 + 2 * P * R * Real.cos δ + R ^ 2

/-- Barred `ρ̄`. -/
def rhoBar : ℝ := c12 * s13 * (P * Real.cos δ + R) / (s23 * D)
/-- Barred `η̄`. -/
def etaBar : ℝ := c12 * s13 * P * Real.sin δ / (s23 * D)

lemma add_bounds {a b la ua lb ub : ℝ} (ha : la < a ∧ a < ua) (hb : lb < b ∧ b < ub) :
    la + lb < a + b ∧ a + b < ua + ub := ⟨by linarith [ha.1, hb.1], by linarith [ha.2, hb.2]⟩

lemma div_bounds {n d ln un ld ud : ℝ} (hln : 0 ≤ ln) (hld : 0 < ld)
    (hn : ln < n ∧ n < un) (hd : ld < d ∧ d < ud) : ln / ud < n / d ∧ n / d < un / ld := by
  have hd0 : 0 < d := lt_trans hld hd.1
  have hn0 : 0 < n := lt_of_le_of_lt hln hn.1
  constructor
  · rw [div_lt_div_iff₀ (by linarith [hd.2]) hd0]
    nlinarith [hn.1, hd.2]
  · rw [div_lt_div_iff₀ hd0 hld]
    nlinarith [hn.2, hd.1]

theorem P_bounds : (0.224207 : ℝ) < P ∧ P < 0.224209 := by
  have h := mul_bounds (by norm_num) (by norm_num) s12_bounds c23_bounds
  unfold P; constructor <;> nlinarith [h.1, h.2]

theorem R_bounds : (0.0001452 : ℝ) < R ∧ R < 0.0001453 := by
  have h1 := mul_bounds (by norm_num) (by norm_num) c12_bounds s23_bounds
  have h2 := mul_bounds (by norm_num) (by norm_num) h1 s13_bounds
  unfold R; constructor <;> nlinarith [h2.1, h2.2]

theorem D_bounds : (0.0502929 : ℝ) < D ∧ D < 0.0502939 := by
  have hP := P_bounds; have hR := R_bounds
  have pp := mul_bounds (by norm_num) (by norm_num) hP hP
  have pr := mul_bounds (by norm_num) (by norm_num) hP hR
  have prc := mul_bounds (by norm_num) (by norm_num) pr cosδ_bounds
  have rr := mul_bounds (by norm_num) (by norm_num) hR hR
  unfold D
  constructor <;> nlinarith [pp.1, pp.2, prc.1, prc.2, rr.1, rr.2]

theorem den_bounds : (0.0020774 : ℝ) < s23 * D ∧ s23 * D < (0.0020776 : ℝ) := by
  have h := mul_bounds (by norm_num) (by norm_num) s23_bounds D_bounds
  constructor <;> nlinarith [h.1, h.2]

theorem etaNum_bounds :
    (0.00073178 : ℝ) < c12 * s13 * P * Real.sin δ ∧ c12 * s13 * P * Real.sin δ < (0.00073182 : ℝ) := by
  have h1 := mul_bounds (by norm_num) (by norm_num) c12_bounds s13_bounds
  have h2 := mul_bounds (by norm_num) (by norm_num) h1 P_bounds
  have h3 := mul_bounds (by norm_num) (by norm_num) h2 sinδ_bounds
  constructor <;> nlinarith [h3.1, h3.2]

theorem rhoNum_bounds :
    (0.00029322 : ℝ) < c12 * s13 * (P * Real.cos δ + R) ∧
      c12 * s13 * (P * Real.cos δ + R) < (0.00029324 : ℝ) := by
  have h1 := mul_bounds (by norm_num) (by norm_num) P_bounds cosδ_bounds
  have h2 := add_bounds h1 R_bounds
  have h3 := mul_bounds (by norm_num) (by norm_num) c12_bounds s13_bounds
  have h4 := mul_bounds (by norm_num) (by norm_num) h3 h2
  constructor <;> nlinarith [h4.1, h4.2]

/-- **`η̄ = 0.3522…`** -/
theorem etaBar_bounds : (0.3522 : ℝ) < etaBar ∧ etaBar < 0.3523 := by
  have h := div_bounds (by norm_num) (by norm_num) etaNum_bounds den_bounds
  unfold etaBar
  constructor
  · have : (0.3522 : ℝ) < 0.00073178 / 0.0020776 := by norm_num
    linarith [h.1]
  · have : (0.00073182 : ℝ) / 0.0020774 < 0.3523 := by norm_num
    linarith [h.2]

/-- **`ρ̄ = 0.1411…`** -/
theorem rhoBar_bounds : (0.1411 : ℝ) < rhoBar ∧ rhoBar < 0.1412 := by
  have h := div_bounds (by norm_num) (by norm_num) rhoNum_bounds den_bounds
  unfold rhoBar
  constructor
  · have : (0.1411 : ℝ) < 0.00029322 / 0.0020776 := by norm_num
    linarith [h.1]
  · have : (0.00029324 : ℝ) / 0.0020774 < 0.1412 := by norm_num
    linarith [h.2]

/-- **`A = 0.8203…`**, narrower than `Wolfenstein.wA_bounds`. -/
theorem wA_tight : (0.8200 : ℝ) < wA ∧ wA < 0.8207 := by
  rw [wA_eq]
  have c13' : (0.999993 : ℝ) < c13 ∧ c13 < 1.0000001 := ⟨c13_bounds.1, by linarith [c13_bounds.2]⟩
  have n := mul_bounds (by norm_num) (by norm_num) s23_bounds c13'
  have l := mul_bounds (by norm_num) (by norm_num) s12_bounds c13'
  have l2 := mul_bounds (by norm_num) (by norm_num) l l
  rw [sq]
  have h := div_bounds (by norm_num) (by norm_num) n l2
  constructor
  · have : (0.8200 : ℝ) < 0.041308 * 0.999993 / (0.2243995 * 1.0000001 * (0.2243995 * 1.0000001)) := by
      norm_num
    linarith [h.1]
  · have : (0.0413084 * 1.0000001 : ℝ) / (0.2243994 * 0.999993 * (0.2243994 * 0.999993)) < 0.8207 := by
      norm_num
    linarith [h.2]

/-! ## The closed form is the PDG ratio -/

theorem m00 : matrix 0 0 = ((c12 * c13 : ℝ) : ℂ) := by unfold matrix; simp [ckm]
theorem m10 : matrix 1 0 = -((s12 * c23 : ℝ) : ℂ) -
    ((c12 * s23 * s13 : ℝ) : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := by
  unfold matrix; simp [ckm]

theorem D_pos : 0 < D := by linarith [D_bounds.1]

theorem key_re : (P * Real.cos δ + R) * (P + R * Real.cos δ) - (P * Real.sin δ) * (R * Real.sin δ) =
    Real.cos δ * D := by
  unfold D; linear_combination (-(P * R)) * Real.cos_sq_add_sin_sq δ

theorem key_im : (P * Real.cos δ + R) * (R * Real.sin δ) + (P * Real.sin δ) * (P + R * Real.cos δ) =
    Real.sin δ * D := by
  unfold D; ring

/-- Real part: `s₂₃c₁₃ (ρ̄ X − η̄ Y) = −c₁₂c₁₃s₁₃ cos δ`, with `V_cd = X + iY`. -/
theorem re_part : s23 * c13 * (rhoBar * (-(P + R * Real.cos δ)) - etaBar * (-(R * Real.sin δ))) =
    -(c12 * c13 * s13 * Real.cos δ) := by
  have hs23 : s23 ≠ 0 := ne_of_gt s23_pos
  have hD : D ≠ 0 := ne_of_gt D_pos
  have e : rhoBar * (-(P + R * Real.cos δ)) - etaBar * (-(R * Real.sin δ)) =
      -(c12 * s13 / (s23 * D)) * ((P * Real.cos δ + R) * (P + R * Real.cos δ) -
        (P * Real.sin δ) * (R * Real.sin δ)) := by
    unfold rhoBar etaBar; ring
  rw [e, key_re]; field_simp

/-- Imaginary part: `s₂₃c₁₃ (ρ̄ Y + η̄ X) = −c₁₂c₁₃s₁₃ sin δ`. -/
theorem im_part : s23 * c13 * (rhoBar * (-(R * Real.sin δ)) + etaBar * (-(P + R * Real.cos δ))) =
    -(c12 * c13 * s13 * Real.sin δ) := by
  have hs23 : s23 ≠ 0 := ne_of_gt s23_pos
  have hD : D ≠ 0 := ne_of_gt D_pos
  have e : rhoBar * (-(R * Real.sin δ)) + etaBar * (-(P + R * Real.cos δ)) =
      -(c12 * s13 / (s23 * D)) * ((P * Real.cos δ + R) * (R * Real.sin δ) +
        (P * Real.sin δ) * (P + R * Real.cos δ)) := by
    unfold rhoBar etaBar; ring
  rw [e, key_im]; field_simp

/-- **`(ρ̄ + iη̄) · V_cd V_cb* = −V_ud V_ub*`**: the closed forms are the PDG definition. -/
theorem zbar_eq :
    ((rhoBar : ℂ) + (etaBar : ℂ) * Complex.I) * (matrix 1 0 * conj (matrix 1 2)) =
      -(matrix 0 0 * conj (matrix 0 2)) := by
  rw [m10, m12, m00, m02]
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hr := re_part
  have hi := im_part
  unfold P R at hr hi
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linear_combination hr
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linear_combination hi

end PMFlavor.WolfensteinBar
