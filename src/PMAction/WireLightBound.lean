import PMAction.WireMass

/-!
# A lower bound on the wire's light-mass ratio (`δ_O ≥ 0`)

The derived wire (`PMAction.WireMass`, `K = 1`, carriers `(1, k, k)` on both walls, real `δ`) has light
mass `M = diag(1, k, k) · (δ + cyc(1, k, k))`:

  `M = [[δ, 0, k], [k, kδ, 0], [0, k², kδ]]`.

Its squared singular values are the eigenvalues `a ≤ b ≤ c` of `G = M Mᵀ`, with
`a + b + c = e₁`, `ab + bc + ca = e₂`, `abc = e₃` (Vieta for `G`).

* `vieta_ratio`: for `0 < a ≤ b ≤ c`, `3 e₂² · a ≥ e₁ e₃ · b`. (`a ≥ e₃/e₂` because `bc ≤ e₂`; `b ≤ 3e₂/e₁`
  because `bc ≤ e₂` and `c ≥ e₁/3`.)
* `gram`, `e1_eq`, `e2_eq`, `e3_eq`: `G` and its invariants: `e₁ = δ²(1 + 2k²) + 2k² + k⁴`,
  `e₂ = k² Q` with `Q = (2 + k²)δ⁴ + 3k²δ² + k² + 2k⁴`, `e₃ = det G = k⁴ (δ³ + k²)²`.
* `poly_bound`: for `δ ≥ 0` and `0 < k ≤ 1/10`, `3k² Q² ≤ 2 e₁ (δ³ + k²)²`.
* `light_ratio_bound`: so `2a ≥ k² b`: the lightest-to-middle mass ratio is at least `k/√2`.
* `vieta`, `eig_nonneg`, `eigen_ratio_bound`: the eigenvalues of `G` (Mathlib's Hermitian eigenvalues,
  via the characteristic polynomial) satisfy Vieta, are nonnegative, and obey the bound in any order.
* `M_eq`: `M` is `WireMass.mass δ (1, k, k) (1, k, k)`.

**Scope.** `δ ≥ 0` is the case where `δ³` and the carrier cycle product `κ₀κ₁κ₂ = k²` have the same sign.
For `δ < 0`, or a cycle phase, `det M = k²(δ³ + k²)` can vanish (`WireMass.det_mass`) and the lightest
mass with it; the bound does not hold there. So "a protocol reads the wire's singular values directly
with `δ_O ≥ 0`" requires `m₁/m₂ ≥ k/√2`.
-/

noncomputable section
namespace PMAction.WireLightBound
open Matrix

/-- **Vieta ratio bound.** -/
theorem vieta_ratio {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    3 * (a * b + b * c + c * a) ^ 2 * a ≥ (a + b + c) * (a * b * c) * b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  set e2 := a * b + b * c + c * a with he2
  have h1 : b * c ≤ e2 := by nlinarith [mul_pos ha hb, mul_pos hc ha]
  have h2 : a + b + c ≤ 3 * c := by linarith
  -- a e2 ≥ a b c and 3 e2 ≥ 3 b c ≥ (a+b+c) b
  have h3 : (a + b + c) * b ≤ 3 * e2 := by nlinarith
  have h4 : a * b * c ≤ a * e2 := by nlinarith
  have h5 : 0 ≤ a * b * c := by positivity
  have h6 : 0 ≤ (a + b + c) * b := by positivity
  calc (a + b + c) * (a * b * c) * b = ((a + b + c) * b) * (a * b * c) := by ring
    _ ≤ (3 * e2) * (a * e2) := mul_le_mul h3 h4 h5 (by nlinarith)
    _ = 3 * e2 ^ 2 * a := by ring

/-- The derived wire's light mass with `K = 1`, carriers `(1, k, k)`, real `δ`. -/
def M (δ k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![δ, 0, k; k, k * δ, 0; 0, k ^ 2, k * δ]

/-- **It is `WireMass.mass`** with `K = 1` and carriers `(1, k, k)` on both walls. -/
theorem M_eq (δ k : ℝ) :
    (M δ k).map (fun x : ℝ => (x : ℂ)) = WireMass.mass δ ![1, k, k] ![1, k, k] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, WireMass.mass, WireMass.shift, ReferenceWallRotation.X, CyclicSeesaw.cyc,
      Matrix.diagonal_mul, sq]

/-- `Q`, so that `e₂ = k² Q`. -/
def Q (δ k : ℝ) : ℝ := (2 + k ^ 2) * δ ^ 4 + 3 * k ^ 2 * δ ^ 2 + k ^ 2 + 2 * k ^ 4

/-- The three invariants of `G = M Mᵀ`. -/
def e1 (δ k : ℝ) : ℝ := δ ^ 2 * (1 + 2 * k ^ 2) + 2 * k ^ 2 + k ^ 4
def e2 (δ k : ℝ) : ℝ := k ^ 2 * Q δ k
def e3 (δ k : ℝ) : ℝ := k ^ 4 * (δ ^ 3 + k ^ 2) ^ 2

/-- **The Gram matrix.** -/
theorem gram (δ k : ℝ) : M δ k * (M δ k)ᵀ =
    !![δ ^ 2 + k ^ 2, k * δ, k ^ 2 * δ; k * δ, k ^ 2 * (1 + δ ^ 2), k ^ 3 * δ;
       k ^ 2 * δ, k ^ 3 * δ, k ^ 2 * (k ^ 2 + δ ^ 2)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> ring

/-- **Trace.** -/
theorem e1_eq (δ k : ℝ) : (M δ k * (M δ k)ᵀ).trace = e1 δ k := by
  rw [gram]; simp [Matrix.trace, Fin.sum_univ_three, e1]; ring

/-- **Sum of the principal 2×2 minors.** -/
theorem e2_eq (δ k : ℝ) :
    let G := M δ k * (M δ k)ᵀ
    (G 0 0 * G 1 1 - G 0 1 * G 1 0) + (G 0 0 * G 2 2 - G 0 2 * G 2 0) +
      (G 1 1 * G 2 2 - G 1 2 * G 2 1) = e2 δ k := by
  simp only [gram]; simp [e2, Q]; ring

/-- **Determinant.** -/
theorem e3_eq (δ k : ℝ) : (M δ k * (M δ k)ᵀ).det = e3 δ k := by
  rw [gram, Matrix.det_fin_three]; simp [e3]; ring

/-- A quadratic with positive leading coefficient and nonpositive discriminant is nonnegative. -/
theorem quad_nonneg {B C D x : ℝ} (hB : 0 < B) (h : C ^ 2 ≤ 4 * B * D) :
    0 ≤ B * x ^ 2 - C * x + D := by
  have h4 : 4 * B * (B * x ^ 2 - C * x + D) = (2 * B * x - C) ^ 2 + (4 * B * D - C ^ 2) := by ring
  have : 0 ≤ 4 * B * (B * x ^ 2 - C * x + D) := by rw [h4]; nlinarith [sq_nonneg (2 * B * x - C)]
  by_contra hc
  push Not at hc
  nlinarith

/-- The discriminant condition in `t = k²`. -/
theorem disc {t : ℝ} (t0 : 0 < t) (t1 : t ≤ 1 / 100) :
    (t ^ 3 * (57 + 301 * t + 306 * t ^ 2 + 81 * t ^ 3)) ^ 2 ≤
      4 * (4 * t * (1 + 2 * t)) * (4 * t ^ 2 * (2 + t)) := by
  have hq : 57 + 301 * t + 306 * t ^ 2 + 81 * t ^ 3 ≤ 61 := by nlinarith
  have hq0 : 0 ≤ 57 + 301 * t + 306 * t ^ 2 + 81 * t ^ 3 := by positivity
  have t3 : 0 < t ^ 3 := by positivity
  have ht3 : t ^ 3 ≤ 1 / 1000000 := by
    have := pow_le_pow_left₀ t0.le t1 3; norm_num at this; linarith
  have hC1 : t ^ 3 * (57 + 301 * t + 306 * t ^ 2 + 81 * t ^ 3) ≤ t ^ 3 * 61 :=
    mul_le_mul_of_nonneg_left hq t3.le
  have h1 := pow_le_pow_left₀ (by positivity) hC1 2
  have h3 : (t ^ 3 * 61) ^ 2 ≤ 128 * t ^ 3 := by
    have e : (t ^ 3 * 61) ^ 2 = (3721 * t ^ 3) * t ^ 3 := by ring
    rw [e]; have : 3721 * t ^ 3 ≤ 128 := by linarith
    nlinarith
  have h4 : 4 * (4 * t * (1 + 2 * t)) * (4 * t ^ 2 * (2 + t)) =
      64 * t ^ 3 * ((1 + 2 * t) * (2 + t)) := by ring
  have h5 : 2 ≤ (1 + 2 * t) * (2 + t) := by nlinarith
  have h6 : 128 * t ^ 3 ≤ 64 * t ^ 3 * ((1 + 2 * t) * (2 + t)) := by nlinarith
  rw [h4]; linarith

/-- **The polynomial inequality** behind the bound, for `δ ≥ 0`, `0 < k ≤ 1/10`. -/
theorem poly_bound {δ k : ℝ} (hδ : 0 ≤ δ) (hk : 0 < k) (hk1 : k ≤ 1 / 10) :
    3 * k ^ 2 * Q δ k ^ 2 ≤ 2 * e1 δ k * (δ ^ 3 + k ^ 2) ^ 2 := by
  have t0 : 0 < k ^ 2 := by positivity
  have t1 : k ^ 2 ≤ 1 / 100 := by nlinarith
  have key : 2 * e1 δ k * (δ ^ 3 + k ^ 2) ^ 2 - 3 * k ^ 2 * Q δ k ^ 2 =
      δ ^ 2 * (2 * k * δ ^ 2 - 3 * k ^ 3) ^ 2 +
      (δ ^ 4 - (17 * (k ^ 2) ^ 2 + 9 * (k ^ 2) ^ 3) * δ ^ 2) ^ 2 +
      ((1 + k ^ 2) * (1 - 9 * k ^ 2 - 3 * (k ^ 2) ^ 2)) * δ ^ 8 +
      δ ^ 3 * ((4 * k ^ 2 * (1 + 2 * k ^ 2)) * δ ^ 2 -
        ((k ^ 2) ^ 3 * (57 + 301 * k ^ 2 + 306 * (k ^ 2) ^ 2 + 81 * (k ^ 2) ^ 3)) * δ +
        4 * (k ^ 2) ^ 2 * (2 + k ^ 2)) +
      ((k ^ 2) ^ 2 * (2 - 23 * k ^ 2 - 36 * (k ^ 2) ^ 2)) * δ ^ 2 +
      (k ^ 2) ^ 3 * (1 - 10 * k ^ 2 - 12 * (k ^ 2) ^ 2) := by
    simp only [e1, Q]; ring
  have hA : 0 ≤ ((1 + k ^ 2) * (1 - 9 * k ^ 2 - 3 * (k ^ 2) ^ 2)) * δ ^ 8 :=
    mul_nonneg (mul_nonneg (by positivity) (by nlinarith)) (by positivity)
  have hE : 0 ≤ ((k ^ 2) ^ 2 * (2 - 23 * k ^ 2 - 36 * (k ^ 2) ^ 2)) * δ ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (by nlinarith)) (by positivity)
  have hG : 0 ≤ (k ^ 2) ^ 3 * (1 - 10 * k ^ 2 - 12 * (k ^ 2) ^ 2) :=
    mul_nonneg (by positivity) (by nlinarith)
  have hbr := quad_nonneg (x := δ) (by positivity : 0 < 4 * k ^ 2 * (1 + 2 * k ^ 2)) (disc t0 t1)
  have hbr3 := mul_nonneg (pow_nonneg hδ 3) hbr
  have hs1 : 0 ≤ δ ^ 2 * (2 * k * δ ^ 2 - 3 * k ^ 3) ^ 2 := by positivity
  have hs2 : 0 ≤ (δ ^ 4 - (17 * (k ^ 2) ^ 2 + 9 * (k ^ 2) ^ 3) * δ ^ 2) ^ 2 := by positivity
  linarith

/-- **The light-ratio bound.** If `0 < a ≤ b ≤ c` are the eigenvalues of `G = M Mᵀ` (given by
Vieta: trace `e₁`, principal minors `e₂`, determinant `e₃`), `δ ≥ 0` and `0 < k ≤ 1/10`, then
`2a ≥ k² b`: squared, the lightest-to-middle mass ratio is at least `k²/2`. -/
theorem light_ratio_bound {δ k a b c : ℝ} (hδ : 0 ≤ δ) (hk : 0 < k) (hk1 : k ≤ 1 / 10)
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (h2 : a * b + b * c + c * a = e2 δ k) (h1 : a + b + c = e1 δ k) (h3 : a * b * c = e3 δ k) :
    k ^ 2 * b ≤ 2 * a := by
  have hv := vieta_ratio ha hab hbc
  rw [h1, h2, h3] at hv
  have hp := poly_bound hδ hk hk1
  have hQ : 0 < Q δ k := by unfold Q; positivity
  have hk4 : 0 < k ^ 4 := by positivity
  have hb : 0 < b := lt_of_lt_of_le ha hab
  -- 3 k⁴ Q² a ≥ e₁ k⁴ S² b, so 3 Q² a ≥ e₁ S² b ≥ (3/2) k² Q² b
  have h4 : 3 * Q δ k ^ 2 * a * k ^ 4 ≥ e1 δ k * (δ ^ 3 + k ^ 2) ^ 2 * b * k ^ 4 := by
    unfold e2 e3 at hv; nlinarith
  have h5 : 3 * Q δ k ^ 2 * a ≥ e1 δ k * (δ ^ 3 + k ^ 2) ^ 2 * b := le_of_mul_le_mul_right h4 hk4
  have h6 : 3 * k ^ 2 * Q δ k ^ 2 * b ≤ 2 * e1 δ k * (δ ^ 3 + k ^ 2) ^ 2 * b :=
    mul_le_mul_of_nonneg_right hp hb.le
  have h7 : 3 * Q δ k ^ 2 * (k ^ 2 * b) ≤ 3 * Q δ k ^ 2 * (2 * a) := by nlinarith
  exact le_of_mul_le_mul_left h7 (by positivity)

/-! ## The eigenvalues of `G` satisfy Vieta -/

theorem G_hermitian (δ k : ℝ) : (M δ k * (M δ k)ᵀ).IsHermitian := by
  have h := Matrix.isHermitian_mul_conjTranspose_self (M δ k)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The characteristic polynomial of `G`, evaluated: `det(t − G) = t³ − e₁t² + e₂t − e₃`. -/
theorem char_eval (δ k t : ℝ) :
    (Matrix.scalar (Fin 3) t - M δ k * (M δ k)ᵀ).det =
      t ^ 3 - e1 δ k * t ^ 2 + e2 δ k * t - e3 δ k := by
  rw [gram, Matrix.det_fin_three]
  simp [Matrix.scalar_apply, e1, e2, e3, Q, Matrix.sub_apply]
  ring

/-- **Vieta for the eigenvalues of `G`.** -/
theorem vieta (δ k : ℝ) :
    let l := (G_hermitian δ k).eigenvalues
    l 0 + l 1 + l 2 = e1 δ k ∧ l 0 * l 1 + l 1 * l 2 + l 2 * l 0 = e2 δ k ∧
      l 0 * l 1 * l 2 = e3 δ k := by
  intro l
  have hp : ∀ t : ℝ, (t - l 0) * (t - l 1) * (t - l 2) =
      t ^ 3 - e1 δ k * t ^ 2 + e2 δ k * t - e3 δ k := by
    intro t
    have h := congrArg (Polynomial.eval t) (G_hermitian δ k).charpoly_eq
    rw [Matrix.eval_charpoly, char_eval] at h
    rw [h, Polynomial.eval_prod, Fin.prod_univ_three]
    simp [l]
  have h0 := hp 0; have h1 := hp 1; have h2 := hp (-1)
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- The eigenvalues of `G = M Mᵀ` are nonnegative. -/
theorem eig_nonneg (δ k : ℝ) (i : Fin 3) : 0 ≤ (G_hermitian δ k).eigenvalues i := by
  have hpsd : (M δ k * (M δ k)ᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose (M δ k)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact hpsd.eigenvalues_nonneg i

/-- **The light-ratio bound for the eigenvalues of `G`.** For `δ ≥ 0`, `0 < k ≤ 1/10`, and any
order `a ≤ b ≤ c` of the three eigenvalues (squared singular values of the wire's light mass),
`k² b ≤ 2 a`. -/
theorem eigen_ratio_bound {δ k : ℝ} (hδ : 0 ≤ δ) (hk : 0 < k) (hk1 : k ≤ 1 / 10)
    (i j l : Fin 3) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (hab : (G_hermitian δ k).eigenvalues i ≤ (G_hermitian δ k).eigenvalues j)
    (hbc : (G_hermitian δ k).eigenvalues j ≤ (G_hermitian δ k).eigenvalues l) :
    k ^ 2 * (G_hermitian δ k).eigenvalues j ≤ 2 * (G_hermitian δ k).eigenvalues i := by
  obtain ⟨v1, v2, v3⟩ := vieta δ k
  set L := (G_hermitian δ k).eigenvalues with hL
  have hsym : L i + L j + L l = e1 δ k ∧ L i * L j + L j * L l + L l * L i = e2 δ k ∧
      L i * L j * L l = e3 δ k := by
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all <;>
      refine ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨s1, s2, s3⟩ := hsym
  have he3 : 0 < e3 δ k := by unfold e3; positivity
  have hn := eig_nonneg δ k
  have ha : 0 < L i := by
    rcases (hn i).lt_or_eq with h | h
    · exact h
    · have h' : L i = 0 := h.symm
      rw [h'] at s3; simp at s3; linarith
  exact light_ratio_bound hδ hk hk1 ha hab hbc s2 s1 s3

end PMAction.WireLightBound
