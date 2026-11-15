import PMAction.PolarizationCubic

/-!
# The third-order rest on the shell: a constant times `|q|³/|k|⁵`

`PolarizationCubic.cubic_bound` takes any constants that dominate the orders. On the shell, with
`κ = n(k)` (`PolarizationMagnitudes.n1`), `t = n(q)`, unit probe directions and `a κ ≤ 1`, the
magnitudes of `PolarizationMagnitudes` are dominated by `A = 4κ`, `B = 2`, `C = (2/3)/κ`,
`E = 1/(4κ²)`, `F = 4κ`, `G = 2`, `H = 3/(2κ)`, `J = 1/(32κ³)`, and `σ = κ²/8` bounds `S`
below (`LeadingLog.half_le_symbol`, `κ² ≤ 4|k|²`).

* `cubic_shell`: then `cubicBound = (t³/κ⁵) P(t/κ)` with `P` a degree-12 polynomial of nonnegative
  coefficients (computed with sympy, checked here by `field_simp; ring`), so for `t ≤ κ` it is at
  most `P(1) t³/κ⁵`, `P(1) = 47979504985/36` (about `1.3 × 10⁹`). The constant is crude (the
  powers of `σ = κ²/8` and the `ℓ¹` sizes); it multiplies `|q|³`, so the `q²` coefficient is still
  resolved.
-/

noncomputable section
namespace PMAction.PolarizationShellCubic
open PolarizationCubic

/-- The polynomial `P`. -/
def Ppoly (s : ℝ) : ℝ := 831049219/12 + 1534612288/9 * s ^ 1 + 2412121280/9 * s ^ 2 + 2606107172/9 * s ^ 3 + 2166224768/9 * s ^ 4 + 1420045120/9 * s ^ 5 + 250529936/3 * s ^ 6 + 325551104/9 * s ^ 7 + 38090240/3 * s ^ 8 + 3621440/1 * s ^ 9 + 798720/1 * s ^ 10 + 129024/1 * s ^ 11 + 13824/1 * s ^ 12

theorem cubic_shell {κ t : ℝ} (hκ : 0 < κ) (ht0 : 0 ≤ t) (ht : t ≤ κ) :
    cubicBound (4 * κ) 2 (2 / 3 / κ) (1 / (4 * κ ^ 2)) (4 * κ) 2 (3 / 2 / κ) (1 / (32 * κ ^ 3)) t
        (κ ^ 2 / 8) ≤ 47979504985 / 36 * t ^ 3 / κ ^ 5 := by
  have e : cubicBound (4 * κ) 2 (2 / 3 / κ) (1 / (4 * κ ^ 2)) (4 * κ) 2 (3 / 2 / κ)
      (1 / (32 * κ ^ 3)) t (κ ^ 2 / 8) = t ^ 3 / κ ^ 5 * Ppoly (t / κ) := by
    unfold cubicBound Ppoly
    simp only []
    field_simp
    ring
  rw [e]
  have hs0 : 0 ≤ t / κ := div_nonneg ht0 hκ.le
  have hs1 : t / κ ≤ 1 := (div_le_one hκ).2 ht
  have hP : Ppoly (t / κ) ≤ 47979504985 / 36 := by
    unfold Ppoly
    have h1 := pow_le_one₀ hs0 hs1 (n := 1); have h2 := pow_le_one₀ hs0 hs1 (n := 2)
    have h3 := pow_le_one₀ hs0 hs1 (n := 3); have h4 := pow_le_one₀ hs0 hs1 (n := 4)
    have h5 := pow_le_one₀ hs0 hs1 (n := 5); have h6 := pow_le_one₀ hs0 hs1 (n := 6)
    have h7 := pow_le_one₀ hs0 hs1 (n := 7); have h8 := pow_le_one₀ hs0 hs1 (n := 8)
    have h9 := pow_le_one₀ hs0 hs1 (n := 9); have h10 := pow_le_one₀ hs0 hs1 (n := 10)
    have h11 := pow_le_one₀ hs0 hs1 (n := 11); have h12 := pow_le_one₀ hs0 hs1 (n := 12)
    linarith
  calc t ^ 3 / κ ^ 5 * Ppoly (t / κ) ≤ t ^ 3 / κ ^ 5 * (47979504985 / 36) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
    _ = 47979504985 / 36 * t ^ 3 / κ ^ 5 := by ring

end PMAction.PolarizationShellCubic
