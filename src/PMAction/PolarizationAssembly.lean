import Mathlib.Tactic

/-!
# Step (ii.d) of the subtracted lattice polarization: the exact second-order assembly

The lattice integrand is `L = P V/(S (S + D)) − C/S` with `P`, `V` the two legs, `S = S(k)`,
`D = S(k + q) − S(k)` and `C` the contact (`PolarizationContact`). `PolarizationSplit` and
`PolarizationOrders` write each as orders in `q`: `P = p₀ + p₁ + p₂ + pₑ`, `V = v₀ + v₁ + v₂ + vₑ`,
`D = d₁ + d₂ + dₑ`, `C = c₀ + c₂ + cₑ` (index = order, `ₑ` = the cubic remainder). This module is
pure algebra over `ℝ`.

* `expand`: `L = L₀ + Lin + Q + R` exactly, with
  `L₀ = p₀v₀/S² − c₀/S` (the `q = 0` value),
  `Lin = (p₀v₁ + p₁v₀)/S² − p₀v₀d₁/S³` (first order),
  `Q = (p₁v₁ + p₀v₂ + p₂v₀)/S² − (p₀v₁ + p₁v₀)d₁/S³ − p₀v₀d₂/S³ + p₀v₀d₁²/S⁴ − c₂/S`
  (second order), and `R` the explicit third-order rest.
* `second_difference`: the first orders are odd and the second even in `q` (`p₁ ↦ −p₁` etc. at
  `−q`), so `L(q) + L(−q) − 2L₀ = 2Q + R(q) + R(−q)`: the odd part cancels exactly, which is what the
  shell's `k ↦ −k` symmetry does to the integral.
* `Rg_bound`: `|R|` by its explicit terms (`R` is `Rg` with `PV = P V`, `D = d₁ + d₂ + dₑ`), for
  `S > 0`, `S + D > 0`.
-/

noncomputable section
namespace PMAction.PolarizationAssembly

/-- The lattice integrand in terms of its orders. -/
def Lfull (S p0 p1 p2 pe v0 v1 v2 ve d1 d2 de c0 c2 ce : ℝ) : ℝ :=
  (p0 + p1 + p2 + pe) * (v0 + v1 + v2 + ve) / (S * (S + (d1 + d2 + de))) - (c0 + c2 + ce) / S

def L0 (S p0 v0 c0 : ℝ) : ℝ := p0 * v0 / S ^ 2 - c0 / S

def Lin (S p0 p1 v0 v1 d1 : ℝ) : ℝ := (p0 * v1 + p1 * v0) / S ^ 2 - p0 * v0 * d1 / S ^ 3

def Q (S p0 p1 p2 v0 v1 v2 d1 d2 c2 : ℝ) : ℝ :=
  (p1 * v1 + p0 * v2 + p2 * v0) / S ^ 2 - (p0 * v1 + p1 * v0) * d1 / S ^ 3 -
    p0 * v0 * d2 / S ^ 3 + p0 * v0 * d1 ^ 2 / S ^ 4 - c2 / S

/-- The third-order rest, with `PV` and `D` as variables. -/
def Rg (S PV D p0 p1 p2 v0 v1 v2 d1 d2 de ce : ℝ) : ℝ :=
  (PV - (p0 * v0 + p0 * v1 + p1 * v0 + p1 * v1 + p0 * v2 + p2 * v0)) / S ^ 2 -
    ((PV - p0 * v0 - p0 * v1 - p1 * v0) * d1 + (PV - p0 * v0) * d2 + PV * de) / S ^ 3 -
    PV * D ^ 3 / (S ^ 4 * (S + D)) +
    ((PV - p0 * v0) * D ^ 2 + p0 * v0 * (d2 + de) * (D + d1)) / S ^ 4 - ce / S

/-- The third-order rest. -/
def R (S p0 p1 p2 pe v0 v1 v2 ve d1 d2 de ce : ℝ) : ℝ :=
  Rg S ((p0 + p1 + p2 + pe) * (v0 + v1 + v2 + ve)) (d1 + d2 + de) p0 p1 p2 v0 v1 v2 d1 d2 de ce

/-- **The exact expansion.** -/
theorem expand (S p0 p1 p2 pe v0 v1 v2 ve d1 d2 de c0 c2 ce : ℝ) (hS : S ≠ 0)
    (hSD : S + (d1 + d2 + de) ≠ 0) :
    Lfull S p0 p1 p2 pe v0 v1 v2 ve d1 d2 de c0 c2 ce =
      L0 S p0 v0 c0 + Lin S p0 p1 v0 v1 d1 + Q S p0 p1 p2 v0 v1 v2 d1 d2 c2 +
        R S p0 p1 p2 pe v0 v1 v2 ve d1 d2 de ce := by
  unfold Lfull L0 Lin Q R Rg
  field_simp
  ring

/-- **The second difference keeps twice the second order.** The values at `−q` have the odd
orders negated and their own remainders. -/
theorem second_difference (S p0 p1 p2 pe pe' v0 v1 v2 ve ve' d1 d2 de de' c0 c2 ce ce' : ℝ)
    (hS : S ≠ 0) (hSD : S + (d1 + d2 + de) ≠ 0) (hSD' : S + (-d1 + d2 + de') ≠ 0) :
    Lfull S p0 p1 p2 pe v0 v1 v2 ve d1 d2 de c0 c2 ce +
        Lfull S p0 (-p1) p2 pe' v0 (-v1) v2 ve' (-d1) d2 de' c0 c2 ce' - 2 * L0 S p0 v0 c0 =
      2 * Q S p0 p1 p2 v0 v1 v2 d1 d2 c2 + R S p0 p1 p2 pe v0 v1 v2 ve d1 d2 de ce +
        R S p0 (-p1) p2 pe' v0 (-v1) v2 ve' (-d1) d2 de' ce' := by
  rw [expand S p0 p1 p2 pe v0 v1 v2 ve d1 d2 de c0 c2 ce hS hSD,
    expand S p0 (-p1) p2 pe' v0 (-v1) v2 ve' (-d1) d2 de' c0 c2 ce' hS hSD']
  unfold Lin Q
  ring

/-- **The rest by its terms.** -/
theorem Rg_bound (S PV D p0 p1 p2 v0 v1 v2 d1 d2 de ce : ℝ) (hS : 0 < S) (hSD : 0 < S + D) :
    |Rg S PV D p0 p1 p2 v0 v1 v2 d1 d2 de ce| ≤
      |PV - (p0 * v0 + p0 * v1 + p1 * v0 + p1 * v1 + p0 * v2 + p2 * v0)| / S ^ 2 +
        (|PV - p0 * v0 - p0 * v1 - p1 * v0| * |d1| + |PV - p0 * v0| * |d2| + |PV| * |de|) / S ^ 3 +
        |PV| * |D| ^ 3 / (S ^ 4 * (S + D)) +
        (|PV - p0 * v0| * D ^ 2 + |p0 * v0| * |d2 + de| * |D + d1|) / S ^ 4 + |ce| / S := by
  have h2 : 0 < S ^ 2 := by positivity
  have h3 : 0 < S ^ 3 := by positivity
  have h4 : 0 < S ^ 4 := by positivity
  have h5 : 0 < S ^ 4 * (S + D) := by positivity
  unfold Rg
  set A := PV - (p0 * v0 + p0 * v1 + p1 * v0 + p1 * v1 + p0 * v2 + p2 * v0)
  set B := (PV - p0 * v0 - p0 * v1 - p1 * v0) * d1 + (PV - p0 * v0) * d2 + PV * de
  set Cc := (PV - p0 * v0) * D ^ 2 + p0 * v0 * (d2 + de) * (D + d1)
  have tA : |A / S ^ 2| = |A| / S ^ 2 := by rw [abs_div, abs_of_pos h2]
  have tB : |B / S ^ 3| ≤ (|PV - p0 * v0 - p0 * v1 - p1 * v0| * |d1| + |PV - p0 * v0| * |d2| +
      |PV| * |de|) / S ^ 3 := by
    rw [abs_div, abs_of_pos h3]
    refine div_le_div_of_nonneg_right ?_ h3.le
    calc |B| ≤ |(PV - p0 * v0 - p0 * v1 - p1 * v0) * d1 + (PV - p0 * v0) * d2| + |PV * de| :=
          abs_add_le _ _
      _ ≤ |(PV - p0 * v0 - p0 * v1 - p1 * v0) * d1| + |(PV - p0 * v0) * d2| + |PV * de| := by
          gcongr; exact abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_mul]
  have tD : |PV * D ^ 3 / (S ^ 4 * (S + D))| = |PV| * |D| ^ 3 / (S ^ 4 * (S + D)) := by
    rw [abs_div, abs_of_pos h5, abs_mul, abs_pow]
  have tC : |Cc / S ^ 4| ≤ (|PV - p0 * v0| * D ^ 2 + |p0 * v0| * |d2 + de| * |D + d1|) / S ^ 4 := by
    rw [abs_div, abs_of_pos h4]
    refine div_le_div_of_nonneg_right ?_ h4.le
    calc |Cc| ≤ |(PV - p0 * v0) * D ^ 2| + |p0 * v0 * (d2 + de) * (D + d1)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg D)]
  have tE : |ce / S| = |ce| / S := by rw [abs_div, abs_of_pos hS]
  calc |A / S ^ 2 - B / S ^ 3 - PV * D ^ 3 / (S ^ 4 * (S + D)) + Cc / S ^ 4 - ce / S|
      ≤ |A / S ^ 2| + |B / S ^ 3| + |PV * D ^ 3 / (S ^ 4 * (S + D))| + |Cc / S ^ 4| + |ce / S| := by
        rw [abs_le]
        constructor <;>
        linarith [le_abs_self (A / S ^ 2), neg_abs_le (A / S ^ 2), le_abs_self (B / S ^ 3),
          neg_abs_le (B / S ^ 3), le_abs_self (PV * D ^ 3 / (S ^ 4 * (S + D))),
          neg_abs_le (PV * D ^ 3 / (S ^ 4 * (S + D))), le_abs_self (Cc / S ^ 4),
          neg_abs_le (Cc / S ^ 4), le_abs_self (ce / S), neg_abs_le (ce / S)]
    _ ≤ _ := by rw [tA, tD, tE]; linarith [tB, tC]

end PMAction.PolarizationAssembly
