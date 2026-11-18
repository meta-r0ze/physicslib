import PMAction.NativeExternal
import PMAction.FiniteVertex

/-!
# The conserved spinor vertex of the native wall block

`FiniteVertex.ward` gives the conserved finite-`q` vertex of the scalar link Laplacian. The muon and
electron are wall modes: one wall's block is `Σⱼ sin kⱼ αⱼ + δ β` (`NativeExternal.wall_block`).
Gauging its hop with a link phase gives the electromagnetic vertex between `k` and `k + q`. This
module gives that vertex and its Ward identity.

* `ward`: exactly, `H(k + q) − H(k) = Σⱼ 2 sin(qⱼ/2) cos(kⱼ + qⱼ/2) αⱼ`. The detuning term
  cancels. So the conserved spatial vertex is `αⱼ cos(kⱼ + qⱼ/2)` with the factor
  `sin(qⱼ/2)/(qⱼ/2)`: the midpoint velocity, weighted as in the scalar case.
* `coeff_gap`: the coefficient of `αⱼ` differs from `qⱼ` by at most `|qⱼ|³/24 + |qⱼ| wⱼ²/2`,
  with `wⱼ = kⱼ + qⱼ/2`.
* `ward_gap`: hence `H(k + q) − H(k) = Σⱼ qⱼ αⱼ + E` with every entry of `E` bounded by
  `Σⱼ (|qⱼ|³/24 + |qⱼ| wⱼ²/2)`. The leading term contracts `q` with the native velocities
  `αⱼ = J(j+1) = γ⁰γʲ` (`NativeExternal.J`, `J_eq`), the continuum vertex `γ^μ`.

* `propagator_ward`: with `S(k) = (z − H(k))⁻¹`, exactly `S(k + q) · Γ(k, q) · S(k) =
  S(k + q) − S(k)`, where `Γ` is the contracted vertex. A photon of momentum `q` inserted in an
  internal wall line is the difference of that line at the two momenta.
* `contact_ward`: the two-photon contact term of the gauged hop obeys the matching identity: its
  contracted finite-`q` form is the difference of the one-photon vertices `cos kⱼ αⱼ`.

So the one-loop vertex and self-energy integrands obey the Ward–Takahashi identity at every
loop momentum, including momenta near the cutoff. The cancellation `Z₁ = Z₂` therefore holds on
the substrate itself, not only in the continuum limit. Not proved here: the size of the finite
remainder from loop momenta near the cutoff.

Lattice momenta are in units of the inverse spacing, so the remainders are `O(a²)` relative at
physical momenta. The density component `J 0 = 1` needs no correction: the update conserves
the norm.
-/

noncomputable section
namespace PMAction.SpinorVertex
open Real ConcreteFermion Matrix

/-- One wall's block at lattice momentum `k` and detuning `δ`. -/
def block (k : Fin 3 → ℝ) (δ : ℝ) : Spin :=
  DomainWallSpectrum.momentum alpha k + δ • beta

/-- The contracted conserved vertex. -/
def contracted (k q : Fin 3 → ℝ) : Spin :=
  ∑ j, (2 * sin (q j / 2) * cos (k j + q j / 2)) • alpha j

/-- **Ward identity.** The difference of wall blocks is the contracted vertex. -/
theorem ward (k q : Fin 3 → ℝ) (δ : ℝ) :
    block (k + q) δ - block k δ = contracted k q := by
  simp only [block, DomainWallSpectrum.momentum, contracted, add_sub_add_right_eq_sub,
    ← Finset.sum_sub_distrib, ← sub_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Pi.add_apply, sin_sub_sin]
  have h1 : (k j + q j - k j) / 2 = q j / 2 := by ring
  have h2 : (k j + q j + k j) / 2 = k j + q j / 2 := by ring
  rw [h1, h2]

/-- **The vertex coefficient.** `2 sin(q/2) cos w` is `q` up to `|q|³/24 + |q| w²/2`. -/
theorem coeff_gap (q w : ℝ) :
    |2 * sin (q / 2) * cos w - q| ≤ |q| ^ 3 / 24 + |q| * w ^ 2 / 2 := by
  have hs : |sin (q / 2) - q / 2| ≤ |q / 2| ^ 3 / 6 := by
    rw [abs_sub_comm]; exact abs_sub_sin_le _
  have hc : |cos w - 1| ≤ w ^ 2 / 2 := by
    have h1 := one_sub_sq_div_two_le_cos (x := w)
    have h2 := cos_le_one w
    rw [abs_le]; constructor <;> linarith
  have hcos : |cos w| ≤ 1 := abs_cos_le_one w
  have e : 2 * sin (q / 2) * cos w - q =
      2 * (sin (q / 2) - q / 2) * cos w + q * (cos w - 1) := by ring
  rw [e]
  calc |2 * (sin (q / 2) - q / 2) * cos w + q * (cos w - 1)|
      ≤ |2 * (sin (q / 2) - q / 2) * cos w| + |q * (cos w - 1)| := abs_add_le _ _
    _ = 2 * |sin (q / 2) - q / 2| * |cos w| + |q| * |cos w - 1| := by
        rw [abs_mul, abs_mul, abs_mul, abs_two]
    _ ≤ 2 * (|q / 2| ^ 3 / 6) * 1 + |q| * (w ^ 2 / 2) := by
        gcongr
    _ = |q| ^ 3 / 24 + |q| * w ^ 2 / 2 := by
        rw [abs_div, abs_two]; ring

lemma alpha_entry_bound (j : Fin 3) (a b : Fin 4) : ‖alpha j a b‖ ≤ 1 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp [alpha]

/-- **The continuum vertex plus an `O(a²)` remainder.** Every entry of
`H(k + q) − H(k) − Σⱼ qⱼ αⱼ` is bounded by `Σⱼ (|qⱼ|³/24 + |qⱼ| wⱼ²/2)`. -/
theorem ward_gap (k q : Fin 3 → ℝ) (δ : ℝ) (a b : Fin 4) :
    ‖(block (k + q) δ - block k δ - ∑ j, (q j : ℝ) • alpha j) a b‖ ≤
      ∑ j, (|q j| ^ 3 / 24 + |q j| * (k j + q j / 2) ^ 2 / 2) := by
  rw [ward, contracted, ← Finset.sum_sub_distrib]
  simp only [← sub_smul, Matrix.sum_apply, Matrix.smul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  calc |2 * sin (q j / 2) * cos (k j + q j / 2) - q j| * ‖alpha j a b‖
      ≤ (|q j| ^ 3 / 24 + |q j| * (k j + q j / 2) ^ 2 / 2) * 1 :=
        mul_le_mul (coeff_gap _ _) (alpha_entry_bound j a b) (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- The wall propagator at complex energy `z`. -/
def prop (z : ℂ) (k : Fin 3 → ℝ) (δ : ℝ) : Spin := (z • (1 : Spin) - block k δ)⁻¹

/-- **Ward–Takahashi identity for the propagator, exact at finite `q`.** Inserting the
conserved vertex between the two propagators gives their difference. -/
theorem propagator_ward (z : ℂ) (k q : Fin 3 → ℝ) (δ : ℝ)
    (hA : IsUnit (z • (1 : Spin) - block (k + q) δ).det)
    (hB : IsUnit (z • (1 : Spin) - block k δ).det) :
    prop z (k + q) δ * contracted k q * prop z k δ = prop z (k + q) δ - prop z k δ := by
  set A := z • (1 : Spin) - block (k + q) δ
  set B := z • (1 : Spin) - block k δ
  have hBA : B - A = contracted k q := by
    rw [← ward k q δ]; simp only [A, B]; abel
  have hAinv : A⁻¹ * A = 1 := nonsing_inv_mul A hA
  have hBinv : B * B⁻¹ = 1 := mul_nonsing_inv B hB
  simp only [prop]
  change A⁻¹ * contracted k q * B⁻¹ = A⁻¹ - B⁻¹
  rw [← hBA, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hBinv, Matrix.mul_one,
    hAinv, Matrix.one_mul]

/-- **The contact (seagull) Ward identity.** The second link variation of the hop is
`−sin kⱼ αⱼ`; contracting its finite-`q` form with `q` gives the difference of the
first-order vertices `cos kⱼ αⱼ` at the two momenta. -/
theorem contact_ward (k q : Fin 3 → ℝ) (j : Fin 3) :
    (cos (k j + q j) - cos (k j)) • alpha j =
      (-(2 * sin (q j / 2) * sin (k j + q j / 2))) • alpha j := by
  congr 1
  rw [cos_sub_cos]
  have h1 : (k j + q j + k j) / 2 = k j + q j / 2 := by ring
  have h2 : (k j + q j - k j) / 2 = q j / 2 := by ring
  rw [h1, h2]; ring

end PMAction.SpinorVertex
