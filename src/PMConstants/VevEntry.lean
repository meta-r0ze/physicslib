import PMAction.PersistenceSelection
import PMAction.WallDispersion
import PMConstants.FermionMassLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# How the VEV enters the wall masses: the inter-wall link is excluded

`FermionMassLaw` compares two ways the link vacuum value `v` could set the light fermion's mass,
through the detuning. Law A is the cost `δ² ∝ v`, and law B is the amplitude `δ ∝ v`; `tau_decides`
selects A. A third possibility is that `v` sets the *inter-wall link* `y`, which joins the two
chiral walls, as a Yukawa coupling joins left and right fermions. Paper II's exact two-wall
spectrum (`WallDispersion`) decides it.

* `link_kappa`: with `y = c v`, the light branch has coupling modifier
  `κ = (v/m) dm/dv = −y²/r < 0`, where `r = √(y⁴ + 4y²δ²)`. The mass falls as the link grows (the
  seesaw `m₋² = δ⁴/m₊²`).
* `link_excluded`: against `κ_τ = 0.92 ± 0.08`, a negative `κ` is more than `11σ` away.

Together with `tau_decides` (law B more than `13σ` away), the VEV enters through the detuning cost
(law A), not its amplitude and not the inter-wall link.

* `kappa_power`, `kappa_power_light`, `yukawa_selects_A`: for `δ² = c vᵠ`, a light fermion has
  `κ → q`. A mass linear in `v` gives `q = 1`, which is law A (`mPow_one`).
* `insertions_odd`, `minimal_degree_one`: hypercharge balance forces an odd number of doublet
  insertions in a mass term. The fewest (Economy) is one, so the mass term is linear in `v`.
  `economy_one_insertion`: at a positive price per insertion, Economy selects exactly one, and
  `economy_law_A` gives law A. Economy here is the framework's own pricing rule
  (`RefreshSchedule`), not a separate premise.
-/

noncomputable section
namespace PMConstants.VevEntry
open PMAction.WallDispersion

lemma massSqM_eq (δ y : ℝ) :
    massSqM δ y = δ ^ 2 + (y ^ 2 - Real.sqrt (y ^ 4 + 4 * y ^ 2 * δ ^ 2)) / 2 := by
  simp only [massSqM, rhoM, rr]

lemma hasDeriv_massSqM (δ y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun y => massSqM δ y) (y - y * (y ^ 2 + 2 * δ ^ 2) / rr δ y) y := by
  have hg : HasDerivAt (fun y : ℝ => y ^ 4 + 4 * y ^ 2 * δ ^ 2) (4 * y ^ 3 + 8 * y * δ ^ 2) y := by
    have := ((hasDerivAt_pow 4 y).add (((hasDerivAt_pow 2 y).const_mul 4).mul_const (δ ^ 2)))
    convert this using 1; push_cast; ring
  have hpos : 0 < y ^ 4 + 4 * y ^ 2 * δ ^ 2 := by positivity
  have hs := (Real.hasDerivAt_sqrt hpos.ne').comp y hg
  have h := (((hasDerivAt_pow 2 y).sub hs).div_const 2).const_add (δ ^ 2)
  have hr : 0 < rr δ y := rr_pos δ y hy
  simp only [rr] at hr ⊢
  convert h using 1
  · funext x; simp only [massSqM_eq, Pi.sub_apply, Function.comp]
  · field_simp; push_cast; ring

/-- **The link's coupling modifier is negative.** -/
theorem link_kappa (δ y : ℝ) (hy : 0 < y) (hδ : δ ≠ 0) :
    y / (2 * massSqM δ y) * (y - y * (y ^ 2 + 2 * δ ^ 2) / rr δ y) = -(y ^ 2 / rr δ y) := by
  have hr := rr_pos δ y hy.ne'
  have h2 := rr_sq δ y
  have hm : massSqM δ y ≠ 0 := by
    intro h0
    have hprod := (branch_masses δ y hy.ne').1
    rw [h0, mul_zero] at hprod
    exact hδ (pow_eq_zero_iff (by norm_num) |>.mp hprod.symm)
  have hmeq : 2 * massSqM δ y = 2 * δ ^ 2 + y ^ 2 - rr δ y := by
    simp only [massSqM, rhoM]; ring
  have hm' : 2 * δ ^ 2 + y ^ 2 - rr δ y ≠ 0 := by
    rw [← hmeq]; exact mul_ne_zero two_ne_zero hm
  rw [hmeq]
  field_simp
  ring

theorem link_kappa_neg (δ y : ℝ) (hy : 0 < y) (hδ : δ ≠ 0) :
    y / (2 * massSqM δ y) * (y - y * (y ^ 2 + 2 * δ ^ 2) / rr δ y) < 0 := by
  rw [link_kappa δ y hy hδ]
  have := rr_pos δ y hy.ne'
  have : 0 < y ^ 2 / rr δ y := by positivity
  linarith

/-- **The inter-wall link is excluded** by the measured `κ_τ = 0.92 ± 0.08` (more than `11σ`). -/
theorem link_excluded (δ y : ℝ) (hy : 0 < y) (hδ : δ ≠ 0) :
    11 < |y / (2 * massSqM δ y) * (y - y * (y ^ 2 + 2 * δ ^ 2) / rr δ y) - 0.92| / 0.08 := by
  have h := link_kappa_neg δ y hy hδ
  rw [abs_of_neg (by linarith), lt_div_iff₀ (by norm_num)]
  linarith

/-! ## Law A is the Yukawa-linear entry -/

/-- Light mass when the detuning cost is a power of the vacuum value, `δ² = c vᵠ`. -/
def mPow (c q v : ℝ) : ℝ := Real.sqrt (c * v ^ q + 1 / 4) - 1 / 2

lemma mPow_rel (c q v : ℝ) (h : 0 ≤ c * v ^ q) : mPow c q v * (mPow c q v + 1) = c * v ^ q := by
  have hs := Real.sq_sqrt (show 0 ≤ c * v ^ q + 1 / 4 by linarith)
  simp only [mPow]; nlinarith [hs]

lemma mPow_nonneg (c q v : ℝ) (h : 0 ≤ c * v ^ q) : 0 ≤ mPow c q v := by
  simp only [mPow, sub_nonneg]
  rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith)

/-- Law A (`q = 1`) is `FermionMassLaw.massA`. -/
theorem mPow_one (c v : ℝ) : mPow c 1 v = FermionMassLaw.massA c v := by
  simp [mPow, FermionMassLaw.massA]

/-- The derivative of the light mass in the vacuum value. -/
theorem mPow_deriv (c q v : ℝ) (hv : 0 < v) (hc : 0 < c) :
    HasDerivAt (mPow c q) (c * q * v ^ (q - 1) / (2 * mPow c q v + 1)) v := by
  have hpos : 0 < c * v ^ q + 1 / 4 := by positivity
  have hr := ((HasDerivAt.rpow_const (p := q) (hasDerivAt_id v) (Or.inl hv.ne')).const_mul c).add_const
    (1 / 4 : ℝ)
  have hs := ((Real.hasDerivAt_sqrt hpos.ne').comp v hr).sub_const (1 / 2 : ℝ)
  have h2 : 2 * mPow c q v + 1 = 2 * Real.sqrt (c * v ^ q + 1 / 4) := by simp only [mPow]; ring
  have : 0 < Real.sqrt (c * v ^ q + 1 / 4) := Real.sqrt_pos.mpr hpos
  convert hs using 1
  · funext x; simp [mPow]
  · rw [h2]; simp only [id]; field_simp

/-- **The coupling modifier of a power-law entry**: `κ = (v/m) dm/dv = q (m + 1)/(2m + 1)`. -/
theorem kappa_power (c q v : ℝ) (hv : 0 < v) (hc : 0 < c) (hm : mPow c q v ≠ 0) :
    v / mPow c q v * (c * q * v ^ (q - 1) / (2 * mPow c q v + 1)) =
      q * (mPow c q v + 1) / (2 * mPow c q v + 1) := by
  have hrel := mPow_rel c q v (by positivity)
  have hm0 := mPow_nonneg c q v (by positivity)
  have hvq : v * v ^ (q - 1) = v ^ q := by
    have := Real.rpow_add hv 1 (q - 1)
    rw [Real.rpow_one, show 1 + (q - 1) = q by ring] at this
    exact this.symm
  have h2 : 2 * mPow c q v + 1 ≠ 0 := by positivity
  field_simp
  rw [show v * c * q * v ^ (q - 1) = q * (c * (v * v ^ (q - 1))) by ring, hvq, ← hrel]
  ring

/-- **Light fermions read the exponent.** For `0 ≤ m`, `q(1 − m) ≤ κ ≤ q`, so `κ → q` as `m → 0`. -/
theorem kappa_power_light (q m : ℝ) (hq : 0 ≤ q) (hm : 0 ≤ m) :
    q * (1 - m) ≤ q * (m + 1) / (2 * m + 1) ∧ q * (m + 1) / (2 * m + 1) ≤ q := by
  have h : 0 < 2 * m + 1 := by linarith
  constructor
  · rw [le_div_iff₀ h]; nlinarith [mul_nonneg hq (mul_nonneg hm hm)]
  · rw [div_le_iff₀ h]; nlinarith

/-- **Yukawa linearity selects law A.** A mass term linear in the vacuum value (light-limit
`κ = 1`, the gauge-invariant Yukawa form) holds exactly for `q = 1`, which is law A. Law B is the
amplitude law `δ ∝ v`, i.e. `q = 2`, with `κ → 2`. -/
theorem yukawa_selects_A (q : ℝ) : q * (0 + 1) / (2 * 0 + 1) = 1 ↔ q = 1 := by
  constructor <;> intro h <;> simpa using h

/-! ## Why the mass term is linear in the vacuum value -/

/-- **Hypercharge balance.** A mass term joining a left field of hypercharge `Y_L` to a right
field of hypercharge `Y_R` with `a` insertions of the doublet (`+Y_H`) and `b` of its conjugate
(`−Y_H`) conserves hypercharge exactly when `Y_R − Y_L + (a − b) Y_H = 0`. For the doublet
assignments `Y_R − Y_L = ∓Y_H` (charged leptons and down quarks: `−Y_H`; up quarks: `+Y_H`),
this means `a − b = ±1`. So the number of insertions `a + b` is odd and at least one. -/
theorem insertions_odd (YL YR YH : ℝ) (hYH : YH ≠ 0) (a b : ℕ)
    (hdoublet : YR - YL = -YH ∨ YR - YL = YH)
    (hbal : YR - YL + ((a : ℝ) - b) * YH = 0) :
    Odd (a + b) ∧ 1 ≤ a + b := by
  have hab : (a : ℤ) - b = 1 ∨ (a : ℤ) - b = -1 := by
    rcases hdoublet with h | h
    · left
      have : ((a : ℝ) - b - 1) * YH = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_right hYH
      exact_mod_cast (by linarith : (a : ℝ) - b = 1)
    · right
      have : ((a : ℝ) - b + 1) * YH = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_right hYH
      exact_mod_cast (by linarith : (a : ℝ) - b = -1)
  rcases hab with h | h
  · refine ⟨⟨b, by omega⟩, by omega⟩
  · refine ⟨⟨a, by omega⟩, by omega⟩

/-- **The fewest insertions is one**, which gives a mass term of degree `1` in `v`, the Yukawa
form. Then `q = 1` (`yukawa_selects_A`), which is law A. -/
theorem minimal_degree_one (YL YR YH : ℝ) (hYH : YH ≠ 0)
    (hdoublet : YR - YL = -YH ∨ YR - YL = YH) :
    (∃ a b : ℕ, YR - YL + ((a : ℝ) - b) * YH = 0 ∧ a + b = 1) ∧
      ∀ a b : ℕ, YR - YL + ((a : ℝ) - b) * YH = 0 → 1 ≤ a + b := by
  refine ⟨?_, fun a b h => (insertions_odd YL YR YH hYH a b hdoublet h).2⟩
  rcases hdoublet with h | h
  · exact ⟨1, 0, by push_cast; linarith, rfl⟩
  · exact ⟨0, 1, by push_cast; linarith, rfl⟩

/-- **Economy picks one insertion.** Each doublet insertion is one read of the vacuum value,
priced `η > 0` (`RefreshSchedule.strict_if_extra`). Among hypercharge-balanced mass terms, the
cheapest has exactly one insertion. -/
theorem economy_one_insertion (YL YR YH η : ℝ) (hYH : YH ≠ 0) (hη : 0 < η)
    (hdoublet : YR - YL = -YH ∨ YR - YL = YH) (a b : ℕ) :
    (YR - YL + ((a : ℝ) - b) * YH = 0 ∧
        ∀ a' b' : ℕ, YR - YL + ((a' : ℝ) - b') * YH = 0 → η * (a + b : ℕ) ≤ η * (a' + b' : ℕ)) ↔
      YR - YL + ((a : ℝ) - b) * YH = 0 ∧ a + b = 1 := by
  obtain ⟨⟨a₀, b₀, h₀, h₀1⟩, hge⟩ := minimal_degree_one YL YR YH hYH hdoublet
  constructor
  · rintro ⟨hb, hmin⟩
    refine ⟨hb, le_antisymm ?_ (hge a b hb)⟩
    have := le_of_mul_le_mul_left (hmin a₀ b₀ h₀) hη
    rw [h₀1] at this
    exact_mod_cast this
  · rintro ⟨hb, h1⟩
    refine ⟨hb, fun a' b' h' => mul_le_mul_of_nonneg_left ?_ hη.le⟩
    rw [h1]; exact_mod_cast hge a' b' h'

/-- **One insertion from persistence.** Under the survival law with `β > 0` and a positive price
per vacuum read, the balanced mass term that persists best has one insertion. -/
theorem persistent_one_insertion (YL YR YH β c₀ p : ℝ) (hYH : YH ≠ 0) (hβ : 0 < β) (hc : c₀ = 1)
    (hp : 0 < p) (hdoublet : YR - YL = -YH ∨ YR - YL = YH) (a b : ℕ) :
    (YR - YL + ((a : ℝ) - b) * YH = 0 ∧
        ∀ a' b' : ℕ, YR - YL + ((a' : ℝ) - b') * YH = 0 →
          Real.exp (-β * (c₀ * p * (a' + b' : ℕ))) ≤ Real.exp (-β * (c₀ * p * (a + b : ℕ)))) ↔
      YR - YL + ((a : ℝ) - b) * YH = 0 ∧ a + b = 1 := by
  rw [← economy_one_insertion YL YR YH (c₀ * p) hYH
    (PMAction.PersistenceSelection.event_price_pos c₀ p hc hp) hdoublet a b]
  refine and_congr_right fun _ => forall_congr' fun a' => forall_congr' fun b' =>
    imp_congr_right fun _ => ?_
  exact (PMAction.PersistenceSelection.survival_strictAnti β hβ).le_iff_ge

/-- **Law A from Economy.** With one insertion the mass term has degree `q = 1` in `v`, and the
power law at `q = 1` is law A. -/
theorem economy_law_A (c v : ℝ) (q : ℕ) (hq : q = 1) :
    mPow c q v = FermionMassLaw.massA c v := by
  subst hq; simpa using mPow_one c v

end PMConstants.VevEntry
