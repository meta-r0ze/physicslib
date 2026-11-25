import PMAction.WireResonanceSpectrum
import Mathlib.Topology.Order.IntermediateValue

/-!
# Positive masses of the shifted resonant Schur wire

A positive static insertion at address 2 splits the bare zero mode. Three
disjoint intervals isolate the squared singular values for independent
small restoring rates and for the wider common-rate benchmark.
-/

noncomputable section
namespace PMAction.WireShiftedSpectrum

open WireResonanceSpectrum

private theorem root_between (p : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ x ∈ Set.Ioo a b, p.eval x = 0 := by
  obtain ⟨x, hx, hz⟩ := intermediate_value_Icc hab.le p.continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) from ⟨ha.le, hb.le⟩)
  exact ⟨x, ⟨hx.1.lt_of_ne (by rintro rfl; linarith),
    hx.2.lt_of_ne (by rintro rfl; linarith)⟩, hz⟩

private def cubic (a b u t : ℝ) : ℝ :=
  t ^ 3 - (2 + 2 * a + b * (1 + u ^ 2)) * t ^ 2 +
    (3 * a + b * (2 + u ^ 2) + a * b * (1 + 2 * u ^ 2)) * t -
    a * b * (1 - u) ^ 2

private theorem cubic_signs (a b u : ℝ) (ha : 0 < a) (ha₂ : a ≤ 2 / 3)
    (hb : 0 < b) (hb₂ : b ≤ 2 / 3) (hu : 0 < u) (hu₁ : u < 1) :
    let m := max a b
    cubic a b u 0 < 0 ∧
      0 < cubic a b u m ∧
      cubic a b u (3 * m) < 0 ∧
      cubic a b u (max 2 (3 * m)) < 0 ∧ 0 < cubic a b u 4 := by
  intro m
  have ha₁ : a < 1 := by linarith
  have hb₁ : b < 1 := by linarith
  have hu₂ : 0 ≤ u ^ 2 := sq_nonneg _
  have hu₂₁ : u ^ 2 ≤ 1 := by nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu₁.le)]
  have h0 : cubic a b u 0 < 0 := by
    have h : 0 < a * b * (1 - u) ^ 2 := by positivity
    simpa [cubic] using neg_neg_of_pos h
  have h2 : cubic a b u 2 < 0 := by
    rw [show cubic a b u 2 =
      -(2 * a * (1 - 3 * b / 2)) - 2 * b * (1 - 3 * a / 2) * u ^ 2 -
        2 * a * b * (1 - u) by simp [cubic]; ring]
    have h₁ : 0 ≤ 2 * a * (1 - 3 * b / 2) := mul_nonneg (by positivity) (by linarith)
    have h₂ : 0 ≤ 2 * b * (1 - 3 * a / 2) * u ^ 2 :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) hu₂
    have h₃ : 0 < 2 * a * b * (1 - u) := by positivity
    linarith
  have h4 : 0 < cubic a b u 4 := by
    rw [show cubic a b u 4 =
      (1 - a) * (1 - b) * 32 + a * (1 - b) * 12 +
        (1 - a) * b * (24 - 12 * u ^ 2) + a * b * (2 + 2 * u + 5 * (1 - u ^ 2)) by
      simp [cubic]; ring]
    have h₁ : 0 < (1 - a) * (1 - b) * 32 := by positivity
    have h₂ : 0 ≤ a * (1 - b) * 12 := by positivity
    have h₃ : 0 ≤ (1 - a) * b * (24 - 12 * u ^ 2) := mul_nonneg (by positivity) (by linarith)
    have h₄ : 0 ≤ a * b * (2 + 2 * u + 5 * (1 - u ^ 2)) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have principal (x : ℝ) (hx : 0 < x) (hx₁ : x < 1) : cubic x x u (3 * x) < 0 := by
    rw [show cubic x x u (3 * x) =
      -(x ^ 2 * (3 * (1 - u ^ 2) * (1 - x) + (1 - u) ^ 2)) by simp [cubic]; ring]
    have h₁ : 0 ≤ 3 * (1 - u ^ 2) * (1 - x) :=
      mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hu₂₁)) (by positivity)
    have h₂ : 0 < (1 - u) ^ 2 := by positivity
    exact neg_neg_of_pos (mul_pos (by positivity) (by linarith))
  have hm : 0 < cubic a b u m ∧ cubic a b u (3 * m) < 0 := by
    rcases le_total b a with hba | hab
    · dsimp only [m]
      rw [max_eq_left hba]
      constructor
      · rw [show cubic a b u a =
          a * ((a - b) * (1 - a) + b * (1 + u) * (2 - a * (1 - u))) by
          simp [cubic]; ring]
        have h₁ : 0 ≤ (a - b) * (1 - a) :=
          mul_nonneg (sub_nonneg.mpr hba) (by positivity)
        have h₂ : 0 < b * (1 + u) * (2 - a * (1 - u)) := by
          have hlt : a * (1 - u) < 2 := by nlinarith [mul_pos (sub_pos.mpr ha₁) (show 0 < 1 - u by positivity)]
          exact mul_pos (by positivity) (sub_pos.mpr hlt)
        exact mul_pos ha (by linarith)
      · have hbare : cubic a 0 u (3 * a) < 0 := by
          rw [show cubic a 0 u (3 * a) = -(9 * a ^ 2 * (1 - a)) by simp [cubic]; ring]
          exact neg_neg_of_pos (by positivity)
        have hmix : a * cubic a b u (3 * a) =
            (a - b) * cubic a 0 u (3 * a) + b * cubic a a u (3 * a) := by
          simp [cubic]; ring
        apply neg_of_mul_neg_right (a := a) _ ha.le
        rw [hmix]
        exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hba) hbare.le)
          (mul_neg_of_pos_of_neg hb (principal a ha ha₁))
    · dsimp only [m]
      rw [max_eq_right hab]
      constructor
      · rw [show cubic a b u b =
          b * ((b - a) * (1 - b) * u ^ 2 + a * (1 + u) * (2 - b * (1 - u))) by
          simp [cubic]; ring]
        have h₁ : 0 ≤ (b - a) * (1 - b) * u ^ 2 :=
          mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (by positivity)) hu₂
        have h₂ : 0 < a * (1 + u) * (2 - b * (1 - u)) := by
          have hlt : b * (1 - u) < 2 := by nlinarith [mul_pos (sub_pos.mpr hb₁) (show 0 < 1 - u by positivity)]
          exact mul_pos (by positivity) (sub_pos.mpr hlt)
        exact mul_pos hb (by linarith)
      · have hbare : cubic 0 b u (3 * b) ≤ 0 := by
          rw [show cubic 0 b u (3 * b) =
            -(b ^ 2 * ((12 - 18 * b) * (1 - u ^ 2) + 9 * (1 - b) * u ^ 2)) by
            simp [cubic]; ring]
          have h : 0 ≤ (12 - 18 * b) * (1 - u ^ 2) :=
            mul_nonneg (by linarith) (sub_nonneg.mpr hu₂₁)
          exact neg_nonpos.mpr (mul_nonneg (sq_nonneg b) (add_nonneg h (by positivity)))
        have hmix : b * cubic a b u (3 * b) =
            (b - a) * cubic 0 b u (3 * b) + a * cubic b b u (3 * b) := by
          simp [cubic]; ring
        apply neg_of_mul_neg_right (a := b) _ hb.le
        rw [hmix]
        exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab) hbare)
          (mul_neg_of_pos_of_neg ha (principal b hb hb₁))
  refine ⟨h0, hm.1, hm.2, ?_, h4⟩
  rcases le_total 2 (3 * m) with h | h
  · rw [max_eq_right h]
    exact hm.2
  · rwa [max_eq_left h]

private theorem char_signs (k₁ k₂ s : ℝ) (hk₁ : 0 < k₁) (hk₁' : k₁ ^ 2 ≤ 2 / 3)
    (hk₂ : 0 < k₂) (hk₂' : k₂ ^ 2 ≤ 2 / 3) (hs : 0 < s) (hs' : s < 1) :
    let m := max (k₁ ^ 2) (k₂ ^ 2)
    let p := (gramWithRates k₁ k₂ s).charpoly
    p.eval 0 < 0 ∧ 0 < p.eval m ∧ p.eval (3 * m) < 0 ∧
      p.eval (max 2 (3 * m)) < 0 ∧ 0 < p.eval 4 := by
  intro m p
  have he (t : ℝ) : p.eval t = cubic (k₁ ^ 2) (k₂ ^ 2) (1 - s) t := by
    dsimp only [p]
    rw [char_eval_with_rates]
    simp [cubic]
    ring
  simp only [he]
  exact cubic_signs _ _ _ (by positivity) hk₁'
    (by positivity) hk₂' (by linarith) (by linarith)

private theorem squared_of_signs (G : Matrix (Fin 3) (Fin 3) ℝ) (bound : ℝ)
    (hbound : 0 < bound) (hbound₁ : bound < 1)
    (h0 : G.charpoly.eval 0 < 0) (h1 : 0 < G.charpoly.eval bound)
    (h3 : G.charpoly.eval (3 * bound) < 0)
    (hmax : G.charpoly.eval (max 2 (3 * bound)) < 0) (h4 : 0 < G.charpoly.eval 4) :
    ∃ x y z : ℝ, x ∈ Set.Ioo 0 bound ∧ y ∈ Set.Ioo bound (3 * bound) ∧
      z ∈ Set.Ioo (max 2 (3 * bound)) 4 ∧
      ∀ t : ℝ, t ∈ spectrum ℝ G ↔ t = x ∨ t = y ∨ t = z := by
  classical
  let p := G.charpoly
  have hmonic : p.Monic := Matrix.charpoly_monic _
  obtain ⟨x, hx, hx0⟩ := root_between p hbound h0 h1
  obtain ⟨y, hy, hy0⟩ := root_between (-p) (by linarith : bound < 3 * bound)
    (by simpa using h1) (by simpa using h3)
  have hy0' : p.eval y = 0 := by simpa using hy0
  obtain ⟨z, hz, hz0⟩ := root_between p (max_lt (by norm_num) (by linarith)) hmax h4
  have h3z := (le_max_right (2 : ℝ) (3 * bound)).trans_lt hz.1
  refine ⟨x, y, z, hx, hy, hz, fun t => ?_⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot]
  change p.eval t = 0 ↔ _
  constructor
  · intro ht
    by_contra! hn
    obtain ⟨htx, hty, htz⟩ := hn
    have hxy := (hx.2.trans hy.1).ne
    have hyz := (hy.2.trans h3z).ne
    have hxz := (hx.2.trans (hy.1.trans (hy.2.trans h3z))).ne
    have hcard : ({t, x, y, z} : Finset ℝ).card ≤ p.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro r hr
      rw [Finset.mem_val, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hr
      rw [Polynomial.mem_roots hmonic.ne_zero, Polynomial.IsRoot]
      rcases hr with h | h | h | h <;> subst r <;> assumption
    simp [htx, hty, htz, hxy, hyz, hxz, p] at hcard
  · rintro (rfl | rfl | rfl) <;> assumption

private theorem ordered_of_squared (G : Matrix (Fin 3) (Fin 3) ℝ) (k : ℝ) (hk : 0 < k)
    (hsquared : ∃ x y z : ℝ, x ∈ Set.Ioo 0 (k ^ 2) ∧ y ∈ Set.Ioo (k ^ 2) (3 * k ^ 2) ∧
      z ∈ Set.Ioo (max 2 (3 * k ^ 2)) 4 ∧
      ∀ t : ℝ, t ∈ spectrum ℝ G ↔ t = x ∨ t = y ∨ t = z) :
    ∃ m₁ m₂ m₃ : ℝ, 0 < m₁ ∧ m₁ < m₂ ∧ m₂ < m₃ ∧ m₂ / m₃ < Real.sqrt (3 / 2) * k ∧
      ∀ m : ℝ, 0 ≤ m → (m ^ 2 ∈ spectrum ℝ G ↔ m = m₁ ∨ m = m₂ ∨ m = m₃) := by
  obtain ⟨x, y, z, hx, hy, hz, hspec⟩ := hsquared
  have hxy := hx.2.trans hy.1
  have hyz := hy.2.trans ((le_max_right (2 : ℝ) (3 * k ^ 2)).trans_lt hz.1)
  have hz₂ : 2 < z := (le_max_left _ _).trans_lt hz.1
  have hratio : Real.sqrt y / Real.sqrt z < Real.sqrt (3 / 2) * k := by
    rw [div_lt_iff₀ (Real.sqrt_pos.2 (by linarith : 0 < z))]
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (hx.1.trans hxy).le, mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
      Real.sq_sqrt (by linarith : 0 ≤ z)]
    have hgap := mul_lt_mul_of_pos_left hz₂ (show 0 < (3 / 2) * k ^ 2 by positivity)
    linarith [hy.2]
  have root_eq (m u : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) :
      m ^ 2 = u ↔ m = Real.sqrt u := by
    conv_lhs => rhs; rw [← Real.sq_sqrt hu]
    exact sq_eq_sq₀ hm (Real.sqrt_nonneg _)
  refine ⟨Real.sqrt x, Real.sqrt y, Real.sqrt z, Real.sqrt_pos.2 hx.1,
    Real.sqrt_lt_sqrt hx.1.le hxy, Real.sqrt_lt_sqrt (hx.1.trans hxy).le hyz, hratio, ?_⟩
  intro m hm
  rw [hspec, root_eq _ _ hm hx.1.le, root_eq _ _ hm (hx.1.trans hxy).le,
    root_eq _ _ hm (hx.1.trans (hxy.trans hyz)).le]

/-- Three disjoint positive intervals isolate the entire squared mass spectrum. -/
theorem squared_spectrum_with_rates (k₁ k₂ s : ℝ)
    (hk₁ : 0 < k₁) (hk₁' : k₁ ^ 2 ≤ 2 / 3) (hk₂ : 0 < k₂) (hk₂' : k₂ ^ 2 ≤ 2 / 3)
    (hs : 0 < s) (hs₁ : s < 1) :
    let bound := max (k₁ ^ 2) (k₂ ^ 2)
    ∃ x y z : ℝ, x ∈ Set.Ioo 0 (bound) ∧ y ∈ Set.Ioo (bound) (3 * bound) ∧
      z ∈ Set.Ioo (max 2 (3 * bound)) 4 ∧
      ∀ t : ℝ, t ∈ spectrum ℝ (gramWithRates k₁ k₂ s) ↔ t = x ∨ t = y ∨ t = z := by
  intro bound
  have hbound : 0 < bound := (show 0 < k₁ ^ 2 by positivity).trans_le (le_max_left _ _)
  have hbound₁ : bound < 1 := max_lt (by linarith) (by linarith)
  obtain ⟨h0, h1, h3, hmax, h4⟩ := char_signs k₁ k₂ s hk₁ hk₁' hk₂ hk₂' hs hs₁
  exact squared_of_signs _ bound hbound hbound₁ h0 h1 h3 hmax h4

/-- The shifted Schur wire has exactly three distinct positive masses. The
middle-to-heavy ratio is uniformly bounded over the whole insertion interval. -/
theorem ordered_mass_spectrum_with_rates (k₁ k₂ s : ℝ)
    (hk₁ : 0 < k₁) (hk₁' : k₁ ^ 2 ≤ 2 / 3) (hk₂ : 0 < k₂) (hk₂' : k₂ ^ 2 ≤ 2 / 3)
    (hs : 0 < s) (hs₁ : s < 1) :
    ∃ m₁ m₂ m₃ : ℝ, 0 < m₁ ∧ m₁ < m₂ ∧ m₂ < m₃ ∧ m₂ / m₃ < Real.sqrt (3 / 2) * max k₁ k₂ ∧
      ∀ m : ℝ, 0 ≤ m → (m ^ 2 ∈ spectrum ℝ (gramWithRates k₁ k₂ s) ↔
        m = m₁ ∨ m = m₂ ∨ m = m₃) := by
  apply ordered_of_squared _ _ (hk₁.trans_le (le_max_left _ _))
  have hsq : (max k₁ k₂) ^ 2 = max (k₁ ^ 2) (k₂ ^ 2) := by
    rcases le_total k₂ k₁ with h | h
    · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ hk₂.le h 2)]
    · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ hk₁.le h 2)]
  simpa only [hsq] using squared_spectrum_with_rates k₁ k₂ s hk₁ hk₁' hk₂ hk₂' hs hs₁

private theorem equal_rate_signs (k s : ℝ) (hk : 0 < k) (hk₁ : k < 1)
    (hs : 0 < s) (hs₁ : s < 1) :
    let p := (gram k s).charpoly
    p.eval 0 < 0 ∧ 0 < p.eval (k ^ 2) ∧ p.eval (3 * k ^ 2) < 0 ∧
      p.eval (max 2 (3 * k ^ 2)) < 0 ∧ 0 < p.eval 4 := by
  intro p
  have hk2 : 0 < k ^ 2 := by positivity
  have hk2₁ : k ^ 2 < 1 := by nlinarith [mul_pos hk (sub_pos.mpr hk₁)]
  have hs2₁ : s ^ 2 < 1 := by nlinarith [mul_pos hs (sub_pos.mpr hs₁)]
  have hδ : 0 < s * (2 - s) := mul_pos hs (by linarith)
  have hδ₁ : s * (2 - s) ≤ 1 := by nlinarith [sq_nonneg (1 - s)]
  have hsmall : s * (2 - s) * k ^ 2 < 1 :=
    (mul_lt_mul_of_pos_left hk2₁ hδ).trans_le (by simpa using hδ₁)
  have hshift : ∀ t : ℝ, p.eval t = t * (t - 3 * k ^ 2) * (t - (2 + k ^ 2)) +
      s * (2 - s) * k ^ 2 * t * (t - (1 + 2 * k ^ 2)) - k ^ 4 * s ^ 2 := by
    intro t
    dsimp only [p]
    rw [char_eval]
    ring
  have h3 : p.eval (3 * k ^ 2) < 0 := by
    rw [hshift]
    have hterm : s * (2 - s) * k ^ 2 * (3 * k ^ 2) *
        (3 * k ^ 2 - (1 + 2 * k ^ 2)) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (by linarith)
    have hsub : 0 ≤ k ^ 4 * s ^ 2 := by positivity
    simp only [sub_self, mul_zero, zero_mul, zero_add]
    linarith
  refine ⟨?_, ?_, h3, ?_, ?_⟩
  · rw [hshift]
    simp only [zero_mul, mul_zero, add_zero, zero_sub, neg_lt_zero]
    positivity
  · rw [hshift, show k ^ 2 * (k ^ 2 - 3 * k ^ 2) * (k ^ 2 - (2 + k ^ 2)) +
      s * (2 - s) * k ^ 2 * k ^ 2 * (k ^ 2 - (1 + 2 * k ^ 2)) - k ^ 4 * s ^ 2 =
        k ^ 4 * (4 - 2 * s - s * (2 - s) * k ^ 2) by ring]
    exact mul_pos (by positivity) (by linarith)
  · rcases le_total 2 (3 * k ^ 2) with h | h
    · rwa [max_eq_right h]
    · rw [max_eq_left h, hshift]
      have hneg : 0 < k ^ 4 * s ^ 2 := by positivity
      rw [show (2 : ℝ) - (2 + k ^ 2) = -k ^ 2 by ring,
        show (2 : ℝ) - (1 + 2 * k ^ 2) = 1 - 2 * k ^ 2 by ring]
      by_cases hterm : 0 ≤ 1 - 2 * k ^ 2
      · have hbound := mul_le_mul_of_nonneg_right hδ₁
          (show 0 ≤ k ^ 2 * 2 * (1 - 2 * k ^ 2) by positivity)
        have hgap : 0 < (2 * k ^ 2) * (1 - k ^ 2) := mul_pos (by positivity) (by linarith)
        nlinarith only [hbound, hgap, hneg]
      · have hbase : 0 ≤ 2 * (2 - 3 * k ^ 2) * k ^ 2 := by positivity
        have hpert : s * (2 - s) * k ^ 2 * 2 * (1 - 2 * k ^ 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hterm)
        linarith
  · rw [hshift]
    have hterm : 0 ≤ s * (2 - s) * k ^ 2 * 4 * (4 - (1 + 2 * k ^ 2)) :=
      mul_nonneg (by positivity) (by linarith)
    have hsub : k ^ 4 * s ^ 2 < 1 := by
      calc
        k ^ 4 * s ^ 2 ≤ 1 * s ^ 2 := by
          gcongr
          nlinarith [mul_pos hk2 (sub_pos.mpr hk2₁)]
        _ < 1 := by simpa using hs2₁
    have hbase : (4 : ℝ) ≤ 4 * (4 - 3 * k ^ 2) * (4 - (2 + k ^ 2)) := by
      calc
        (4 : ℝ) = 4 * 1 * 1 := by norm_num
        _ ≤ _ := by gcongr <;> linarith
    linarith

/-- Three disjoint positive intervals isolate the entire squared mass spectrum. -/
theorem squared_spectrum (k s : ℝ) (hk : 0 < k) (hk₁ : k < 1)
    (hs : 0 < s) (hs₁ : s < 1) :
    ∃ x y z : ℝ, x ∈ Set.Ioo 0 (k ^ 2) ∧ y ∈ Set.Ioo (k ^ 2) (3 * k ^ 2) ∧
      z ∈ Set.Ioo (max 2 (3 * k ^ 2)) 4 ∧
      ∀ t : ℝ, t ∈ spectrum ℝ (gram k s) ↔ t = x ∨ t = y ∨ t = z := by
  have hk₂ : 0 < k ^ 2 := by positivity
  have hk₂₁ : k ^ 2 < 1 := by nlinarith [mul_pos hk (sub_pos.mpr hk₁)]
  obtain ⟨h0, h1, h3, hmax, h4⟩ := equal_rate_signs k s hk hk₁ hs hs₁
  exact squared_of_signs _ _ hk₂ hk₂₁ h0 h1 h3 hmax h4

/-- The shifted Schur wire has exactly three distinct positive masses. The
middle-to-heavy ratio is uniformly bounded over the whole insertion interval. -/
theorem ordered_mass_spectrum (k s : ℝ) (hk : 0 < k) (hk₁ : k < 1)
    (hs : 0 < s) (hs₁ : s < 1) :
    ∃ m₁ m₂ m₃ : ℝ, 0 < m₁ ∧ m₁ < m₂ ∧ m₂ < m₃ ∧ m₂ / m₃ < Real.sqrt (3 / 2) * k ∧
      ∀ m : ℝ, 0 ≤ m → (m ^ 2 ∈ spectrum ℝ (gram k s) ↔
        m = m₁ ∨ m = m₂ ∨ m = m₃) := by
  exact ordered_of_squared _ _ hk (squared_spectrum k s hk hk₁ hs hs₁)

end PMAction.WireShiftedSpectrum
