import PMAction.PolarizationGapSizes
import PMAction.PolarizationShellQ

/-!
# Step (c) of the subtracted lattice polarization: the pointwise bound

The lattice integrand with unit probes `e_μ`, `e_ν` (`latInt`) is `PolarizationAssembly.Lfull` with
the orders of `PolarizationOrders` and the remainders `leg − (l₀ + l₁ + l₂)`, … (`latInt_eq`). At `−q`
the first orders change sign and the second do not (`l1_neg`, `s1_neg`, `l2_neg`, `s2_neg`,
`c2_neg`), so `latInt` at `−q` is `Lfull` with the signs `second_difference` expects
(`latInt_neg`); at `q = 0` it is `L₀` (`latInt_zero`).

* `R_side`: the third-order rest at `q` is at most `P(1) n(q)³/n(k)⁵` (`cubic_bound`, `cubic_shell`).
* `pointwise`: with `κ = n(k)`, `t = n(q)`, under the shell conditions (`t ≤ κ`, `a κ ≤ 1`, the
  bounds on `S(k)`, `S(k ± q)`, `|k|²` and `|S(k) − |k|²|`),
  `|L(q) + L(−q) − 2L(0) − 2 Q_cont| ≤ 2 K a² t²/κ² + 2 P(1) t³/κ⁵`, where `Q_cont` is the
  continuum's second order (`Q` at `S = |k|²`, `2k_μ`, `q_μ`, `2k·q`, `q·q`).

Step (d) derives the shell conditions from the Euclidean window and integrates.
-/

noncomputable section
namespace PMAction.PolarizationPointwise
open Real D4Gauge LeadingLog PolarizationContact PolarizationSplit PolarizationOrders
  PolarizationMagnitudes PolarizationGapSizes PolarizationAssembly PolarizationCubic
  PolarizationShellCubic PolarizationShellQ

/-- The unit probe along `μ`. -/
def e (μ : Fin 4) : Fin 4 → ℝ := fun i => if i = μ then 1 else 0

lemma n1_e (μ : Fin 4) : n1 (e μ) = 1 := by
  unfold n1 e; fin_cases μ <;> simp [Fin.sum_univ_four]

lemma dot_e (μ : Fin 4) (w : Fin 4 → ℝ) : PolarizationOrders.dot (e μ) w = w μ := by
  unfold PolarizationOrders.dot e; fin_cases μ <;> simp

lemma abs_le_n1 (w : Fin 4 → ℝ) (μ : Fin 4) : |w μ| ≤ n1 w :=
  Finset.single_le_sum (f := fun i => |w i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ μ)

lemma dot_le (w z : Fin 4 → ℝ) : |PolarizationOrders.dot w z| ≤ n1 w * n1 z := by
  unfold PolarizationOrders.dot
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [n1, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_le_n1 z i) (abs_nonneg _)

lemma n1_neg (q : Fin 4 → ℝ) : n1 (-q) = n1 q := by simp [n1]

lemma rk_neg (r : Fin 4 → Fin 3) (q : Fin 4 → ℝ) : rk r (-q) = -rk r q := by
  simp [rk, Finset.sum_neg_distrib]

lemma l1_neg (a : ℝ) (k q u : Fin 4 → ℝ) : l1 a k (-q) u = -l1 a k q u := by
  unfold l1; rw [← neg_div, ← Finset.sum_neg_distrib]; congr 1
  exact Finset.sum_congr rfl fun r _ => by rw [rk_neg]; ring

lemma l2_neg (a : ℝ) (k q u : Fin 4 → ℝ) : l2 a k (-q) u = l2 a k q u := by
  unfold l2; congr 1; exact Finset.sum_congr rfl fun r _ => by rw [rk_neg]; ring

lemma s1_neg (a : ℝ) (k q : Fin 4 → ℝ) : s1 a k (-q) = -s1 a k q := by
  unfold s1; rw [← neg_div, ← Finset.sum_neg_distrib]; congr 1
  exact Finset.sum_congr rfl fun r _ => by rw [rk_neg]; ring

lemma s2_neg (a : ℝ) (k q : Fin 4 → ℝ) : s2 a k (-q) = s2 a k q := by
  unfold s2; congr 1; exact Finset.sum_congr rfl fun r _ => by rw [rk_neg]; ring

lemma c2_neg (a : ℝ) (k q u v : Fin 4 → ℝ) : c2 a k (-q) u v = c2 a k q u v := by
  unfold c2; congr 1; exact Finset.sum_congr rfl fun r _ => by rw [rk_neg]; ring

lemma leg_zero (a : ℝ) (k u : Fin 4 → ℝ) : leg a k 0 u 1 = l0 a k u := by
  unfold leg l0; congr 1
  exact Finset.sum_congr rfl fun r _ => by simp [rk, Real.sinc_zero]

lemma contact_zero (a : ℝ) (k u v : Fin 4 → ℝ) : contact a k 0 u v = c0 a k u v := by
  unfold contact c0; congr 1
  exact Finset.sum_congr rfl fun r _ => by simp [rk, Real.sinc_zero]; ring

/-- The lattice polarization integrand with unit probes. -/
def latInt (a : ℝ) (q : Fin 4 → ℝ) (μ ν : Fin 4) (k : Fin 4 → ℝ) : ℝ :=
  leg a k q (e μ) 1 * leg a k q (e ν) 1 / (symbol a k * symbol a (k + q)) -
    contact a k q (e μ) (e ν) / symbol a k

theorem latInt_eq (a : ℝ) (q : Fin 4 → ℝ) (μ ν : Fin 4) (k : Fin 4 → ℝ) :
    latInt a q μ ν k = Lfull (symbol a k) (l0 a k (e μ)) (l1 a k q (e μ)) (l2 a k q (e μ))
      (leg a k q (e μ) 1 - (l0 a k (e μ) + l1 a k q (e μ) + l2 a k q (e μ)))
      (l0 a k (e ν)) (l1 a k q (e ν)) (l2 a k q (e ν))
      (leg a k q (e ν) 1 - (l0 a k (e ν) + l1 a k q (e ν) + l2 a k q (e ν)))
      (s1 a k q) (s2 a k q) (symbol a (k + q) - symbol a k - (s1 a k q + s2 a k q))
      (c0 a k (e μ) (e ν)) (c2 a k q (e μ) (e ν))
      (contact a k q (e μ) (e ν) - (c0 a k (e μ) (e ν) + c2 a k q (e μ) (e ν))) := by
  unfold latInt Lfull
  rw [show symbol a k + (s1 a k q + s2 a k q + (symbol a (k + q) - symbol a k -
      (s1 a k q + s2 a k q))) = symbol a (k + q) by ring]
  ring

theorem latInt_neg (a : ℝ) (q : Fin 4 → ℝ) (μ ν : Fin 4) (k : Fin 4 → ℝ) :
    latInt a (-q) μ ν k = Lfull (symbol a k) (l0 a k (e μ)) (-l1 a k q (e μ)) (l2 a k q (e μ))
      (leg a k (-q) (e μ) 1 - (l0 a k (e μ) + -l1 a k q (e μ) + l2 a k q (e μ)))
      (l0 a k (e ν)) (-l1 a k q (e ν)) (l2 a k q (e ν))
      (leg a k (-q) (e ν) 1 - (l0 a k (e ν) + -l1 a k q (e ν) + l2 a k q (e ν)))
      (-s1 a k q) (s2 a k q) (symbol a (k + -q) - symbol a k - (-s1 a k q + s2 a k q))
      (c0 a k (e μ) (e ν)) (c2 a k q (e μ) (e ν))
      (contact a k (-q) (e μ) (e ν) - (c0 a k (e μ) (e ν) + c2 a k q (e μ) (e ν))) := by
  rw [latInt_eq, l1_neg, l1_neg, l2_neg, l2_neg, s1_neg, s2_neg, c2_neg]

theorem latInt_zero (a : ℝ) (μ ν : Fin 4) (k : Fin 4 → ℝ) :
    latInt a 0 μ ν k = L0 (symbol a k) (l0 a k (e μ)) (l0 a k (e ν)) (c0 a k (e μ) (e ν)) := by
  unfold latInt L0
  rw [add_zero, leg_zero, leg_zero, contact_zero]
  ring

/-! ## The rest at one side -/

lemma a_le {a κ : ℝ} (hκ : 0 < κ) (haκ : a * κ ≤ 1) : a ≤ 1 / κ := by
  rw [le_div_iff₀ hκ]; exact haκ

lemma a2_le {a κ : ℝ} (ha : 0 < a) (hκ : 0 < κ) (haκ : a * κ ≤ 1) : a ^ 2 ≤ 1 / κ ^ 2 := by
  rw [le_div_iff₀ (by positivity), ← mul_pow]
  exact pow_le_one₀ (by positivity) haκ

lemma a3_le {a κ : ℝ} (ha : 0 < a) (hκ : 0 < κ) (haκ : a * κ ≤ 1) : a ^ 3 ≤ 1 / κ ^ 3 := by
  rw [le_div_iff₀ (by positivity), ← mul_pow]
  exact pow_le_one₀ (by positivity) haκ

theorem R_side {a : ℝ} {k q : Fin 4 → ℝ} (μ ν : Fin 4) (ha : 0 < a) (hκ : 0 < n1 k)
    (ht : n1 q ≤ n1 k) (haκ : a * n1 k ≤ 1) (hS : n1 k ^ 2 / 8 ≤ symbol a k)
    (hSq : n1 k ^ 2 / 16 ≤ symbol a (k + q)) :
    |R (symbol a k) (l0 a k (e μ)) (l1 a k q (e μ)) (l2 a k q (e μ))
      (leg a k q (e μ) 1 - (l0 a k (e μ) + l1 a k q (e μ) + l2 a k q (e μ)))
      (l0 a k (e ν)) (l1 a k q (e ν)) (l2 a k q (e ν))
      (leg a k q (e ν) 1 - (l0 a k (e ν) + l1 a k q (e ν) + l2 a k q (e ν)))
      (s1 a k q) (s2 a k q) (symbol a (k + q) - symbol a k - (s1 a k q + s2 a k q))
      (contact a k q (e μ) (e ν) - (c0 a k (e μ) (e ν) + c2 a k q (e μ) (e ν)))| ≤
      47979504985 / 36 * n1 q ^ 3 / n1 k ^ 5 := by
  have ht0 := n1_nonneg q
  have hκ' : n1 k ≠ 0 := hκ.ne'
  have hx : ∀ r ∈ roots, |a * rk r q / 2| ≤ 1 := fun r _ => (hx_le ha r q).trans (by
    have : a * n1 q ≤ a * n1 k := mul_le_mul_of_nonneg_left ht ha.le
    linarith)
  have h1a := a_le hκ haκ
  have h2a := a2_le ha hκ haκ
  have h3a := a3_le ha hκ haκ
  -- the orders of one leg
  have leg_bounds : ∀ u : Fin 4, |l0 a k (e u)| ≤ 4 * n1 k ∧ |l1 a k q (e u)| ≤ 2 * n1 q ∧
      |l2 a k q (e u)| ≤ 2 / 3 / n1 k * n1 q ^ 2 ∧
      |leg a k q (e u) 1 - (l0 a k (e u) + l1 a k q (e u) + l2 a k q (e u))| ≤
        1 / (4 * n1 k ^ 2) * n1 q ^ 3 := by
    intro u
    refine ⟨(l0_le ha k (e u)).trans (le_of_eq (by rw [n1_e]; ring)),
      (l1_le ha k q (e u)).trans (le_of_eq (by rw [n1_e]; ring)), ?_, ?_⟩
    · refine (l2_le ha k q (e u)).trans ?_
      rw [n1_e]
      calc 2 / 3 * a ^ 2 * 1 * n1 q ^ 2 * n1 k = 2 / 3 * n1 q ^ 2 * (a ^ 2 * n1 k) := by ring
        _ ≤ 2 / 3 * n1 q ^ 2 * (1 / n1 k ^ 2 * n1 k) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2a hκ.le) (by positivity)
        _ = 2 / 3 / n1 k * n1 q ^ 2 := by field_simp; try ring
    · have h := leg_split ha k q (e u) hx
      rw [legExp_eq] at h
      refine h.trans ((legE_le ha q (e u)).trans ?_)
      rw [n1_e]
      calc a ^ 2 * 1 * n1 q ^ 3 / 4 = n1 q ^ 3 / 4 * a ^ 2 := by ring
        _ ≤ n1 q ^ 3 / 4 * (1 / n1 k ^ 2) := mul_le_mul_of_nonneg_left h2a (by positivity)
        _ = 1 / (4 * n1 k ^ 2) * n1 q ^ 3 := by field_simp; try ring
  obtain ⟨p0b, p1b, p2b, peb⟩ := leg_bounds μ
  obtain ⟨v0b, v1b, v2b, veb⟩ := leg_bounds ν
  have d1b : |s1 a k q| ≤ 4 * n1 k * n1 q := (s1_le ha k q).trans (le_of_eq (by ring))
  have d2b : |s2 a k q| ≤ 2 * n1 q ^ 2 := s2_le ha k q
  have deb : |symbol a (k + q) - symbol a k - (s1 a k q + s2 a k q)| ≤ 3 / 2 / n1 k * n1 q ^ 3 := by
    have h := dS_split ha k q hx
    rw [dSExp_eq] at h
    refine h.trans ((dSE_le ha q).trans ?_)
    calc 3 / 2 * a * n1 q ^ 3 = 3 / 2 * n1 q ^ 3 * a := by ring
      _ ≤ 3 / 2 * n1 q ^ 3 * (1 / n1 k) := mul_le_mul_of_nonneg_left h1a (by positivity)
      _ = 3 / 2 / n1 k * n1 q ^ 3 := by field_simp; try ring
  have ceb : |contact a k q (e μ) (e ν) - (c0 a k (e μ) (e ν) + c2 a k q (e μ) (e ν))| ≤
      1 / (32 * n1 k ^ 3) * n1 q ^ 3 := by
    have h := contact_split a k q (e μ) (e ν) hx
    rw [contactExp_eq] at h
    refine h.trans ((cE_le ha q (e μ) (e ν)).trans ?_)
    rw [n1_e, n1_e]
    calc a ^ 3 * 1 * 1 * n1 q ^ 3 / 32 = n1 q ^ 3 / 32 * a ^ 3 := by ring
      _ ≤ n1 q ^ 3 / 32 * (1 / n1 k ^ 3) := mul_le_mul_of_nonneg_left h3a (by positivity)
      _ = 1 / (32 * n1 k ^ 3) * n1 q ^ 3 := by field_simp; try ring
  have hSD : n1 k ^ 2 / 8 / 2 ≤ symbol a k + (s1 a k q + s2 a k q +
      (symbol a (k + q) - symbol a k - (s1 a k q + s2 a k q))) := by
    rw [show symbol a k + (s1 a k q + s2 a k q + (symbol a (k + q) - symbol a k -
      (s1 a k q + s2 a k q))) = symbol a (k + q) by ring]
    linarith
  unfold R
  exact (cubic_bound (div_pos (pow_pos hκ 2) (by norm_num)) hS hSD p0b p1b p2b peb v0b v1b v2b veb
    (d1b.trans (le_of_eq (by ring))) d2b deb ceb).trans (cubic_shell hκ ht0 ht)

/-! ## The pointwise bound -/

theorem pointwise {a : ℝ} {k q : Fin 4 → ℝ} (μ ν : Fin 4) (ha : 0 < a) (hκ : 0 < n1 k)
    (ht : n1 q ≤ n1 k) (haκ : a * n1 k ≤ 1) (hS : n1 k ^ 2 / 8 ≤ symbol a k)
    (hSle : symbol a k ≤ n1 k ^ 2) (hSq : n1 k ^ 2 / 16 ≤ symbol a (k + q))
    (hSmq : n1 k ^ 2 / 16 ≤ symbol a (k + -q)) (hSc : n1 k ^ 2 / 8 ≤ sq4 k)
    (hScle : sq4 k ≤ n1 k ^ 2) (hdS : |symbol a k - sq4 k| ≤ a ^ 2 * n1 k ^ 4 / 12) :
    |latInt a q μ ν k + latInt a (-q) μ ν k - 2 * latInt a 0 μ ν k -
        2 * Q (sq4 k) (2 * k μ) (q μ) 0 (2 * k ν) (q ν) 0 (2 * PolarizationOrders.dot q k)
          (PolarizationOrders.dot q q) 0| ≤
      2 * (271853128 / 3 * a ^ 2 * n1 q ^ 2 / n1 k ^ 2) +
        2 * (47979504985 / 36 * n1 q ^ 3 / n1 k ^ 5) := by
  have hk2 : 0 < n1 k ^ 2 := pow_pos hκ 2
  have hS0 : 0 < symbol a k := by linarith
  have hSDq : symbol a k + (s1 a k q + s2 a k q + (symbol a (k + q) - symbol a k -
      (s1 a k q + s2 a k q))) ≠ 0 := by
    rw [show symbol a k + (s1 a k q + s2 a k q + (symbol a (k + q) - symbol a k -
      (s1 a k q + s2 a k q))) = symbol a (k + q) by ring]
    linarith
  have hSDm : symbol a k + (-s1 a k q + s2 a k q + (symbol a (k + -q) - symbol a k -
      (-s1 a k q + s2 a k q))) ≠ 0 := by
    rw [show symbol a k + (-s1 a k q + s2 a k q + (symbol a (k + -q) - symbol a k -
      (-s1 a k q + s2 a k q))) = symbol a (k + -q) by ring]
    linarith
  rw [latInt_eq, latInt_neg, latInt_zero, second_difference _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hS0.ne' hSDq hSDm]
  -- the two rests
  have hR := R_side μ ν ha hκ ht haκ hS hSq
  have hR' := R_side (q := -q) μ ν ha hκ (by rw [n1_neg]; exact ht) haκ hS hSmq
  rw [l1_neg, l1_neg, l2_neg, l2_neg, s1_neg, s2_neg, c2_neg, n1_neg] at hR'
  -- the second order against the continuum's
  have he0 : ∀ u : Fin 4, |l0 a k (e u) - 2 * k u| ≤ 2 / 3 * a ^ 2 * n1 k ^ 3 := fun u => by
    have h := l0_close ha k (e u); rw [dot_e, n1_e] at h; exact h.trans (le_of_eq (by ring))
  have hp0 : ∀ u : Fin 4, |l0 a k (e u)| ≤ 4 * n1 k := fun u =>
    (l0_le ha k (e u)).trans (le_of_eq (by rw [n1_e]; ring))
  have hP0 : ∀ u : Fin 4, |2 * k u| ≤ 2 * n1 k := fun u => by
    rw [abs_mul, abs_two]; linarith [abs_le_n1 k u]
  have he1 : ∀ u : Fin 4, |l1 a k q (e u) - q u| ≤ a ^ 2 * n1 k ^ 2 * n1 q := fun u => by
    have h := l1_close ha k q (e u); rw [dot_e, n1_e] at h; exact h.trans (le_of_eq (by ring))
  have hp2 : ∀ u : Fin 4, |l2 a k q (e u)| ≤ 2 / 3 * a ^ 2 * n1 k * n1 q ^ 2 := fun u =>
    (l2_le ha k q (e u)).trans (le_of_eq (by rw [n1_e]; ring))
  have hD1 : |2 * PolarizationOrders.dot q k| ≤ 2 * n1 k * n1 q := by
    rw [abs_mul, abs_two]
    have := dot_le q k
    calc 2 * |PolarizationOrders.dot q k| ≤ 2 * (n1 q * n1 k) := by linarith
      _ = 2 * n1 k * n1 q := by ring
  have hD2 : |PolarizationOrders.dot q q| ≤ n1 q ^ 2 := (dot_le q q).trans (le_of_eq (by ring))
  have hc2 : |c2 a k q (e μ) (e ν)| ≤ a ^ 2 * n1 q ^ 2 / 3 :=
    (c2_le ha k q (e μ) (e ν)).trans (le_of_eq (by rw [n1_e, n1_e]; ring))
  have hM : |symbol a k| ≤ n1 k ^ 2 := by rw [abs_of_pos hS0]; exact hSle
  have hMc : |sq4 k| ≤ n1 k ^ 2 := by rw [abs_of_nonneg (by linarith)]; exact hScle
  have hQ := Q_shell (a := a) (κ := n1 k) (t := n1 q) (S := symbol a k) (Sc := sq4 k) (p0 := l0 a k (e μ)) (p1 := l1 a k q (e μ))
    (p2 := l2 a k q (e μ)) (v0 := l0 a k (e ν)) (v1 := l1 a k q (e ν)) (v2 := l2 a k q (e ν))
    (d1 := s1 a k q) (d2 := s2 a k q) (c2 := c2 a k q (e μ) (e ν)) (P0 := 2 * k μ) (P1 := q μ)
    (V0 := 2 * k ν) (V1 := q ν) (D1 := 2 * PolarizationOrders.dot q k)
    (D2 := PolarizationOrders.dot q q) ha hκ hS hSc hM hMc hdS
    (hp0 := hp0 μ) (hP0 := hP0 μ) (he0 := he0 μ) (hv0 := hp0 ν) (hV0 := hP0 ν) (hf0 := he0 ν)
    (hP1 := abs_le_n1 q μ) (he1 := he1 μ)
    (hv1 := (l1_le ha k q (e ν)).trans (le_of_eq (by rw [n1_e]; ring)))
    (hV1 := abs_le_n1 q ν) (hf1v := he1 ν) (hp2 := hp2 μ) (hv2 := hp2 ν)
    (hd1 := (s1_le ha k q).trans (le_of_eq (by ring)))
    (hD1 := hD1) (hg1 := s1_close ha k q) (hd2 := s2_le ha k q) (hD2 := hD2)
    (hg2 := s2_close ha k q) (hc2 := hc2)
  have := abs_le.1 hQ; have := abs_le.1 hR; have := abs_le.1 hR'
  exact abs_le.2 ⟨by linarith, by linarith⟩

end PMAction.PolarizationPointwise
