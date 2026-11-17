import PMElementaryParticles.MuonLifetimeCorrected

/-!
# The muon lifetime with the full Fermi-theory QED series (van Ritbergen–Stuart)

`MuonLifetimeCorrected` keeps the one-loop factor at `α(0)` with a massless electron. The relation
the measured `G_F` is defined by (van Ritbergen and Stuart, hep-ph/9904240, eqs. 2.4–2.9; MuLan,
arXiv:1211.0960) is

  `1/τ_μ = (G_F² m_μ⁵ / 192π³) (1 + Δq⁽⁰⁾ + Δq⁽¹⁾ + Δq⁽²⁾)`,

* `Δq⁽⁰⁾ = f(r) − 1`, the massive-electron phase space (`MassiveWidth.phase`, derived);
* `Δq⁽¹⁾ = (α_r/π)(25/8 − π²/2 − (34 + 12 ln r) r + 16π² r^{3/2})`, the one-loop term with its
  electron-mass corrections (supplied);
* `Δq⁽²⁾ = 6.700 (α_r/π)²`, the two-loop term including the hadronic and tau loops (supplied);
* `α_r⁻¹ = α⁻¹ − (2/3π) ln(m_μ/m_e)`, the coupling at the muon scale (eq. 3.3 without the `W`-loop
  term, which the `G_F` definition omits; `α_r⁻¹ ≈ 135.90`).

Everything is evaluated at E8 inputs: `G_F`, `m_μ/m_e`, `α = 1/geometricIndex`. The series is the
supplied part; the Fermi-theory corrections are finite to all orders (`MuonRadiativeLog`: no log).

* `log_muon_bounds`: `5.3315 < ln(m_μ/m_e) < 5.3317`.
* `alphaR_div_pi_bounds`, `dq1_bounds`, `dq2_bounds`.
* `lifetime_bounds`: `2.196974 µs < τ_μ < 2.196984 µs` (measured `2.1969811(22)`).
-/

noncomputable section
namespace PMElementaryParticles.MuonLifetimeHigherOrder

open PMElementaryParticles MuonLifetimeCorrected

def logMuon : ℝ := Real.log LeptonMasses.muon

/-- `α_r = α(m_μ)` with `α = 1/geometricIndex`. -/
def alphaR : ℝ := 1 / (PMSubstrate.geometricIndex - 2 / (3 * Real.pi) * logMuon)

def dq0 : ℝ := phaseFactor - 1

def dq1 : ℝ := alphaR / Real.pi *
  (25 / 8 - Real.pi ^ 2 / 2 - (34 + 12 * Real.log r) * r + 16 * Real.pi ^ 2 * r * Real.sqrt r)

def dq2 : ℝ := 6.700 * (alphaR / Real.pi) ^ 2

def lifetime : ℝ := PhysicalUnits.muonLifetimeSeconds / (1 + dq0 + dq1 + dq2)

lemma exp_lower : Real.exp 5.3315 < 206.7682716 := by
  have hsplit : Real.exp 5.3315 = Real.exp 1 ^ 5 * Real.exp 0.3315 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have h5 : Real.exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  have hx := Real.exp_bound' (x := (0.3315 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
  have hx2 : Real.exp 0.3315 ≤ 1.393057 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at hx; linarith
  rw [hsplit]
  calc Real.exp 1 ^ 5 * Real.exp 0.3315 < (2.7182818286 : ℝ) ^ 5 * 1.393057 :=
        mul_lt_mul h5 hx2 (Real.exp_pos _) (by positivity)
    _ < 206.7682716 := by norm_num

lemma exp_upper : (206.7682718 : ℝ) < Real.exp 5.3317 := by
  have hsplit : Real.exp 5.3317 = Real.exp 1 ^ 5 * Real.exp 0.3317 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_gt_d9
  have h5 : (2.7182818283 : ℝ) ^ 5 < Real.exp 1 ^ 5 :=
    pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  have hx := Real.sum_le_exp_of_nonneg (x := (0.3317 : ℝ)) (by norm_num) 10
  have hx2 : (1.393334 : ℝ) ≤ Real.exp 0.3317 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at hx; linarith
  rw [hsplit]
  calc (206.7682718 : ℝ) < (2.7182818283 : ℝ) ^ 5 * 1.393334 := by norm_num
    _ < Real.exp 1 ^ 5 * Real.exp 0.3317 := mul_lt_mul h5 hx2 (by norm_num) (by positivity)

theorem log_muon_bounds : (5.3315 : ℝ) < logMuon ∧ logMuon < 5.3317 := by
  have hm := LeptonMasses.muon_value
  have hpos : (0 : ℝ) < LeptonMasses.muon := by linarith [hm.1]
  unfold logMuon
  constructor
  · rw [Real.lt_log_iff_exp_lt hpos]; linarith [exp_lower, hm.1]
  · rw [Real.log_lt_iff_lt_exp hpos]; linarith [exp_upper, hm.2]

lemma log_r_eq : Real.log r = -2 * logMuon := by
  have hm := LeptonMasses.muon_value
  have hpos : (0 : ℝ) < LeptonMasses.muon := by linarith [hm.1]
  unfold r logMuon
  rw [one_div, Real.log_inv, Real.log_pow]; push_cast; ring

lemma pi_lo : (3.14159265358979 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
lemma pi_hi : Real.pi < (3.1415926535898 : ℝ) := by linarith [Real.pi_lt_d20]

theorem den_bounds : (135.904577 : ℝ) < PMSubstrate.geometricIndex - 2 / (3 * Real.pi) * logMuon ∧
    PMSubstrate.geometricIndex - 2 / (3 * Real.pi) * logMuon < 135.904620 := by
  have hg := PMSubstrate.geometricIndex_bounds
  have hl := log_muon_bounds
  have hp1 := pi_lo; have hp2 := pi_hi
  have hc1 : (2 / (3 * 3.1415926535898) : ℝ) < 2 / (3 * Real.pi) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)
  have hc2 : 2 / (3 * Real.pi) < (2 / (3 * 3.14159265358979) : ℝ) := by
    apply div_lt_div_of_pos_left (by norm_num) (by norm_num) (by linarith)
  have hcpos : (0 : ℝ) < 2 / (3 * Real.pi) := by positivity
  have hm1 : 2 / (3 * Real.pi) * logMuon < (2 / (3 * 3.14159265358979) : ℝ) * 5.3317 :=
    mul_lt_mul'' hc2 hl.2 hcpos.le (by linarith [hl.1])
  have hm2 : (2 / (3 * 3.1415926535898) : ℝ) * 5.3315 < 2 / (3 * Real.pi) * logMuon :=
    mul_lt_mul'' hc1 hl.1 (by norm_num) (by norm_num)
  constructor
  · have : (135.904577 : ℝ) < 137.035999212381397211 - (2 / (3 * 3.14159265358979) : ℝ) * 5.3317 := by
      norm_num
    linarith [hg.1]
  · have : (137.035999212381397213 : ℝ) - (2 / (3 * 3.1415926535898) : ℝ) * 5.3315 < 135.904620 := by
      norm_num
    linarith [hg.2]

theorem alphaR_div_pi_bounds :
    (0.0023421564 : ℝ) < alphaR / Real.pi ∧ alphaR / Real.pi < 0.0023421573 := by
  obtain ⟨d1, d2⟩ := den_bounds
  have hp1 := pi_lo; have hp2 := pi_hi
  have hdpos : (0 : ℝ) < PMSubstrate.geometricIndex - 2 / (3 * Real.pi) * logMuon := by linarith
  unfold alphaR
  rw [div_div]
  have hpos : (0 : ℝ) < (PMSubstrate.geometricIndex - 2 / (3 * Real.pi) * logMuon) * Real.pi :=
    mul_pos hdpos Real.pi_pos
  constructor
  · rw [lt_div_iff₀ hpos]
    have := mul_lt_mul'' d2 hp2 hdpos.le Real.pi_pos.le
    nlinarith
  · rw [div_lt_iff₀ hpos]
    have := mul_lt_mul'' d1 hp1 (by norm_num) (by norm_num)
    nlinarith

lemma sqrt_r_bounds : (0.0048 : ℝ) < Real.sqrt r ∧ Real.sqrt r < 0.0049 := by
  have hr := r_bounds
  constructor
  · rw [show (0.0048 : ℝ) = Real.sqrt (0.0048 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by nlinarith [hr.1])
  · rw [show (0.0049 : ℝ) = Real.sqrt (0.0049 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by linarith [hr.1]) (by nlinarith [hr.2])

theorem bracket_bounds :
    (-1.8075880 : ℝ) <
      25 / 8 - Real.pi ^ 2 / 2 - (34 + 12 * Real.log r) * r + 16 * Real.pi ^ 2 * r * Real.sqrt r ∧
    25 / 8 - Real.pi ^ 2 / 2 - (34 + 12 * Real.log r) * r + 16 * Real.pi ^ 2 * r * Real.sqrt r <
      -1.8075860 := by
  have hr := r_bounds
  have hl := log_muon_bounds
  have hs := sqrt_r_bounds
  have hp1 := pi_lo; have hp2 := pi_hi
  rw [log_r_eq]
  have hpp1 : (3.14159265358979 : ℝ) ^ 2 < Real.pi ^ 2 := pow_lt_pow_left₀ hp1 (by norm_num) (by norm_num)
  have hpp2 : Real.pi ^ 2 < (3.1415926535898 : ℝ) ^ 2 := pow_lt_pow_left₀ hp2 Real.pi_pos.le (by norm_num)
  have hrs1 : (2.339010677e-5 : ℝ) * 0.0048 < r * Real.sqrt r := mul_lt_mul'' hr.1 hs.1 (by norm_num) (by norm_num)
  have hrs2 : r * Real.sqrt r < (2.339010682e-5 : ℝ) * 0.0049 :=
    mul_lt_mul'' hr.2 hs.2 (by linarith [hr.1]) (Real.sqrt_nonneg _)
  have hrspos : 0 < r * Real.sqrt r := lt_trans (by norm_num) hrs1
  have hk1 : (34 + 12 * (-2 * 5.3317) : ℝ) < 34 + 12 * (-2 * logMuon) := by linarith [hl.2]
  have hk2 : 34 + 12 * (-2 * logMuon) < (34 + 12 * (-2 * 5.3315) : ℝ) := by linarith [hl.1]
  have hq1 : (34 + 12 * (-2 * logMuon)) * r < (34 + 12 * (-2 * 5.3315) : ℝ) * 2.339010677e-5 := by
    nlinarith [hr.1, hr.2]
  have hq2 : (34 + 12 * (-2 * 5.3317) : ℝ) * 2.339010682e-5 < (34 + 12 * (-2 * logMuon)) * r := by
    nlinarith [hr.1, hr.2]
  have ht1 : (16 * 3.14159265358979 ^ 2 * (2.339010677e-5 * 0.0048) : ℝ) < 16 * Real.pi ^ 2 * r * Real.sqrt r := by
    have := mul_lt_mul'' hpp1 hrs1 (by norm_num) (by norm_num)
    nlinarith
  have ht2 : 16 * Real.pi ^ 2 * r * Real.sqrt r < (16 * 3.1415926535898 ^ 2 * (2.339010682e-5 * 0.0049) : ℝ) := by
    have := mul_lt_mul'' hpp2 hrs2 (by positivity) hrspos.le
    nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem dq1_bounds : (-4.233657e-3 : ℝ) < dq1 ∧ dq1 < -4.233648e-3 := by
  obtain ⟨a1, a2⟩ := alphaR_div_pi_bounds
  obtain ⟨b1, b2⟩ := bracket_bounds
  unfold dq1
  set A := alphaR / Real.pi
  set B := 25 / 8 - Real.pi ^ 2 / 2 - (34 + 12 * Real.log r) * r + 16 * Real.pi ^ 2 * r * Real.sqrt r
  have hA : 0 < A := lt_trans (by norm_num) a1
  have e1 : A * B - 0.0023421573 * (-1.8075880) = A * (B - (-1.8075880)) + (-1.8075880) * (A - 0.0023421573) := by ring
  have e2 : A * B - 0.0023421564 * (-1.8075860) = A * (B - (-1.8075860)) + (-1.8075860) * (A - 0.0023421564) := by ring
  have p1 : 0 < A * (B - (-1.8075880)) := mul_pos hA (by linarith)
  have p2 : 0 < (-1.8075880 : ℝ) * (A - 0.0023421573) := mul_pos_of_neg_of_neg (by norm_num) (by linarith)
  have n1 : A * (B - (-1.8075860)) < 0 := mul_neg_of_pos_of_neg hA (by linarith)
  have n2 : (-1.8075860 : ℝ) * (A - 0.0023421564) < 0 := mul_neg_of_neg_of_pos (by norm_num) (by linarith)
  constructor
  · have : (-4.233657e-3 : ℝ) < 0.0023421573 * (-1.8075880) := by norm_num
    linarith
  · have : (0.0023421564 : ℝ) * (-1.8075860) < -4.233648e-3 := by norm_num
    linarith

theorem dq2_bounds : (3.6754e-5 : ℝ) < dq2 ∧ dq2 < 3.6755e-5 := by
  obtain ⟨a1, a2⟩ := alphaR_div_pi_bounds
  unfold dq2
  set A := alphaR / Real.pi
  constructor <;> nlinarith

theorem dq0_bounds : (-1.8706e-4 : ℝ) < dq0 ∧ dq0 < -1.8704e-4 := by
  have h := phase_bounds
  unfold dq0
  constructor <;> linarith [h.1, h.2]

theorem lifetime_bounds : (2.196974e-6 : ℝ) < lifetime ∧ lifetime < (2.196984e-6 : ℝ) := by
  have ht := PhysicalUnits.muonLifetimeSeconds_tight
  obtain ⟨p1, p2⟩ := dq0_bounds
  obtain ⟨q1, q2⟩ := dq1_bounds
  obtain ⟨s1, s2⟩ := dq2_bounds
  have hd1 : (0.995616037 : ℝ) < 1 + dq0 + dq1 + dq2 := by linarith
  have hd2 : 1 + dq0 + dq1 + dq2 < (0.995616067 : ℝ) := by linarith
  have hdpos : 0 < 1 + dq0 + dq1 + dq2 := by linarith
  unfold lifetime
  constructor
  · rw [lt_div_iff₀ hdpos]
    calc (2.196974e-6 : ℝ) * (1 + dq0 + dq1 + dq2) < 2.196974e-6 * 0.995616067 := by nlinarith
      _ < 2.187343e-6 := by norm_num
      _ < _ := ht.1
  · rw [div_lt_iff₀ hdpos]
    calc PhysicalUnits.muonLifetimeSeconds < 2.187352e-6 := ht.2
      _ < 2.196984e-6 * 0.995616037 := by norm_num
      _ < _ := by nlinarith

end PMElementaryParticles.MuonLifetimeHigherOrder
