import PMElementaryParticles.MassiveWidth
import PMElementaryParticles.MassiveVolume
import PMElementaryParticles.MassivePair

/-!
# Tree contact spectrum in the pair invariant `q²`

The existing spectrum is in the charged daughter's energy. The affine
change of variable to `q²` gives a positive Jacobian `1/(2m)` after
reversing the endpoints. The weighted substitution lets a later virtual
kernel depend on the pair invariant while retaining the tree normalization.
For massive spectators the same invariant fixes their shell volume and
the open window. The boosted tensor gives a contact weight with all final
masses retained as inputs.
-/

noncomputable section
namespace PMElementaryParticles.PairInvariantSpectrum

open MassiveDaughterSpectrum (endpoint width kinematics)
open scoped Interval
open Matrix
open PairIsotropy (AngularAverage)
open PairIsotropy.AngularAverage (restMomentum)

def invariant (m μ E : ℝ) : ℝ := 2 * m * (endpoint m μ - E)

def energyAt (m μ s : ℝ) : ℝ := endpoint m μ - s / (2 * m)

theorem invariant_eq (m μ E : ℝ) (hm : m ≠ 0) :
    invariant m μ E = m ^ 2 + μ ^ 2 - 2 * m * E := by
  unfold invariant endpoint
  field_simp

theorem invariant_mdot (m μ E P : ℝ) (hm : m ≠ 0) (hP : P ^ 2 = E ^ 2 - μ ^ 2) :
    let p : Fin 4 → ℝ := ![m, 0, 0, 0]
    let pe : Fin 4 → ℝ := ![E, P, 0, 0]
    MuonRate.mdot (p - pe) (p - pe) = invariant m μ E := by
  rw [invariant_eq m μ E hm]
  exact (kinematics m μ E P hP).2

theorem invariant_energyAt (m μ s : ℝ) (hm : m ≠ 0) :
    invariant m μ (energyAt m μ s) = s := by
  unfold invariant energyAt
  field_simp
  ring

theorem invariant_range_iff (m μ E : ℝ) (hm : 0 < m) :
    (0 ≤ invariant m μ E ∧ invariant m μ E ≤ (m - μ) ^ 2) ↔
      μ ≤ E ∧ E ≤ endpoint m μ := by
  have hden : 0 < 2 * m := by positivity
  have hmax : invariant m μ μ = (m - μ) ^ 2 := by
    rw [invariant_eq m μ μ hm.ne']
    ring
  rw [← hmax, invariant, invariant]
  constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨by linarith [(mul_le_mul_iff_right₀ hden).mp h₁],
      sub_nonneg.mp (nonneg_of_mul_nonneg_right h₀ hden)⟩
  · rintro ⟨h₀, h₁⟩
    exact ⟨mul_nonneg hden.le (sub_nonneg.mpr h₁),
      mul_le_mul_of_nonneg_left (sub_le_sub_left h₀ _) hden.le⟩

/-- In the parent rest frame, the recoiling daughter has positive momentum
and the spectator pair has positive internal rest momentum precisely on this
open invariant-mass interval. The pair energy in the parent frame is positive. -/
theorem massive_pair_window (m μ m₁ m₂ s : ℝ) (hm : 0 < m) (hμ : 0 ≤ μ) (hμm : μ < m)
    (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) :
    (μ < energyAt m μ s ∧ energyAt m μ s < m ∧
      ∃ P : ℝ, 0 < P ∧ MassiveVolume.Q m₁ m₂ P = Real.sqrt s) ↔
      (m₁ + m₂) ^ 2 < s ∧ s < (m - μ) ^ 2 := by
  have hden : 0 < 2 * m := by positivity
  have hE : μ < energyAt m μ s ↔ s < (m - μ) ^ 2 := by
    have hg := MassiveDaughterSpectrum.endpoint_gap m μ hm.ne'
    unfold energyAt
    constructor
    · intro h
      have h' : s / (2 * m) < (m - μ) ^ 2 / (2 * m) := by linarith
      exact (div_lt_div_iff_of_pos_right hden).mp h'
    · intro h
      have h' := (div_lt_div_iff_of_pos_right hden).mpr h
      linarith
  have hpair : m₁ + m₂ < Real.sqrt s ↔ (m₁ + m₂) ^ 2 < s := by
    constructor
    · intro h
      have hs := Real.sqrt_pos.mp (lt_of_le_of_lt (add_nonneg h₁ h₂) h)
      calc
        (m₁ + m₂) ^ 2 < (Real.sqrt s) ^ 2 := sq_lt_sq' (by linarith [Real.sqrt_pos.mpr hs]) h
        _ = s := Real.sq_sqrt hs.le
    · intro h
      rw [← Real.sqrt_sq (add_nonneg h₁ h₂)]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) h
  rw [hE, MassiveVolume.exists_pos_momentum_iff _ _ _ h₁ h₂, hpair]
  constructor
  · rintro ⟨hhi, -, hlo⟩
    exact ⟨hlo, hhi⟩
  · rintro ⟨hlo, hhi⟩
    have hs : 0 < s := lt_of_le_of_lt (sq_nonneg _) hlo
    have hEm : energyAt m μ s < m := by
      unfold energyAt
      linarith [(MassiveDaughterSpectrum.threshold m μ hm hμ hμm).2, div_pos hs hden]
    exact ⟨hhi, hEm, hlo⟩

/-- There is an interior rest-frame configuration precisely when the parent
mass exceeds the sum of the three final masses. Equality gives no open window. -/
theorem massive_channel_open_iff (m μ m₁ m₂ : ℝ) (hm : 0 < m) (hμ : 0 ≤ μ)
    (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) :
    (∃ s : ℝ, μ < energyAt m μ s ∧ energyAt m μ s < m ∧
        ∃ P : ℝ, 0 < P ∧ MassiveVolume.Q m₁ m₂ P = Real.sqrt s) ↔
      μ + m₁ + m₂ < m := by
  constructor
  · rintro ⟨s, hE, hEm, hP⟩
    have hμm := hE.trans hEm
    obtain ⟨hlo, hhi⟩ := (massive_pair_window m μ m₁ m₂ s hm hμ hμm h₁ h₂).mp
      ⟨hE, hEm, hP⟩
    have h := Real.sqrt_lt_sqrt (sq_nonneg _) (hlo.trans hhi)
    rw [Real.sqrt_sq (add_nonneg h₁ h₂), Real.sqrt_sq (sub_nonneg.mpr hμm.le)] at h
    linarith
  · intro h
    have hμm : μ < m := by linarith
    have hsq : (m₁ + m₂) ^ 2 < (m - μ) ^ 2 := by
      apply sq_lt_sq'
      · linarith
      · linarith
    let s := ((m₁ + m₂) ^ 2 + (m - μ) ^ 2) / 2
    refine ⟨s, (massive_pair_window m μ m₁ m₂ s hm hμ hμm h₁ h₂).mpr ?_⟩
    dsimp [s]
    exact ⟨by linarith, by linarith⟩

/-- The two-body shell volume at total pair energy `Q`. -/
def pairVolume (m₁ m₂ Q : ℝ) : ℝ :=
  (1 / (8 * Real.pi)) * (2 * MassiveVolume.momentumAt m₁ m₂ Q / Q)

/-- Contact spectrum per unit recoil-daughter energy, with both spectator
masses retained. Use the spectrum on the open physical shell. -/
def massiveContactRate (G m μ m₁ m₂ E : ℝ) : ℝ :=
  let Q := Real.sqrt (invariant m μ E)
  let P := MassiveVolume.momentumAt m₁ m₂ Q
  let p : Fin 4 → ℝ := ![m, 0, 0, 0]
  let pe : Fin 4 → ℝ := ![E, MassiveDaughterSpectrum.momentum μ E, 0, 0]
  let q := p - pe
  1 / (2 * m) * (MassiveDaughterSpectrum.momentum μ E / (4 * Real.pi ^ 2)) *
    (64 * G ^ 2 * (pairVolume m₁ m₂ Q * (P ^ 2 / 3) * MuonRate.mdot pe p +
      pairVolume m₁ m₂ Q *
        ((MassiveVolume.E m₁ P * MassiveVolume.E m₂ P - P ^ 2 / 3) / Q ^ 2) *
        MuonRate.mdot pe q * MuonRate.mdot p q))

/-- The spectrum is the boosted on-shell angular contraction times the recoil
measure and flux. The average is normalized to the derived pair shell volume. -/
theorem massive_contact_density {Ω : Type*} (A : AngularAverage Ω)
    (G m μ m₁ m₂ s : ℝ) (hm : 0 < m) (hμ : 0 ≤ μ) (hμm : μ < m)
    (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (hlo : (m₁ + m₂) ^ 2 < s)
    (hhi : s < (m - μ) ^ 2) (hΦ : A.volume = pairVolume m₁ m₂ (Real.sqrt s)) :
    let E := energyAt m μ s
    let Q := Real.sqrt s
    let P := MassiveVolume.momentumAt m₁ m₂ Q
    let p : Fin 4 → ℝ := ![m, 0, 0, 0]
    let pe : Fin 4 → ℝ := ![E, MassiveDaughterSpectrum.momentum μ E, 0, 0]
    let q := p - pe
    ∃ Λ, PairTransport.IsLorentz Λ ∧
      (∀ ω, Λ *ᵥ MassivePair.left A (MassiveVolume.E m₁ P) P ω +
        Λ *ᵥ MassivePair.right A (MassiveVolume.E m₂ P) (-P) ω = q) ∧
      1 / (2 * m) * (MassiveDaughterSpectrum.momentum μ E / (4 * Real.pi ^ 2)) *
        (64 * G ^ 2 * A.average (fun ω =>
          MuonRate.mdot pe (Λ *ᵥ MassivePair.left A (MassiveVolume.E m₁ P) P ω) *
          MuonRate.mdot p (Λ *ᵥ MassivePair.right A (MassiveVolume.E m₂ P) (-P) ω))) =
        massiveContactRate G m μ m₁ m₂ E := by
  intro E Q P p pe q
  obtain ⟨hE, hEm, r, hr, hQr⟩ :=
    (massive_pair_window m μ m₁ m₂ s hm hμ hμm h₁ h₂).mpr ⟨hlo, hhi⟩
  have hQ : MassiveVolume.E m₁ P + MassiveVolume.E m₂ P = Q := by
    change MassiveVolume.Q m₁ m₂ (MassiveVolume.momentumAt m₁ m₂ (Real.sqrt s)) =
      Real.sqrt s
    rw [← hQr, MassiveVolume.momentumAt_Q _ _ _ hr]
  have hP := MassiveDaughterSpectrum.momentum_shell μ E (by nlinarith [hE, hμ])
  have hq : MuonRate.mdot q q = s := by
    rw [invariant_mdot m μ E _ hm.ne' hP, invariant_energyAt _ _ _ hm.ne']
  have hs : 0 < s := lt_of_le_of_lt (sq_nonneg _) hlo
  have hq0 : 0 < q 0 := by change 0 < m - E; linarith
  obtain ⟨Λ, hΛ, hboost⟩ := PairTransport.boost_to q hq0 (by rw [hq]; exact hs)
  rw [hq] at hboost
  refine ⟨Λ, hΛ, ?_, ?_⟩
  · intro ω
    rw [← Matrix.mulVec_add]
    have hrest : MassivePair.left A (MassiveVolume.E m₁ P) P ω +
        MassivePair.right A (MassiveVolume.E m₂ P) (-P) ω = restMomentum Q := by
      funext i
      fin_cases i <;> simp [MassivePair.left, MassivePair.right, restMomentum, ← hQ]
    rw [hrest]
    exact hboost
  · rw [MassivePair.pair_contraction A hΛ _ _ _ (hQ.trans_ne (Real.sqrt_pos.mpr hs).ne') p pe,
      hQ, hboost, hΦ, massiveContactRate, invariant_energyAt _ _ _ hm.ne']

/-- Two massless spectators recover the existing differential contact rate
on the physical interior, including its normalization. -/
theorem massiveContactRate_massless_pair (G m μ E : ℝ)
    (hm : 0 < m) (hμ : 0 ≤ μ) (hE : μ < E) (hEnd : E < endpoint m μ) :
    massiveContactRate G m μ 0 0 E = MassiveDaughterSpectrum.rate G m μ E := by
  let Q := Real.sqrt (invariant m μ E)
  have hs : 0 < invariant m μ E := by
    unfold invariant
    exact mul_pos (by positivity) (sub_pos.mpr hEnd)
  have hQ : 0 < Q := Real.sqrt_pos.mpr hs
  have hQsq : Q ^ 2 = invariant m μ E := Real.sq_sqrt hs.le
  have hR : MassiveVolume.momentumAt 0 0 Q = Q / 2 := by
    have he : (Q ^ 2 + 0 ^ 2 - 0 ^ 2) / (2 * Q) = Q / 2 := by
      field_simp [hQ.ne']
      ring
    unfold MassiveVolume.momentumAt
    rw [he]
    simpa using Real.sqrt_sq (show 0 ≤ Q / 2 by positivity)
  have hEa : MassiveVolume.E 0 (Q / 2) = Q / 2 := by
    simp [MassiveVolume.E, Real.sqrt_sq (show 0 ≤ Q / 2 by positivity)]
  have hΦ : pairVolume 0 0 Q = 1 / (8 * Real.pi) := by
    unfold pairVolume
    rw [hR]
    field_simp [hQ.ne']
  have hP := MassiveDaughterSpectrum.momentum_shell μ E (by nlinarith [hμ, hE])
  have hkin := invariant_mdot m μ E _ hm.ne' hP
  simp only at hkin
  have h₁ : pairVolume 0 0 Q * ((Q / 2) ^ 2 / 3) =
      (1 / (96 * Real.pi)) * invariant m μ E := by
    rw [hΦ, ← hQsq]
    ring
  have h₂ : pairVolume 0 0 Q * ((Q / 2 * (Q / 2) - (Q / 2) ^ 2 / 3) / Q ^ 2) =
      2 / (96 * Real.pi) := by
    rw [hΦ]
    field_simp [hQ.ne', Real.pi_ne_zero]
    ring
  dsimp only [massiveContactRate]
  rw [hR, hEa, h₁, h₂, ← hkin]
  have hc := MassiveDaughterSpectrum.rest_contraction G m μ E _ hP
  dsimp only at hc
  rw [mul_right_comm (1 / (96 * Real.pi))] at hc
  rw [hc]
  exact MassiveDaughterSpectrum.density G m μ E hm.ne'

/-- Integrated contact weight over the physical window; a closed channel has
zero weight. The integrand is already angularly averaged. -/
def massiveContactWidth (G m μ m₁ m₂ : ℝ) : ℝ :=
  if μ + m₁ + m₂ < m then
    ∫ E in μ..energyAt m μ ((m₁ + m₂) ^ 2), massiveContactRate G m μ m₁ m₂ E
  else 0

/-- The integrated weight agrees exactly with the earlier two-massless-spectator
width. The endpoint with zero pair invariant is an almost-everywhere exception. -/
theorem massiveContactWidth_massless_pair (G m μ : ℝ) (hμ : 0 ≤ μ) (hOpen : μ < m) :
    massiveContactWidth G m μ 0 0 = width G m μ := by
  have hm : 0 < m := hμ.trans_lt hOpen
  have hEnd := (MassiveDaughterSpectrum.threshold m μ hm hμ hOpen).1
  simp [massiveContactWidth, width, energyAt, hOpen]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.volume.ae_ne (endpoint m μ)] with E hE hi
  rw [Set.uIoc_of_le hEnd.le] at hi
  exact massiveContactRate_massless_pair G m μ E hm hμ hi.1 (lt_of_le_of_ne hi.2 hE)

/-- With a positive sum of spectator masses, the contact kernel is continuous
on its closed integration interval, including the collapsed-momentum ends. -/
theorem massiveContactRate_integrable (G m μ m₁ m₂ : ℝ) (hm : 0 < m)
    (hpair : 0 < m₁ + m₂) (hOpen : μ + m₁ + m₂ < m) :
    IntervalIntegrable (massiveContactRate G m μ m₁ m₂) MeasureTheory.volume
      μ (energyAt m μ ((m₁ + m₂) ^ 2)) := by
  have hμm : μ < m := by linarith
  have hhi : (m₁ + m₂) ^ 2 < (m - μ) ^ 2 := by
    apply sq_lt_sq' <;> linarith
  have hden : 0 < 2 * m := by positivity
  have hEnd : μ ≤ energyAt m μ ((m₁ + m₂) ^ 2) := by
    have hg := MassiveDaughterSpectrum.endpoint_gap m μ hm.ne'
    have hh := (div_lt_div_iff_of_pos_right hden).mpr hhi
    unfold energyAt
    linarith
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hEnd]
  intro E hE
  apply ContinuousAt.continuousWithinAt
  have hInv : (m₁ + m₂) ^ 2 ≤ invariant m μ E := by
    calc
      (m₁ + m₂) ^ 2 = invariant m μ (energyAt m μ ((m₁ + m₂) ^ 2)) :=
        (invariant_energyAt m μ _ hm.ne').symm
      _ ≤ invariant m μ E :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left hE.2 _) hden.le
  have hQ : 0 < Real.sqrt (invariant m μ E) :=
    Real.sqrt_pos.mpr ((sq_pos_of_pos hpair).trans_le hInv)
  unfold massiveContactRate pairVolume MassiveVolume.momentumAt MassiveVolume.E
    MassiveDaughterSpectrum.momentum invariant MuonRate.mdot
  simp only [Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  fun_prop (disch := first | exact hQ.ne' | positivity)

/-- Tree density per unit pair mass squared. -/
def rate (G m μ s : ℝ) : ℝ :=
  MassiveDaughterSpectrum.rate G m μ (energyAt m μ s) / (2 * m)

theorem weighted_integral (G m μ : ℝ) (hm : 0 < m) (w : ℝ → ℝ) :
    (∫ s in (0 : ℝ)..(m - μ) ^ 2, w s * rate G m μ s) =
      ∫ E in μ..endpoint m μ, w (invariant m μ E) * MassiveDaughterSpectrum.rate G m μ E := by
  let f := fun E => w (invariant m μ E) * MassiveDaughterSpectrum.rate G m μ E
  have h := intervalIntegral.inv_smul_integral_comp_sub_div
    (a := (0 : ℝ)) (b := (m - μ) ^ 2) f (2 * m) (endpoint m μ)
  have hlo : endpoint m μ - (m - μ) ^ 2 / (2 * m) = μ := by
    rw [← MassiveDaughterSpectrum.endpoint_gap m μ hm.ne']
    ring
  rw [hlo, zero_div, sub_zero] at h
  calc
    (∫ s in (0 : ℝ)..(m - μ) ^ 2, w s * rate G m μ s) =
        ∫ s in (0 : ℝ)..(m - μ) ^ 2, f (energyAt m μ s) / (2 * m) := by
      apply intervalIntegral.integral_congr
      intro s _
      simp [f, rate, invariant_energyAt m μ s hm.ne', mul_div_assoc]
    _ = (2 * m)⁻¹ • ∫ s in (0 : ℝ)..(m - μ) ^ 2, f (energyAt m μ s) := by
      rw [intervalIntegral.integral_div, div_eq_mul_inv, smul_eq_mul, mul_comm]
    _ = ∫ E in μ..endpoint m μ, w (invariant m μ E) * MassiveDaughterSpectrum.rate G m μ E := h

theorem integrated_rate (G m μ : ℝ) (hm : 0 < m) (hμ : 0 ≤ μ) (hμm : μ ≤ m) :
    (∫ s in (0 : ℝ)..(m - μ) ^ 2, rate G m μ s) =
      G ^ 2 * m ^ 5 / (192 * Real.pi ^ 3) * MassiveWidth.phase ((μ / m) ^ 2) := by
  have h : (∫ s in (0 : ℝ)..(m - μ) ^ 2, rate G m μ s) = width G m μ := by
    simpa [width] using weighted_integral G m μ hm (fun _ => 1)
  rw [h, MassiveWidth.closed_width G m μ hm hμ hμm]

/-- With a massless daughter, the normalized invariant `z = q²/m²` has
weight `2(1−z)²(1+2z)` times the tree width. -/
theorem massless_normalized_rate (G m z : ℝ) (hm : 0 < m) (hz : z ≤ 1) :
    m ^ 2 * rate G m 0 (m ^ 2 * z) =
      (G ^ 2 * m ^ 5 / (192 * Real.pi ^ 3)) * (2 * (1 - z) ^ 2 * (1 + 2 * z)) := by
  have he : energyAt m 0 (m ^ 2 * z) = m * (1 - z) / 2 := by
    unfold energyAt endpoint
    field_simp
    ring
  rw [rate, he, MassiveDaughterSpectrum.massless G m _
    (div_nonneg (mul_nonneg hm.le (sub_nonneg.mpr hz)) (by norm_num))]
  calc
    m ^ 2 * (MuonRate.rate G m (m * (1 - z) / 2) / (2 * m)) =
        MuonRate.rate G m (m * (1 - z) / 2) * (m / 2) := by
      field_simp
    _ = _ := by rw [MuonRate.spectrum_form]; unfold MassScaling.spectrum; ring

end PMElementaryParticles.PairInvariantSpectrum
