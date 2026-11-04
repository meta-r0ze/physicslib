import PMConstants.ReadoutAccounting

/-!
# Which generator normalization the gauge ledgers price

`ReadoutAccounting` showed that, under the selected preparation, the W mass reads the ledgers as
effective stiffness. This module identifies what that reading means for the generators, and
tests the natural internal candidate, the packet's own trace form.

A refresh ledger `L` fixes the stiffness of a sector's **unit** generator `X`. If the
conventional generator is `G = μ X`, its coupling is `g² = 1/(c L μ²)` (`gsq`). Two choices of
unit:

* **Trace form.** Every unit generator has the same packet trace. Since the conventional
  weak `T₃` and `Y/2` have packet traces `2` and `10/3` (`PacketTraceForm`), `μ² ∝ 2, 10/3`.
  The hypercharge unit is `√(3/5)·Y/2`, which has the weak trace (`trace_unit_hyper`).
  This is the normalization of a unified group, and with equal ledgers it gives the familiar
  `s = 3/8` (`unification_value`). With the actual ledgers it gives exactly the raw value
  `5547/37777` (`trace_form_gives_raw`, equal to `GaugeTraceNormalization.rawMixing`).
* **Charge units.** The unit generators are the conventional ones, `T₃ = ±1/2` on the
  doublet and `Y/2` fixed by `Q = T₃ + Y/2` with integer lepton charge (the carrier charges of
  `CarrierRepresentation.charges_from_carriers`), so `μ = 1`. This gives the manuscript value
  `1849/8295` (`charge_units_give_effective`).

`normalization_decided`: with the measured `m_Z`, the trace-form normalization puts the W mass
more than `289σ` above the direct average, while the charge-unit normalization lies within
`1.3σ`. So the substrate's own trace form is **not** the normalization of the gauge
stiffness; the charge quanta are. The vacuum is not normalized as a unified group: the 3/5 that
unification would introduce is absent.

The two normalizations also differ in how the conserved electric charge is assembled. On the
packet `Q = T₃ + Y/2` (`electron_charge` gives the electron `−1`). It is the plain sum of the
unit generators exactly in charge units (`plain_sum_iff`). In trace-form units it is not
(`trace_units_not_plain_sum`). So the selected normalization is the one in which every sector's
unit contributes to the conserved charge with coefficient one, one currency for charge.

What remains is a derivation, from the event law, that refresh stiffness is counted per unit of
that conserved charge rather than per unit of the packet trace form.
-/

noncomputable section
namespace PMConstants.GeneratorNormalization
open PMConstants Matrix PacketTraceForm

/-- Coupling of the conventional generator `G = μ X` when the ledger `L` fixes the stiffness of
the unit generator `X` (with `μsq = μ²`). -/
def gsq (c L μsq : ℝ) : ℝ := 1 / (c * L * μsq)

/-- Weak fraction `g'²/(g² + g'²)`. -/
def mixing (c LW LY μW μY : ℝ) : ℝ := gsq c LY μY / (gsq c LW μW + gsq c LY μY)

theorem mixing_eq {c LW LY μW μY : ℝ} (hc : 0 < c) (hW : 0 < LW) (hY : 0 < LY)
    (hμW : 0 < μW) (hμY : 0 < μY) :
    mixing c LW LY μW μY = μW * LW / (μW * LW + μY * LY) := by
  unfold mixing gsq; field_simp; ring

lemma footprint_sub : (0 : ℝ) < footprint - 43 := by norm_num [footprint, overhead]

/-- **The trace form gives the raw value.** -/
theorem trace_form_gives_raw {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) :
    mixing c 43 (footprint - 43) (2 / τ) ((10 / 3) / τ) = 5547 / 37777 ∧
      mixing c 43 (footprint - 43) (2 / τ) ((10 / 3) / τ) =
        GaugeTraceNormalization.rawMixing c := by
  have h : mixing c 43 (footprint - 43) (2 / τ) ((10 / 3) / τ) = 5547 / 37777 := by
    rw [mixing_eq hc (by norm_num) footprint_sub (by positivity) (by positivity)]
    field_simp
    norm_num [footprint, overhead]
  exact ⟨h, h.trans (GaugeTraceNormalization.raw_mixing_exact hc).symm⟩

/-- **Charge units give the manuscript value.** -/
theorem charge_units_give_effective {c : ℝ} (hc : 0 < c) :
    mixing c 43 (footprint - 43) 1 1 = clockRatio := by
  rw [mixing_eq hc (by norm_num) footprint_sub one_pos one_pos]
  simp [clockRatio]

/-- The trace normalization is that of a unified group: equal ledgers give `3/8`. -/
theorem unification_value {c τ L : ℝ} (hc : 0 < c) (hτ : 0 < τ) (hL : 0 < L) :
    mixing c L L (2 / τ) ((10 / 3) / τ) = 3 / 8 := by
  rw [mixing_eq hc hL hL (by positivity) (by positivity)]
  field_simp; ring

/-- The trace-form hypercharge unit `√(3/5)·Y/2` has the weak packet trace `2`. -/
theorem trace_unit_hyper :
    (((Real.sqrt (3 / 5) : ℂ) • hyperGen) * ((Real.sqrt (3 / 5) : ℂ) • hyperGen)).trace = 2 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul, hyper_trace_square, smul_eq_mul,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; norm_num

/-- The conventional weak generator `T₃ = diag(1/2, −1/2)` has packet trace `2`. -/
theorem weak_unit_trace :
    (weakGen !![(1 / 2 : ℂ), 0; 0, -1 / 2] * weakGen !![(1 / 2 : ℂ), 0; 0, -1 / 2]).trace = 2 := by
  rw [weak_trace_product]
  simp [Matrix.trace_fin_two]
  norm_num

/-- **The W mass decides the normalization.** With the selected preparation and measured `m_Z`,
the trace-form normalization is excluded by more than `289σ`; charge units lie within `1.3σ`. -/
theorem normalization_decided {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) {c τ : ℝ}
    (hc : 0 < c) (hτ : 0 < τ) :
    mixing c 43 (footprint - 43) (2 / τ) ((10 / 3) / τ) = 5547 / 37777 ∧
      289 < WMassTest.pull 80.3692 0.0133 (ReadoutAccounting.rawWMass mZ) ∧
      mixing c 43 (footprint - 43) 1 1 = clockRatio ∧
      WMassTest.pull 80.3692 0.0133 (WMassTest.wMass mZ) < 1.3 :=
  ⟨(trace_form_gives_raw hc hτ).1, ReadoutAccounting.raw_excluded h,
    charge_units_give_effective hc, (WMassTest.pull_world h).2⟩

/-! ## One currency for charge

The two normalizations differ in how the conserved electric charge is built from the unit
generators. On the packet `Q = T₃ + Y/2` (`electron_charge`). In charge units `Q` is the plain
sum of the two unit generators; in trace-form units it is `X_W + √(5/3) X_Y`. -/

/-- The conventional weak generator `T₃` on the packet. -/
def t3 : PacketGaugeActions.M := weakGen !![(1 / 2 : ℂ), 0; 0, -1 / 2]

/-- The right-handed electron and a left-handed quark carrier. -/
def eR : PacketGaugeActions.Channels := .inr (.inr (.inr 1))
def qL : PacketGaugeActions.Channels := .inl (0, 0)

lemma t3_eR : t3 eR eR = 0 := by
  simp [t3, eR, weakGen, PacketGaugeActions.block]
lemma hyper_eR : hyperGen eR eR = -1 := by
  simp [hyperGen, PacketGaugeActions.charge, eR, PacketGaugeActions.block]
lemma t3_qL : t3 qL qL = 1 / 2 := by
  simp [t3, qL, weakGen, PacketGaugeActions.block]
lemma hyper_qL : hyperGen qL qL = 1 / 6 := by
  simp [hyperGen, PacketGaugeActions.charge, qL, PacketGaugeActions.block]; norm_num

/-- The electron has charge `−1` under `Q = T₃ + Y/2`. -/
theorem electron_charge : (t3 + hyperGen) eR eR = -1 := by
  rw [Matrix.add_apply, t3_eR, hyper_eR, zero_add]

/-- **Plain-sum criterion.** Writing `Q = kW • T₃ + kY • (Y/2)` reproduces the packet's electric
charge exactly when `kW = kY = 1`. -/
theorem plain_sum_iff (kW kY : ℂ) :
    t3 + hyperGen = kW • t3 + kY • hyperGen ↔ kW = 1 ∧ kY = 1 := by
  constructor
  · intro h
    have he := congrFun (congrFun h eR) eR
    have hq := congrFun (congrFun h qL) qL
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, t3_eR, hyper_eR, t3_qL,
      hyper_qL] at he hq
    have hY : kY = 1 := by linear_combination he
    subst hY
    refine ⟨?_, rfl⟩
    linear_combination -2 * hq
  · rintro ⟨rfl, rfl⟩; simp

/-- In trace-form units the conserved charge is not the plain sum of the unit generators: the
unit generators are `T₃/√μ_W` and `(Y/2)/√μ_Y` with `μ_Y/μ_W = 5/3`, so the coefficients
`√μ_W, √μ_Y` cannot both be one. -/
theorem trace_units_not_plain_sum {τ : ℝ} (hτ : 0 < τ) :
    ¬ (Real.sqrt (2 / τ) = 1 ∧ Real.sqrt ((10 / 3) / τ) = 1) := by
  rintro ⟨h1, h2⟩
  have e1 : 2 / τ = 1 := by
    have := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / τ); rw [h1] at this; linarith
  have e2 : (10 / 3) / τ = 1 := by
    have := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (10 / 3) / τ); rw [h2] at this; linarith
  rw [div_eq_one_iff_eq hτ.ne'] at e1 e2
  linarith

end PMConstants.GeneratorNormalization
