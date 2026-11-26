import PMElementaryParticles.FinalChannels
import PMElementaryParticles.ProtocolToll

/-!
# What a charged-current event must read

`PMAction.RefreshSchedule` and `PMAction.CoherentRefresh` show that Economy serves each
required item exactly once; the requirement table is the remaining input. This module derives
the table for one charged-current event (`FinalChannels`) and evaluates it on the static
hypercharge readouts (`ProtocolToll`).

**What the event depends on.** The parent `x` goes to `flip x`, which ignores the sign
(`FinalChannels.flip`). The emitted labels are `pairs x.2`: they depend on the parent's sign and
on nothing else (`pairs_of_sign`), and the two signs give disjoint sets (`pairs_disjoint`). So
no rule that reads only the axis can choose them (`axis_cannot_choose`), and one rule that reads
only the sign does. The event's requirement is one bit: the parent's doublet position.

**Which readout reads it.** On the static wall:
* the quark doublet bit (down flag `1`, up flag `0`) is read exactly by the full readout, down
  flag `1` (`quark_bit_iff`);
* the lepton doublet bit (electron flag `1`; the vacancy flag is always `0`) is read by down flag
  `1` or `¼` (`ProtocolToll.lepton_readout_iff`).

**Own-event accounting ties the labels.** If each label pays only the flags of the readout its
own event requires, then electron and down each pay `1` and up and the vacancy pay `0`
(`own_event_tolls`): `T_e = T_d` and `T_u = T_ν`. So the requirement table read label by label
cannot order the charged labels. Any ordering has to come from readouts a label receives in
events of other labels: a shared register, whose accounting is not derived here.
-/

namespace PMElementaryParticles.EventRequirements
open FinalChannels

/-- The emitted labels depend on the parent only through its sign. -/
theorem pairs_of_sign (x x' : Label) (h : x.2 = x'.2) : pairs x.2 = pairs x'.2 := by rw [h]

/-- The two signs emit disjoint label sets. -/
theorem pairs_disjoint : Disjoint (pairs true) (pairs false) := by decide

/-- **The axis alone cannot choose the emission.** -/
theorem axis_cannot_choose : ¬ ∃ g : Fin 4 → Finset Label, ∀ x : Label, g x.1 = pairs x.2 := by
  rintro ⟨g, hg⟩
  have h1 := hg (0, true)
  have h2 := hg (0, false)
  simp only at h1 h2
  rw [h1] at h2
  exact absurd h2 (by decide)

open ProtocolToll

/-- **The quark doublet readout is the full readout.** A step reads the quark bit (down flag
`1`, up flag `0`) exactly when its down flag is `1`. -/
theorem quark_bit_iff (t : ℝ) (a : Fin 3) :
    (hyperchargeFlag t (downStatic a) = 1 ∧ hyperchargeFlag t (upStatic a) = 0) ↔
      hyperchargeFlag t (downStatic a) = 1 :=
  ⟨And.left, fun h => ⟨h, (full_readout t a h).2.1⟩⟩

/-- **Own-event accounting.** With a lepton-bit readout `t_L` and a quark-bit readout `t_Q`,
each label paying only its own event's readout gives electron and down `1`, up and the vacancy
`0`. -/
theorem own_event_tolls (tL tQ : ℝ) (a : Fin 3)
    (hL : hyperchargeFlag tL electronStatic = 1)
    (hQ : hyperchargeFlag tQ (downStatic a) = 1) :
    hyperchargeFlag tL electronStatic = hyperchargeFlag tQ (downStatic a) ∧
      hyperchargeFlag tQ (upStatic a) = hyperchargeFlag tL neutrinoStatic := by
  refine ⟨by rw [hL, hQ], ?_⟩
  rw [(full_readout tQ a hQ).2.1, neutrinoStatic, hyperchargeFlag_static_neutral]

/-! ### A persisting massive label is on both walls

A massive mode has half its weight on each chirality
(`PMAction.WallRestChirality.charged_weight_half`), and the register's active and static banks
are the two walls (`ControlledGluedRegister`). So a persisting massive label is the equal
superposition of its active slot (quark doublet `Q`, tag `1`; lepton doublet `L`, tag `−3`) and
its static slot. Its flag is the mean of the two slot flags (`PMAction.DiagonalReadout.state_flag`,
`massive_flag`). The active slot cannot read the doublet bit: both partners share it.

At the full readout `3π/2` the active slots flag `½` each, so the massive Tolls are `¾` for the
electron and down and `¼` for up and the vacancy (`full_massive`). The full readout reads the
lepton and the quark bit at once (`full_reads_both`), so one full readout per cycle serves every
event's requirement; under Economy a lepton-only readout adds only cost. Then
`T_e = T_d`: the doublet readouts, with Economy and both walls, still tie the electron with down.
The electron–down split of the heavy-label weight has to come from something that tells the
lepton sector from the colour sector, outside the hypercharge doublet readouts.
-/

open PMConstants.PacketGaugeActions in
/-- An active quark-doublet slot of colour `a`. -/
abbrev quarkActive (a : Fin 3) (i : Fin 2) : PMConstants.PacketGaugeActions.Channels := .inl (a, i)

open PMConstants.PacketGaugeActions in
/-- An active lepton-doublet slot. -/
abbrev leptonActive (i : Fin 2) : PMConstants.PacketGaugeActions.Channels := .inr (.inr (.inl i))

/-- The flag of a massive label: the mean of its active and static slots. -/
noncomputable def massiveFlag (t : ℝ) (cA cS : PMConstants.PacketGaugeActions.Channels) : ℝ :=
  (hyperchargeFlag t cA + hyperchargeFlag t cS) / 2

/-- **The equal superposition's flag is the slot mean.** -/
theorem massive_flag (t : ℝ) (cA cS : PMConstants.PacketGaugeActions.Channels) (h : cA ≠ cS) :
    PMAction.CommonResponse.stateFlag (PMConstants.PacketGaugeActions.hypercharge t)
      (fun c => if c = cA ∨ c = cS then ((Real.sqrt 2)⁻¹ : ℂ) else 0) = massiveFlag t cA cS := by
  rw [PMConstants.PacketGaugeActions.hypercharge, PMAction.DiagonalReadout.state_flag
    PMConstants.PacketGaugeActions.charge_hermitian _ VacancyProjection.charge_real,
    massiveFlag, hyperchargeFlag, hyperchargeFlag, VacancyProjection.hypercharge_flag,
    VacancyProjection.hypercharge_flag]
  have hs : Complex.normSq ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_inv, Complex.normSq_ofReal, ← sq, inv_pow,
      Real.sq_sqrt (by norm_num)]; norm_num
  set F := fun c : PMConstants.PacketGaugeActions.Channels =>
    PMAction.DiagonalReadout.flag (t * ((PMConstants.ChannelOccupancy.hyperchargeThirds c : ℝ) / 3))
  have hpt : ∀ c, Complex.normSq (if c = cA ∨ c = cS then ((Real.sqrt 2)⁻¹ : ℂ) else 0) * F c =
      (if cA = c then F c / 2 else 0) + (if cS = c then F c / 2 else 0) := by
    intro c
    by_cases h1 : c = cA
    · subst h1; simp [hs, h, Ne.symm h]; ring
    · by_cases h2 : c = cS
      · subst h2; simp [hs, h1, Ne.symm h1]; ring
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  change ∑ c, Complex.normSq (if c = cA ∨ c = cS then ((Real.sqrt 2)⁻¹ : ℂ) else 0) * F c =
    (F cA + F cS) / 2
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- The active slots flag `½` at the full readout. -/
theorem active_full (a : Fin 3) (i j : Fin 2) :
    hyperchargeFlag (3 * Real.pi / 2) (quarkActive a i) = 1 / 2 ∧
      hyperchargeFlag (3 * Real.pi / 2) (leptonActive j) = 1 / 2 := by
  simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.hyperchargeThirds_apply, quarkActive, leptonActive]
  push_cast
  constructor
  · rw [show 3 * Real.pi / 2 * 1 / 3 = Real.pi / 2 by ring, Real.cos_pi_div_two]; norm_num
  · rw [show 3 * Real.pi / 2 * -3 / 3 = -(Real.pi + Real.pi / 2) by ring, Real.cos_neg,
      Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]; norm_num

/-- The full readout reads both doublet bits. -/
theorem full_reads_both (a : Fin 3) :
    hyperchargeFlag (3 * Real.pi / 2) electronStatic = 1 ∧
      hyperchargeFlag (3 * Real.pi / 2) neutrinoStatic = 0 ∧
      hyperchargeFlag (3 * Real.pi / 2) (downStatic a) = 1 ∧
      hyperchargeFlag (3 * Real.pi / 2) (upStatic a) = 0 := by
  obtain ⟨he, hd, hu⟩ := flags_three_quarter a
  exact ⟨he, hyperchargeFlag_static_neutral _, hd, hu⟩

/-- **Both walls, full readout: the electron ties with down, up with the vacancy.** -/
theorem full_massive (a : Fin 3) (i j k l : Fin 2) :
    massiveFlag (3 * Real.pi / 2) (leptonActive i) electronStatic = 3 / 4 ∧
      massiveFlag (3 * Real.pi / 2) (quarkActive a j) (downStatic a) = 3 / 4 ∧
      massiveFlag (3 * Real.pi / 2) (quarkActive a k) (upStatic a) = 1 / 4 ∧
      massiveFlag (3 * Real.pi / 2) (leptonActive l) neutrinoStatic = 1 / 4 := by
  obtain ⟨he, hn, hd, hu⟩ := full_reads_both a
  obtain ⟨-, hLi⟩ := active_full a 0 i
  obtain ⟨-, hLl⟩ := active_full a 0 l
  obtain ⟨hQj, -⟩ := active_full a j 0
  obtain ⟨hQk, -⟩ := active_full a k 0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [massiveFlag] <;>
    first
    | (rw [hLi, he]; norm_num) | (rw [hQj, hd]; norm_num)
    | (rw [hQk, hu]; norm_num) | (rw [hLl, hn]; norm_num)

/-- **A colour cost goes the wrong way.** With `n` full readouts per cycle (`full_massive`) and
any nonnegative colour cost `c` charged to the coloured labels (for example the colour ledger's
refresh weight per coloured channel, `PMConstants.ColourReference.colour_ledger_minimal`), down
is never heavier than the electron: `s_d ≤ s_e`. The recorded order needs the opposite, so a
colour contribution to the heavy label must lower the coloured labels' Toll. -/
theorem colour_cost_wrong_way (n c : ℝ) (hc : 0 ≤ c) :
    PersistenceMechanics.EffectiveAction.attenuationWeight 1 (n * (3 / 4) + c) ≤
      PersistenceMechanics.EffectiveAction.attenuationWeight 1 (n * (3 / 4)) := by
  rcases eq_or_lt_of_le hc with h | h
  · rw [← h, add_zero]
  · exact le_of_lt (PMAction.TollAmplitude.wireAmplitude_lt_iff.mpr (by linarith))

/-! ### Which flips a Toll reaches

The wire's light mass is `M = diag(s, k, k) · X · diag(s, 1, 1)`
(`tools/protocol_readout_scan.py`; `PMAction.ReferenceWallFactorization`). A Toll paid equally by all
three generations' flips scales both diagonal factors by one number, so `M` changes by an
overall factor and every mass ratio is unchanged (`uniform_weight_cancels`). Protocol upkeep
that does not depend on the generation (the colour refresh, the doublet readouts as computed
above) therefore cannot produce the heavy-label weight in either direction. Only a Toll that
reaches some generations' flips and not others can.

The library has one native generation difference. On the reference's wall the heavy generation's
carrier never touches the reference class, while the two light ones must pass through the
reference node (`PMAction.ReferenceClassHop`). A Toll `T` on the node legs only multiplies them by
`μ = exp(−T/2)`, which is the same as raising the heavy weight to `s/μ = s · exp(T/2)` at fixed
`k` (`node_toll_raises_heavy`). So a node-path Toll enters with the opposite sign to a Toll on the
heavy flip itself.
-/

/-- **Generation-blind Tolls cancel.** -/
theorem uniform_weight_cancels (l s k : ℂ) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.diagonal ![l * s, l * k, l * k] * X * Matrix.diagonal ![l * s, l, l] =
      (l ^ 2) • (Matrix.diagonal ![s, k, k] * X * Matrix.diagonal ![s, 1, 1]) := by
  have h1 : Matrix.diagonal ![l * s, l * k, l * k] = l • Matrix.diagonal ![s, k, k] := by
    rw [← Matrix.diagonal_smul]; congr 1; ext i; fin_cases i <;> simp
  have h2 : Matrix.diagonal ![l * s, l, l] = l • Matrix.diagonal ![s, 1, 1] := by
    rw [← Matrix.diagonal_smul]; congr 1; ext i; fin_cases i <;> simp
  rw [h1, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, sq]

/-- **A node-path Toll raises the heavy weight.** Damping the two node legs by `μ ≠ 0` is the
heavy weight `s/μ` with undamped node legs, up to an overall factor. -/
theorem node_toll_raises_heavy (μ s k : ℂ) (hμ : μ ≠ 0) :
    Matrix.diagonal ![s, k * μ, k * μ] = μ • Matrix.diagonal ![s / μ, k, k] := by
  rw [← Matrix.diagonal_smul]; congr 1; ext i
  fin_cases i <;> simp [mul_comm, mul_div_cancel₀ _ hμ]

end PMElementaryParticles.EventRequirements
