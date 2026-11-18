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

end PMElementaryParticles.EventRequirements
