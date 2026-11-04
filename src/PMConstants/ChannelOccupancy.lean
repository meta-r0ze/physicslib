import PMConstants.PacketGaugeActions

/-!
# The sixteen channels are one observed generation, with no slot to spare

Paper III's structural audit lists "no supersymmetric partners (`ν = 16`)" and says a proof needs
the explicit map from channels to representations. The packet (`PacketGaugeActions`) supplies it:
`Channels = Q ⊕ (Q ⊕ (Fin 2 ⊕ Fin 2))`, with weak acting on the first `Q` and the first `Fin 2`,
colour on both `Q`s, and the hypercharge `charge = 2Y` on the diagonal.

* `charge_entries`: the diagonal of `charge` is `2Y = 6Y/3` = `1/3` on the quark doublets, `4/3` and
  `−2/3` on the right quarks, `−1` on the lepton doublet, `0` and `−2` on the right leptons.
* `occupancy`: tagging each channel by (colour dimension, weak dimension, `6Y`), the channels
  are exactly one generation with a right-handed neutrino: `(3,2,1)` six times, `(3,1,4)` and
  `(3,1,−2)` three times each, `(1,2,−3)` twice, `(1,1,−6)` and `(1,1,0)` once each, sixteen in
  all.
* `no_spare_channel`: every channel is used by an observed state, so any further state, such as a
  superpartner, which carries the same gauge numbers but different spin, needs a channel beyond the
  sixteen. No injective placement of the observed states plus `d > 0` extra states exists.

Premise: one generation's states occupy one packet (Paper V's channel table) and each state needs
its own channel. Whether superpartners could live in another structure (more packets, other
cells) is not addressed; the statement is that the packet has no room.
-/

noncomputable section
namespace PMConstants.ChannelOccupancy
open PMConstants PacketGaugeActions Matrix

/-- (colour dimension, weak dimension, `6Y`) of each channel. -/
def tag : Channels → ℕ × ℕ × ℤ
  | .inl _ => (3, 2, 1)
  | .inr (.inl (_, s)) => if s = 0 then (3, 1, 4) else (3, 1, -2)
  | .inr (.inr (.inl _)) => (1, 2, -3)
  | .inr (.inr (.inr s)) => if s = 0 then (1, 1, 0) else (1, 1, -6)

/-- **The hypercharge diagonal is the tag's `2Y`.** -/
theorem charge_entries (c : Channels) : charge c c = ((tag c).2.2 : ℂ) / 3 := by
  rcases c with ⟨i, s⟩ | ⟨i, s⟩ | s | s <;> fin_cases s <;>
    simp [charge, block, tag, kroneckerMap_apply, one_apply, diagonal]
  all_goals norm_num

/-- **The channels are one generation with `ν_R`.** -/
theorem occupancy :
    (Finset.univ.filter (fun c => tag c = (3, 2, 1))).card = 6 ∧
    (Finset.univ.filter (fun c => tag c = (3, 1, 4))).card = 3 ∧
    (Finset.univ.filter (fun c => tag c = (3, 1, -2))).card = 3 ∧
    (Finset.univ.filter (fun c => tag c = (1, 2, -3))).card = 2 ∧
    (Finset.univ.filter (fun c => tag c = (1, 1, -6))).card = 1 ∧
    (Finset.univ.filter (fun c => tag c = (1, 1, 0))).card = 1 ∧
    Fintype.card Channels = 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by simp [Channels, Q]⟩ <;> decide

/-- **No channel is left for an extra state.** -/
theorem no_spare_channel (d : ℕ) (f : Channels ⊕ Fin d → Channels) (hf : Function.Injective f) :
    d = 0 := by
  have := Fintype.card_le_of_injective f hf
  simp [Channels, Q] at this
  omega

end PMConstants.ChannelOccupancy
