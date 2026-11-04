import PMConstants.PacketGaugeActions
import PMConstants.ReferenceAxis
import PMConstants.CarrierRepresentation
import Mathlib.Tactic

/-!
# Baryon number on the 16 channels, and why a reversible update conserves it

Baryon number is not a separate axiom here: it is read off the same axis ledger
that gives `B − L`. The lepton axis carries baryon `0` and lepton `1`; each colour
axis carries baryon `1/3` and lepton `0`, so `B − L` is `−1` on the lepton axis and
`1/3` on the colour axes, exactly `ReferenceAxis.bl = diag(−1, 1/3, 1/3, 1/3)`
(`bl_eq`).

On the actual 16 channels (`PacketGaugeActions.Channels`), `axisOf` sends the
colour blocks to the three colour axes and the lepton blocks to the lepton axis;
`baryon`/`lepton` are the corresponding weights.

**Conservation.** The native reversible operations act within a block
(`flipWeak` swaps the doublet index, `permuteColour` permutes the colour axes), so
they preserve `baryon` pointwise. Any bijective channel update that preserves
`baryon` pointwise conserves the total baryon weight of any state
(`totalB_perm`). Hence a *reversible* substrate update cannot create a baryon
asymmetry: a net baryon number requires a non-baryon-preserving (irreversible /
baryon-changing) event. This is the Paper VI B4 prerequisite, proved on the
actual channels rather than asserted.

Also recorded: `CarrierRepresentation.pmns...` no — the colour/lepton multiplicities
are unchanged; only the charge grading is added.
-/

noncomputable section
namespace PMConstants.BaryonNumber
open PMConstants PacketGaugeActions Matrix

/-- The axis a channel lives on: colour blocks → the three colour axes, lepton
blocks → the lepton axis `0`. -/
def axisOf : Channels → Fin 4
  | .inl (c, _) => Fin.succ c
  | .inr (.inl (c, _)) => Fin.succ c
  | .inr (.inr (.inl _)) => 0
  | .inr (.inr (.inr _)) => 0

/-- Baryon weight per axis: `0` on the lepton axis, `1/3` on the colour axes. -/
def axisB (i : Fin 4) : ℚ := if i = 0 then 0 else 1/3

/-- Lepton weight per axis: `1` on the lepton axis, `0` on the colour axes. -/
def axisL (i : Fin 4) : ℚ := if i = 0 then 1 else 0

/-- Baryon number of a channel. -/
def baryon (c : Channels) : ℚ := axisB (axisOf c)

/-- Lepton number of a channel. -/
def lepton (c : Channels) : ℚ := axisL (axisOf c)

theorem baryon_eq_axisB (c : Channels) : baryon c = axisB (axisOf c) := rfl
theorem lepton_eq_axisL (c : Channels) : lepton c = axisL (axisOf c) := rfl

/-- `B − L` on the four axes is exactly `ReferenceAxis.bl`. -/
theorem bl_eq :
    ReferenceAxis.bl =
      Matrix.diagonal (fun i : Fin 4 => ((axisB i - axisL i : ℚ) : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ReferenceAxis.bl, axisB, axisL, Matrix.diagonal]

/-- `B − L` per channel is the paper's value: `1/3` on colour, `−1` on the lepton
axis. -/
theorem baryon_sub_lepton (c : Channels) :
    axisB (axisOf c) - axisL (axisOf c) = if axisOf c = 0 then -1 else 1/3 := by
  by_cases h : axisOf c = 0 <;> simp [axisB, axisL, h]

/-- **The doublet flip preserves baryon** (it only swaps the doublet index). -/
theorem baryon_flipWeak (c : Channels) : baryon (flipWeak c) = baryon c := by
  rcases c with ⟨a, s⟩ | ⟨a, s⟩ | s | s <;>
    simp [baryon, axisOf, flipWeak, axisB]

/-- **Colour permutations preserve baryon** (they only relabel the colour axes). -/
theorem baryon_permuteColour (a b : Fin 3) (c : Channels) :
    baryon (permuteColour a b c) = baryon c := by
  rcases c with ⟨q, s⟩ | ⟨q, s⟩ | s | s <;>
    simp [baryon, axisOf, permuteColour, axisB]

/-- **Reversible updates conserve total baryon.** If a bijective channel update
preserves `baryon` pointwise, the total baryon weight of any state is unchanged. -/
theorem totalB_perm (n : Channels → ℚ) (σ : Channels ≃ Channels)
    (hB : ∀ c, baryon (σ c) = baryon c) :
    (∑ c, n (σ.symm c) * baryon c) = ∑ c, n c * baryon c := by
  have h1 : (∑ c, n (σ.symm c) * baryon c) = ∑ c, n c * baryon (σ c) := by
    have := Equiv.sum_comp σ.symm (fun c => n c * baryon (σ c))
    simpa using this
  rw [h1]
  exact Finset.sum_congr rfl (fun c _ => by rw [hB c])

/-- A reversible update that preserves baryon cannot change the *net* baryon
weight: if the total is initially zero, it stays zero. (Contrapositive: creating a
net baryon number needs a baryon-changing, non-pointwise-preserving event.) -/
theorem no_asymmetry_from_reversible (n : Channels → ℚ) (σ : Channels ≃ Channels)
    (hB : ∀ c, baryon (σ c) = baryon c)
    (hzero : ∑ c, n c * baryon c = 0) :
    ∑ c, n (σ.symm c) * baryon c = 0 := by
  rw [totalB_perm n σ hB, hzero]

end PMConstants.BaryonNumber
