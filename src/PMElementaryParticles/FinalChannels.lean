import PMElementaryParticles.SubstrateFinalStates

/-!
# Final channels of a charged-current event, from the register

In the register reading (OVERVIEW, "Protocol register"; `GluedRegister`) a protocol is a wire mode
tensored with a label, a carrier of the other `D₄` factor. In the vector frame a label is an axis and
a sign: axis `0` is the lepton axis, axes `1, 2, 3` are the colours (`TauBranching.colours_eq`), and the
sign is the doublet. The weak event acts on the label as its antipode, which keeps the axis and flips
the sign (`GluedRegister.neg_class`, `neg_ne`); on the wire mode it acts as the native charged current
(`PMAction.NativeExternal.native_current`). The label's charge is its base protocol's
(`PMElementaryParticles.ProtocolInventory.BaseProtocol.charge`).

* `flip_charge`: the weak flip changes the charge by exactly one unit on every label (`+1` from a
  down label, `−1` from an up label): the event carries one unit of charge, whatever the axis.
* `pair_conserves_iff`: a charged-current event takes the parent `x` to `flip x` and emits a label
  with the antilabel of its partner, `y + anti (flip y)`. Charge is conserved exactly when `y` has the
  parent's sign. So the emitted pairs of a down parent are `(down, anti up)` on one axis: on the
  lepton axis `e ν̄`, on each colour axis `d ū` of that colour.
* `pairs_card`, `colour_pairs_card`: there are four such pairs, one leptonic and three coloured.
  This is the channel count in `TauBranching.branching` (`1` per open lepton pair, `N_c = 3` for the
  quark pair), now from the label rather than stipulated.

Which pairs are open is kinematic (masses, PMHadrons for quark pairs); generation changes at the
vertex are PMFlavor's transfer readout. The SM names in the comments are comparison labels.
-/

namespace PMElementaryParticles.FinalChannels
open ProtocolInventory SubstrateFinalStates

/-- A label in the vector frame: axis (`0` lepton, `1..3` colour) and sign (`true` = up member). -/
abbrev Label := Fin 4 × Bool

def base (x : Label) : BaseProtocol :=
  if x.1 = 0 then (if x.2 then .neutrino else .electron) else (if x.2 then .up else .down)

def charge (x : Label) : ℚ := PMElementaryParticles.ProtocolInventory.BaseProtocol.charge (base x)

/-- The weak event on the label: the antipode, same axis, opposite sign. -/
def flip (x : Label) : Label := (x.1, !x.2)

theorem flip_charge : ∀ x : Label, charge x - charge (flip x) = if x.2 then 1 else -1 := by
  rintro ⟨a, s⟩
  fin_cases a <;> cases s <;> norm_num [charge, base, flip, PMElementaryParticles.ProtocolInventory.BaseProtocol.charge, PMElementaryParticles.ProtocolInventory.BaseProtocol.leptonAxis, PMElementaryParticles.ProtocolInventory.BaseProtocol.positiveSign, PMConstants.Hypercharge.electric, PMConstants.CarrierRepresentation.blAxis, PMConstants.CarrierRepresentation.t3Sign]

theorem flip_flip (x : Label) : flip (flip x) = x := by simp [flip]

/-- Parent `x` goes to `flip x` and emits `y` with the antilabel of `flip y`. -/
theorem pair_conserves_iff : ∀ x y : Label,
    charge (flip x) + (charge y - charge (flip y)) = charge x ↔ y.2 = x.2 := by
  rintro ⟨a, s⟩ ⟨b, t⟩
  fin_cases a <;> fin_cases b <;> cases s <;> cases t <;> norm_num [charge, base, flip, PMElementaryParticles.ProtocolInventory.BaseProtocol.charge, PMElementaryParticles.ProtocolInventory.BaseProtocol.leptonAxis, PMElementaryParticles.ProtocolInventory.BaseProtocol.positiveSign, PMConstants.Hypercharge.electric, PMConstants.CarrierRepresentation.blAxis, PMConstants.CarrierRepresentation.t3Sign]

/-- The emitted labels for a parent of sign `σ`. -/
def pairs (σ : Bool) : Finset Label := Finset.univ.filter fun y => y.2 = σ

theorem pairs_card (σ : Bool) : (pairs σ).card = 4 := by
  cases σ <;> decide

theorem colour_pairs_card (σ : Bool) : ((pairs σ).filter fun y => y.1 ≠ 0).card = 3 := by
  cases σ <;> decide

theorem lepton_pair (σ : Bool) : ((pairs σ).filter fun y => y.1 = 0) = {(0, σ)} := by
  cases σ <;> decide

/-- A down lepton parent (`μ`, `τ`): the leptonic pair is `e ν̄`, the coloured pairs `d ū`. -/
theorem down_lepton_pairs :
    base (flip (0, false)) = .neutrino ∧ base (0, false) = .electron ∧
      ∀ i : Fin 4, i ≠ 0 → base (i, false) = .down ∧ base (flip (i, false)) = .up := by
  decide

end PMElementaryParticles.FinalChannels
