import PMElementaryParticles.WireSchedule
import PMConstants.PreparationSelection
import PMConstants.ReferenceEconomy
import PMSubstrate.PersistenceMaximin

/-!
# The population cost of the two electric record references

The individual flags come from the electric reader. Aggregate costs need
a population or a set of required reads. Neither the reader nor the
survival conversion supplies that population.
-/

noncomputable section
namespace PMElementaryParticles.WireReferenceCost
open PMConstants.PacketGaugeActions ProtocolInventory Finset
open PMSubstrate.NetCost
open scoped BigOperators

/-- Uniform sampling on the full packet gives the inventory multiplicities
divided by sixteen. The absence of a base protocol is its own event. -/
theorem uniform_slot_weights :
    prob (univ.filter fun c : Channels => baseProtocol c = some .electron) = 2 / 16 ∧
    prob (univ.filter fun c : Channels => baseProtocol c = some .down) = 6 / 16 ∧
    prob (univ.filter fun c : Channels => baseProtocol c = some .up) = 6 / 16 ∧
    prob (univ.filter fun c : Channels => baseProtocol c = some .neutrino) = 1 / 16 ∧
    prob (univ.filter fun c : Channels => baseProtocol c = none) = 1 / 16 := by
  obtain ⟨hu, hd, he, hn, hv⟩ := inventory_split
  simp [prob, he, hd, hu, hn, hv]

/-- A protocol's copies on one wall. The quark copies are the `Fin 3`
colour coordinates of the two sum types. -/
def wallSlots (wall : Bool) (label : Option BaseProtocol) : Finset Channels :=
  univ.filter fun c => active c = wall ∧ baseProtocol c = label

theorem wall_inventory (wall : Bool) :
    (wallSlots wall (some .electron)).card = 1 ∧
    (wallSlots wall (some .down)).card = 3 ∧
    (wallSlots wall (some .up)).card = 3 ∧
    (wallSlots wall (some .neutrino)).card = (if wall then 1 else 0) ∧
    (wallSlots wall none).card = (if wall then 0 else 1) := by
  cases wall <;> decide +kernel

/-- The full-packet maximin premise forces the uniform slot sampling law. -/
theorem uniform_if_maximin (p : Channels → ℝ)
    (h : PMSubstrate.PersistenceMaximin.Maximin p) (c : Channels) : p c = 1 / 16 := by
  simpa [channels_card] using
    (PMSubstrate.PersistenceMaximin.maximin_iff p).mp h c

/-- An alternative uniformity proof when the writer's inputs really inherit
the invariant 32-carrier preparation by restriction and renormalization. -/
theorem uniform_if_inherited
    (P : Bool × PMSubstrate.ChannelSymmetry.V4 → ℝ)
    (hP : ∀ i, ∀ x ∈ PMSubstrate.ChannelSymmetry.channels,
      P (PMSubstrate.ChannelSymmetry.gen i x) = P x)
    (p : Channels → ℝ) (k : ℝ)
    (hp : ∀ c, p c = k * P (PMConstants.PreparationSelection.toChannel c))
    (hsum : ∑ c, p c = 1) (c : Channels) : p c = 1 / 16 := by
  rw [PMConstants.PreparationSelection.packet_preparation_uniform P hP p k hp hsum,
    PersistenceMechanics.LawSelection.uniform, channels_card]
  norm_num

/-- A packet comparison sees the supplied input populations. Diagonality
eliminates cross terms even for coherent input; it assigns no populations. -/
theorem packet_flag (t : ℝ) (φ : Channels → ℂ) :
    PMAction.CommonResponse.stateFlag (hypercharge t) φ =
      ∑ c, Complex.normSq (φ c) * ProtocolToll.hyperchargeFlag t c := by
  simp only [ProtocolToll.hyperchargeFlag, VacancyProjection.hypercharge_flag]
  exact PMAction.DiagonalReadout.state_flag charge_hermitian _
    VacancyProjection.charge_real t φ

/-- Compressing a two-wall pair to one massive state takes the mean of
the two flags. The weight of that massive state in a traffic law is separate. -/
theorem massive_pair_flag (t : ℝ) (c : Channels) :
    PMAction.CommonResponse.stateFlag (hypercharge t)
      (fun d => if d = ControlledGluedRegister.opposite c ∨ d = c
        then ((Real.sqrt 2)⁻¹ : ℂ) else 0) =
    (ProtocolToll.hyperchargeFlag t (ControlledGluedRegister.opposite c) +
      ProtocolToll.hyperchargeFlag t c) / 2 := by
  have h : ControlledGluedRegister.opposite c ≠ c := by
    intro h
    have hh := ControlledGluedRegister.opposite_active c
    rw [h] at hh
    cases hc : active c <;> simp_all
  exact EventRequirements.massive_flag t _ _ h

end PMElementaryParticles.WireReferenceCost
