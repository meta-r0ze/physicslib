import PMConstants.CarrierActions
import PMAction.Machine.RegisterPrograms
import PMAction.Machine.RegisterVacuum

/-!
# Separate native register banks for spinor and internal packet labels

Two banks use actual existing carrier labels: sixteen two-wall vacuum labels
and sixteen packet labels. Exactly one occupied register per bank supplies 256
configuration states and an isometric 128-mode coordinate readout (eight vacuum
coordinates times sixteen packet states). This does not confuse identical label
types with the same physical register. The beta word and every packet permutation
act independently and are observed exactly, including coherent evolution of their
operator expressions.

The construction requires two banks and their occupancy sector. It does not
select them, prepare them, locate them on the phase grid or price their gates.
It identifies one native vacuum generator word, not the full vacuum schedule,
fermionic statistics, a physical reference source or a generation breaking law.
-/
noncomputable section
set_option synthInstance.maxSize 512
namespace PMConstants.CarrierRegisterModel
open Matrix PMAction NativeObservation IndependentRegisters
open scoped Kronecker
attribute [local instance] Classical.propDecidable

abbrev SpinLabels := CarrierVacuumSector.Labels 0
abbrev Payload := CarrierActions.Packet
abbrev Config := Configuration SpinLabels Payload
abbrev Modes := ConcreteFermion.Sites × Payload

def coordinate : Matrix (SpinLabels × Payload) Modes ℂ :=
  RegisterVacuum.coordinate (b := Payload) 0

def embedding : Matrix Config Modes ℂ := RegisterVacuum.embedding (b := Payload) 0

theorem coordinate_isometry : coordinateᴴ * coordinate = 1 :=
  tensor_isometry _ _ (CarrierVacuumSector.isometry 0) (by simp)

theorem isometry : embeddingᴴ * embedding = 1 :=
  RegisterVacuum.isometry 0

theorem register_count : Fintype.card (SpinLabels ⊕ Payload) = 32 := by
  simp [SpinLabels, CarrierVacuumSector.Labels, Payload, CarrierActions.Packet,
    CarrierRepresentation.V, CarrierEvents.carrier_card]

theorem sector_count : Fintype.card {q : Config // Valid q} = 256 := by
  rw [IndependentRegisters.sector_card]
  simp [SpinLabels, CarrierVacuumSector.Labels, Payload, CarrierActions.Packet,
    CarrierRepresentation.V, CarrierEvents.carrier_card]

theorem mode_count : Fintype.card Modes = 128 := by
  simp [Modes, Payload, CarrierActions.Packet, CarrierRepresentation.V,
    CarrierEvents.carrier_card, ConcreteFermion.Sites]

def betaWord : Equiv.Perm SpinLabels :=
  Equiv.sumCongr (CarrierWeyl.lookup 0 0) (CarrierWeyl.lookup 0 0)

def betaObserved : Matrix ConcreteFermion.Sites ConcreteFermion.Sites ℂ :=
  fromBlocks ConcreteFermion.beta 0 0 ConcreteFermion.beta

private theorem beta_matrix : betaWord.permMatrix ℂ =
    fromBlocks (CarrierVacuumSector.beta 0) 0 0 (CarrierVacuumSector.beta 0) := by
  ext i j
  cases i <;> cases j <;>
    simp [betaWord, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      CarrierVacuumSector.beta, fromBlocks, Pi.single_apply, eq_comm]

theorem beta_word_observed : Obs (CarrierVacuumSector.embedding 0)
    (betaWord.permMatrix ℂ) betaObserved := by
  rw [beta_matrix]
  exact NativeObservation.blocks (NativeSector.beta_obs 0) NativeObservation.zero
    NativeObservation.zero (NativeSector.beta_obs 0)

/-- The spinor word and actual weak/colour permutations can run on independent
registers with exact all-configuration coordinate readout. -/
theorem beta_payload_observed (f : Equiv.Perm Payload) :
    Obs embedding ((update betaWord f).permMatrix ℂ) (betaObserved ⊗ₖ f.permMatrix ℂ) := by
  apply NativeObservation.compose (tensor_observed betaWord f)
  exact NativeObservation.tensor beta_word_observed
    (show Obs (1 : Matrix Payload Payload ℂ) (f.permMatrix ℂ) (f.permMatrix ℂ)
      from ⟨by simp, by simp⟩)

theorem payload_observed (f : Equiv.Perm Payload) :
    Obs embedding ((update (Equiv.refl SpinLabels) f).permMatrix ℂ)
      ((1 : Matrix ConcreteFermion.Sites ConcreteFermion.Sites ℂ) ⊗ₖ f.permMatrix ℂ) := by
  apply NativeObservation.compose (tensor_observed (Equiv.refl SpinLabels) f)
  apply NativeObservation.tensor
  · simpa using (NativeObservation.one : Obs (CarrierVacuumSector.embedding 0) 1 1)
  · exact ⟨by simp, by simp⟩

/-- The weak and colour actions now have a separate bank; neither consumes a
spinor coordinate nor the spinor wall as an implicit extra index. -/
theorem weak_colour_separate (i j : Fin 3) :
    Obs embedding ((update (Equiv.refl SpinLabels) CarrierActions.weak).permMatrix ℂ)
      ((1 : Matrix ConcreteFermion.Sites ConcreteFermion.Sites ℂ) ⊗ₖ
        CarrierActions.weak.permMatrix ℂ) ∧
    Obs embedding ((update (Equiv.refl SpinLabels) (CarrierActions.colour i j)).permMatrix ℂ)
      ((1 : Matrix ConcreteFermion.Sites ConcreteFermion.Sites ℂ) ⊗ₖ
        (CarrierActions.colour i j).permMatrix ℂ) :=
  ⟨payload_observed _, payload_observed _⟩

end PMConstants.CarrierRegisterModel
