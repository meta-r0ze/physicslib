import PMConstants.Generations
import PMAction.CarrierClassBundle

/-!
# Test generation dictionaries against the already constructed vacuum

The vector-only packet readout used in the distinct-pair count is not the same
readout as Paper II's native vacuum. The native vacuum retains the wall label
and realizes its full chosen Hamiltonian on two copies of a single class.
This is an explicit dynamically consistent alternative to the vector-faithful
packet contract, not a selection of that alternative as physical generations.

The class-bundle route keeps the wall action independent of the class index.
Its unbroken generator gives the same eigenvalue to every class superposition;
an actual interaction/breaking law is needed for splittings and mixing.
-/

noncomputable section
namespace PMConstants.GenerationVacuumChoice
open Matrix PMAction

/-- Vector collision does not preclude the existing two-wall native vacuum
model when the observed state keeps its wall distinction. -/
theorem same_class_vacuum (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) :
    ¬ Function.Injective (@CarrierCost.packetVector c c) ∧
      (CarrierVacuumSector.embedding c)ᴴ * CarrierVacuumSector.embedding c = 1 ∧
      (NativeSector.nativeHamiltonian c p k δ).IsHermitian ∧
      NativeObservation.Obs (CarrierVacuumSector.embedding c)
        (NativeSector.nativeHamiltonian c p k δ) (ConcreteFermion.hamiltonian k δ) :=
  ⟨Generations.same_class_loses c, CarrierVacuumSector.isometry c,
    NativeSector.nativeHamiltonian_hermitian c p k δ, NativeSector.native_obs hp hp1 k δ⟩

/-- A further reason the readout contract matters: erasing the wall label
prevents deterministic prediction of the next vector under a one-wall root. -/
theorem vector_readout_fails (c : Fin 3) :
    ¬ ∃ update : (Fin 4 → ℤ) → (Fin 4 → ℤ), ∀ v : CarrierCost.Packet c c,
      CarrierCost.packetVector (CarrierCost.firstWallRoot c v) =
        update (CarrierCost.packetVector v) :=
  CarrierCost.equal_class_vector_not_closed c

/-- The common class-sector vacuum leaves all class superpositions at the same
eigenvalue. It does not select three distinct masses merely by having three classes. -/
theorem unbroken_class_freedom (k : Fin 3 → ℝ) (δ : ℝ) (energy : ℂ)
    (v : ConcreteFermion.Sites → ℂ)
    (hv : ConcreteFermion.hamiltonian k δ *ᵥ v = energy • v) (w : Fin 3 → ℂ) :
    CarrierClassBundle.observedGenerator k δ *ᵥ
        (fun q : CarrierClassBundle.Modes => w q.1 * v q.2) =
      energy • (fun q : CarrierClassBundle.Modes => w q.1 * v q.2) :=
  CarrierClassBundle.common_eigenvalue k δ energy v hv w

end PMConstants.GenerationVacuumChoice
