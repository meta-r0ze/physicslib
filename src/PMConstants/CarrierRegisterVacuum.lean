import PMConstants.CarrierRegisterModel
import PMAction.RegisterVacuum

/-!
# Full native vacuum on the independent-register configuration model

The canonical construction is `PMAction.RegisterVacuum`; this module retains
Paper III's entry points specialized to its actual packet labels.
The number-conserving hard-core lift of Paper II's actual native Hamiltonian
has the complete eight-mode vacuum readout, for every momentum and detuning.
It is Hermitian on all configurations, evolves unitarily, and has no invisible
feedback into the spinor/payload readout. The second bank is retained.

The hard-core higher-occupation completion is specified, not selected from PM.
Physical bank preparation, coherent hopping/gate admission, the real-space split
schedule, reference/current attachment and primitive prices remain obligations.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMConstants.CarrierRegisterVacuum
open Matrix PMAction CarrierRegisterModel NativeObservation
open scoped Kronecker

def generator (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) : Matrix Config Config ℂ :=
  RegisterVacuum.generator (b := Payload) 0 p k δ

def observedGenerator (k : Fin 3 → ℝ) (δ : ℝ) : Matrix Modes Modes ℂ :=
  RegisterVacuum.observedGenerator (b := Payload) k δ

theorem hermitian (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) :
    (generator p k δ).IsHermitian := RegisterVacuum.hermitian 0 p k δ

/-- Full generator identification along the existing isometric coordinate readout. -/
theorem observed (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) :
    Obs embedding (generator p k δ) (observedGenerator k δ) :=
  RegisterVacuum.observed 0 p hp hp1 k δ

theorem evolution_unitary (p : ℝ) (k : Fin 3 → ℝ) (δ t : ℝ) :
    NormedSpace.exp ((-Complex.I * t) • generator p k δ) ∈ unitary (Matrix Config Config ℂ) :=
  RegisterVacuum.evolution_unitary 0 p k δ t

/-- Exact readout for every ambient initial amplitude, not only encoded inputs. -/
theorem evolution_readout (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (z : ℂ) (ψ : Config → ℂ) :
    embeddingᴴ *ᵥ (NormedSpace.exp (z • generator p k δ) *ᵥ ψ) =
      NormedSpace.exp (z • observedGenerator k δ) *ᵥ (embeddingᴴ *ᵥ ψ) :=
  RegisterVacuum.evolution_readout 0 p hp hp1 k δ z ψ

end PMConstants.CarrierRegisterVacuum
