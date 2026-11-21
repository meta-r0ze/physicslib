import PMAction.LinkEvolution
import PMAction.CommonResponse

/-! Exact finite flavour evolution from supplied eigenenergies and mixing:
`U · diag(e^{−iE t}) · Uᴴ`, a one-parameter unitary group. Valid algebra; the physical premise is
in its use. That the substrate update at the clock acts on wall modes this way is open
(`PMAction/TODO.md`, "Update as `e^{−iHt}` on wall modes"); `PMFlavor.NativeFlavourPropagation`
shows the native wall generator's exponential is this evolution on prepared eigenmodes.
The Hamiltonian and probability readout are inputs. This supplies no physical
neutrino masses, relativistic energy approximation or exclusion of Majorana terms. -/
noncomputable section
namespace PMAction.FlavourEvolution
open Matrix
open scoped Matrix.Norms.Operator
abbrev M := Matrix (Fin 3) (Fin 3) ℂ

/-- The flavour Hamiltonian `U · diag(E) · Uᴴ` (`PMFlavor.MassMixing.mass` is the same matrix). -/
def hamiltonian (U : M) (energy : Fin 3 → ℝ) : M := U * diagonal (fun i => (energy i : ℂ)) * Uᴴ

def evolution (U : M) (energy : Fin 3 → ℝ) (t : ℝ) :=
  U * PMAction.LinkExpansion.phaseDiag energy (-t) * Uᴴ

/-- Reuse Paper II's basis-independent exponential theorem for the supplied
flavour Hamiltonian. Energies need not be mass eigenvalues. -/
theorem equals_exponential (U : M) (energy : Fin 3 → ℝ) (hU : U*Uᴴ=1) (t : ℝ) :
    evolution U energy t =
      NormedSpace.exp ((((-t : ℝ) : ℂ)*Complex.I) • hamiltonian U energy) := by
  exact (PMAction.LinkEvolution.diagonalization_exponential U energy
    (mul_eq_one_comm.mp hU) hU (-t)).symm

theorem evolution_unitary (U : M) (energy : Fin 3 → ℝ) (hU : U*Uᴴ=1) (t : ℝ) :
    evolution U energy t ∈ unitary M := by
  have hu : U ∈ unitary M := ⟨mul_eq_one_comm.mp hU,hU⟩
  exact (unitary M).mul_mem ((unitary M).mul_mem hu
    (PMAction.HermitianTransport.diagonal_unitary energy (-t))) (Unitary.star_mem hu)

theorem composition (U : M) (energy : Fin 3 → ℝ) (hU : U*Uᴴ=1) (s t : ℝ) :
    evolution U energy s * evolution U energy t = evolution U energy (s+t) := by
  simp only [evolution, PMAction.LinkEvolution.conjugate_mul U _ _ (mul_eq_one_comm.mp hU),
    PMAction.LinkEvolution.phase_add, neg_add]

theorem zero (U : M) (energy : Fin 3 → ℝ) (hU : U*Uᴴ=1) : evolution U energy 0=1 := by
  simpa [evolution, PMAction.LinkExpansion.phaseDiag] using hU

def probability (U : M) (energy : Fin 3 → ℝ) (t : ℝ) (outgoing incoming : Fin 3) : ℝ :=
  Complex.normSq (evolution U energy t outgoing incoming)

/-- Probability is normalized across the complete three-channel output space. -/
theorem total_probability (U : M) (energy : Fin 3 → ℝ) (hU : U*Uᴴ=1)
    (t : ℝ) (incoming : Fin 3) : ∑ outgoing, probability U energy t outgoing incoming=1 := by
  have hh := congrArg Complex.re (PMAction.CommonResponse.unitary_nsq
    (evolution U energy t) (evolution_unitary U energy hU t) (Pi.single incoming 1))
  simpa [probability, dotProduct, Complex.mul_conj, ← Complex.normSq_eq_conj_mul_self,
    Matrix.mulVec_single, Pi.single_apply] using hh

/-- Column phases cancel from propagation, including the extra column phases
usually considered when comparing Dirac and Majorana mixing conventions. -/
theorem column_phases (U : M) (energy : Fin 3 → ℝ) (phase : Fin 3 → ℂ)
    (hp : ∀ i, phase i*star (phase i)=1) (t : ℝ) :
    evolution (U * diagonal phase) energy t = evolution U energy t := by
  have hd : diagonal phase * PMAction.LinkExpansion.phaseDiag energy (-t) * (diagonal phase)ᴴ =
      PMAction.LinkExpansion.phaseDiag energy (-t) := by
    simp only [PMAction.LinkExpansion.phaseDiag, diagonal_conjTranspose,
      diagonal_mul_diagonal]
    congr 1
    funext i
    change phase i * _ * star (phase i) = _
    calc
      _ = (phase i*star (phase i))*Complex.exp (((-t*energy i : ℝ) : ℂ)*Complex.I) := by ring
      _ = _ := by rw [hp]; simp
  simp only [evolution, conjTranspose_mul]
  calc
    _ = U * (diagonal phase * PMAction.LinkExpansion.phaseDiag energy (-t) * (diagonal phase)ᴴ) * Uᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hd]

end PMAction.FlavourEvolution
