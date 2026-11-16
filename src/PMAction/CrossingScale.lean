import PMAction.CyclicSeesaw
import PMAction.LinkEvolution

/-!
# Crossing isometry, unitary evolution and the crossing time scale

The gapped block uses Y as a Hamiltonian coupling. Its coherent evolution
is unitary for every Y. Requiring Y itself to be an isometry is an additional
contract. A common positive real rate can be absorbed into the evolution time;
its size relative to other terms and the substrate clock remains physical input.
-/
noncomputable section
namespace PMAction.CrossingScale
open Matrix
open scoped Matrix.Norms.Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem gapped_hermitian (Y : Matrix n n ℂ) : (WallSeesaw.G Y).IsHermitian := by
  simp [Matrix.IsHermitian, WallSeesaw.G, fromBlocks_conjTranspose]

/-- All Hamiltonian crossing strengths admit unitary coherent evolution. -/
theorem evolution_unitary (Y : Matrix n n ℂ) (t : ℝ) :
    HermitianTransport.transport (gapped_hermitian Y) t ∈ unitary _ :=
  HermitianTransport.transport_unitary _ _

/-- A concrete cyclic link fails the standalone isometry contract while
its gapped Hamiltonian still generates unitary evolution at every time. -/
theorem unitary_does_not_force_isometry :
    let Y := CyclicSeesaw.cyc (fun _ => (2 : ℂ))
    Yᴴ * Y ≠ 1 ∧ ∀ t : ℝ,
      HermitianTransport.transport (gapped_hermitian Y) t ∈ unitary _ := by
  constructor
  · rw [ne_eq, CyclicSeesaw.crossing_isometry_iff]
    norm_num
  · exact evolution_unitary _

omit [Fintype n] [DecidableEq n] in
theorem gapped_scale (Y : Matrix n n ℂ) (s : ℝ) :
    WallSeesaw.G (s • Y) = s • WallSeesaw.G Y := by
  ext i j
  cases i <;> cases j <;> simp [WallSeesaw.G, conjTranspose_smul]

/-- Scaling a crossing rate is exactly inverse scaling of its time unit. -/
theorem rate_time (Y : Matrix n n ℂ) (s t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • WallSeesaw.G (s • Y)) =
      NormedSpace.exp ((Complex.I * ((s*t : ℝ) : ℂ)) • WallSeesaw.G Y) := by
  rw [gapped_scale]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- A nonzero common real crossing magnitude is a permissible time unit.
No value relative to an independent lattice-hop clock follows. -/
theorem normalize_rate (Y : Matrix n n ℂ) (s t : ℝ) (hs : s ≠ 0) :
    NormedSpace.exp ((Complex.I * ((t/s : ℝ) : ℂ)) • WallSeesaw.G (s • Y)) =
      NormedSpace.exp ((Complex.I * (t : ℂ)) • WallSeesaw.G Y) := by
  rw [rate_time, mul_div_cancel₀ t hs]

end PMAction.CrossingScale
