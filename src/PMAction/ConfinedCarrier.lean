import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The domain-wall carrier confined to a finite region

`DomainWall` gives one chiral mode per D₄ sector on the infinite slab. A hadron needs that mode
confined to a finite region: the `3×3×3` cube of `PMHadrons`. This file covers the algebra of
the confined construction. The spectrum is computed outside Lean by
`tools/confined_carrier.py`.

**Construction.** Each sector (slice) carries a Wilson–Dirac Hamiltonian `A` on the sites of
the region, with Dirichlet (hard) walls or a confinement mass outside it. The sectors are joined
by the site-diagonal wall hop `B = −(i α₄ + r β)/2`. The total Hamiltonian is
`twoSlice A B = [[A, B], [Bᴴ, A]]`.

* `twoSlice_hermitian`: if the slice Hamiltonian is Hermitian, so is the confined two-slice
  Hamiltonian, for any wall hop and any region.
* `spin_commutes_beta_alpha4`: the spin `Σ_z = −i α₁α₂` commutes with `β α₄`, and therefore
  with the wall chirality `Γ = i β α₄` and with the wall hop. The wall does not reduce the spin.
  Any reduction of `⟨Σ_z⟩` below one comes from the transverse momentum that confinement forces
  on the mode (the `αⱼ` terms), which is the relativistic reduction of `g_A`.
* `axisStep_conjTranspose`, `axisStep_unitary`, `axisStep_unitary'`: the axis step of the
  walk on a finite region. If the truncated hop `N` is Hermitian with `N³ = N`, then
  `R = a·N² + b·N + (1 − N²)` is unitary whenever `|a|² + |b|² = 1` and `ā b + b̄ a = 0`
  (for the walk, `a = cos τ`, `b = i sin τ`). It rotates the modes the hop covers and leaves the
  face modes `1 − N²` unchanged: the identity completion that `CompletionSelection` selects.
* `coefficient_partial`: the hop coefficient (`c² = 0`, `cc† + c†c = 1`, as in
  `LocalUnitary.coefficient_relations`) satisfies `c c† c = c`. With the open shift's
  `S Sᵀ S = S`, this gives `N³ = N` for the truncated hop `S ⊗ c + Sᵀ ⊗ c†`.
* `spin_anticommutes_alpha1`, `spin_anticommutes_alpha2`: `Σ_z` anticommutes with `α₁` and
  `α₂` (it commutes with `α₃`, by `spin_commutes_beta`). So the full carrier Hamiltonian does
  **not** conserve `Σ_z`; only the wall part does. `⟨Σ_z⟩` of the lowest level is an
  expectation value below one, not a conserved spin.

**Status of `g_A` (recorded so it is not fitted later).** With every input fixed by Persistence
Mechanics or geometry, the single free confined carrier gives `(5/3)⟨Σ_z⟩ = 1.377` against the
measured `1.2754` (`+8%`):

| input | value | fixed by |
|---|---|---|
| count | `5/3 = σ/(σ−χ)` | `PMHadrons.AxialCount` |
| region | `3×3×3` | `PMHadrons.MinimalCube` (smallest volume-persistent cube) |
| wall | hard | identity completion (`CompletionSelection`, `axisStep_unitary`) |
| `r`, `M` | `1`, `1` | `DomainWall` (Wilson point) |
| tick | small-tick limit | isotropy: finite `τ` makes `⟨Σ_x⟩, ⟨Σ_y⟩, ⟨Σ_z⟩` differ (`VacuumTangent`) |
| axial density | `Σ_z` | `γ⁵ = Γ = −iα₁α₂α₃` (`WallChiralCurrent`, `VATrace`) |

Every alternative that would close the gap was rejected as a choice rather than a derivation:
a 4-site cube (`1.265`), a soft wall (`M_out ≈ 0.7`), a finite tick (`τ ≈ 0.3–0.5`, anisotropic),
and the ratio `25/27`. The `8%` is what a single free carrier leaves out. Candidates still to
investigate, each something that touches spin or position: the three carriers' mutual
interaction beyond pure colour routing (which leaves spin and position unchanged), and the pion
emission space (`PMHadrons.EmissionSpace`). This value is not used in the neutron rate.

**Numerical result** (`tools/confined_carrier.py`, `M = r = 1`):

| region | wall | lowest `E` | degeneracy | `⟨Σ_z⟩` | `(5/3)⟨Σ_z⟩` |
|---|---|---|---|---|---|
| `3³` | hard | 0.841 | 2 | 0.826 | 1.377 |
| `3³` in `5³` | `M_out = 100` | | 2 | 0.826 | 1.377 |
| `3³` in `5³` | `M_out = 10` | | 2 | 0.822 | 1.369 |
| `3³` in `5³` | `M_out = 3` | | 2 | 0.802 | 1.337 |

For comparison, the single-sector Wilson carrier at `r = 1` gives `0.893` (`g_A = 1.488`). The
measured `g_A = 1.2754` needs `0.765`.

**The wall is hard, by persistence.** A phase persists only if each of its resources is
refreshed (Paper III, `RequirementComplement`). The hadron's resources are the sites of its cube
(`PMHadrons.MinimalCube`), so carrier amplitude on a site outside the cube is not refreshed and
does not persist. Infinite cost means zero amplitude, which is the Dirichlet wall `M_out = ∞`.
Paper V gives the same answer from the other side: colour is internal routing with no external
Map projection (`3_info_transit`), so a carrier has no admissible state outside the hadron. A
finite `M_out` would need a finite external cost for a coloured carrier, and Persistence
Mechanics assigns none. The soft-wall rows are sensitivity checks only.

**Result:** `⟨Σ_z⟩ = 0.826`, so `(5/3)⟨Σ_z⟩ = 1.377`. This is the **single free carrier's
value**: the count `5/3` times one free confined carrier's spin fraction. It is **not the
neutron's `g_A`**, and it is not used in the neutron rate (`NeutronRate.gA = 5/4` still is).
Against the measured `1.2754` it is `+8%`.

**Cube size.** With a hard wall, `⟨Σ_z⟩` depends only on the number of sites per edge
(`r = M = 1` are fixed by `DomainWall`; the lattice-to-energy unit does not enter):

| edge sites | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|
| `⟨Σ_z⟩` | 0.916 | 0.826 | 0.759 | 0.717 | 0.692 |
| `(5/3)⟨Σ_z⟩` | 1.527 | 1.377 | 1.265 | 1.195 | 1.153 |

`MinimalCube.cube_interior_iff` selects 3 (Economy: the smallest volume-persistent cube). Four
sites would come close to the measurement, but nothing in Persistence Mechanics selects 4, so
it is not used. With the geometry fixed, the remaining `+8%` is not in the single carrier. It
lies in what this free-carrier model leaves out: the three carriers' mutual synchronization
(gluon dressing) and the discrete-time walk.

**The walk version** (`tools/confined_walk.py`). The substrate update (`SplitUpdate`,
`WilsonSplit`) is a coin times one rotation per axis. On the cube the truncated hop `N_t` covers
all modes except the face modes `P_j = 1 − N_t²`. `CompletionSelection` (persistence: modes an
update does not reach evolve by the identity) gives the axis step
`R_j = cos τ · N_t² + i sin τ · N_t + P_j`: unitary, local, and with the plain truncation as its
generator. So the hard wall *is* the walk's wall, and as the cube grows the truncation's
`⟨Σ_z⟩` levels off toward the continuum bag value (`0.826, 0.759, 0.717, 0.692, 0.677` for edge
`3–7`). (Completing `N_j` itself by `±P` instead adds a `∓1/2` face potential that binds
surface states; that is not the selected completion.)

**The tick.** In Paper II's vacuum-preserving update `Ũ_τ = (e^{−iτW} R_β(τ)†³) R₀R₁R₂`, the
three axis steps act in order, so at finite `τ` the carrier speeds are `sin τ (cos 5τ, cos 3τ,
cos τ)` (`VacuumTangent`), equal only as `τ → 0`. On the cube the same anisotropy appears in the
spin: at `τ = 0.3` the lowest level has `⟨Σ_x, Σ_y, Σ_z⟩ = 0.785, 0.797, 0.776`. A hadron's `g_A`
cannot depend on the axis, and the cube's symmetry is fixed geometry, so the physical regime is
the small-tick limit, which Paper II controls (`VacuumErrorRate`: `‖Ũ_{T/N}^N − e^{TG}‖ ≤ 2a²T²/N`).
There the carrier is the Hamiltonian's: `⟨Σ_z⟩ = 0.826` on `3³` (`τ ≤ 0.05`: anisotropy below
`0.1%`). A finite-tick reduction would need an ordering that persistence selects and that
keeps isotropy; Paper II leaves the uniqueness of the ordering open.
-/

namespace PMAction.ConfinedCarrier
open Matrix

variable {m : Type*}

/-- The confined two-slice Hamiltonian: slice Hamiltonian `A` on each sector, wall hop `B`. -/
def twoSlice (A B : Matrix m m ℂ) : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  fromBlocks A B Bᴴ A

theorem twoSlice_hermitian (A B : Matrix m m ℂ) (hA : A.IsHermitian) :
    (twoSlice A B).IsHermitian := by
  show (fromBlocks A B Bᴴ A)ᴴ = fromBlocks A B Bᴴ A
  rw [fromBlocks_conjTranspose, conjTranspose_conjTranspose, hA.eq]

section Spin
variable {R : Type*} [Ring R]

/-- `α₁α₂` commutes with `β α₄` when each `αⱼ` (`j = 1, 2`) anticommutes with `β` and with
`α₄`. Hence `Σ_z = −i α₁α₂` commutes with `Γ = i β α₄`. -/
theorem spin_commutes_beta_alpha4 (a1 a2 β α4 : R)
    (h1β : a1 * β = -(β * a1)) (h2β : a2 * β = -(β * a2))
    (h14 : a1 * α4 = -(α4 * a1)) (h24 : a2 * α4 = -(α4 * a2)) :
    a1 * a2 * (β * α4) = β * α4 * (a1 * a2) := by
  calc a1 * a2 * (β * α4) = a1 * (a2 * β) * α4 := by noncomm_ring
    _ = -(a1 * β * (a2 * α4)) := by rw [h2β]; noncomm_ring
    _ = a1 * β * α4 * a2 := by rw [h24]; noncomm_ring
    _ = -(β * (a1 * α4) * a2) := by rw [h1β]; noncomm_ring
    _ = β * α4 * (a1 * a2) := by rw [h14]; noncomm_ring

/-- `α₁α₂` also commutes with `β` alone, so it commutes with the whole wall hop
`−(i α₄ + r β)/2`; see `spin_commutes_beta_alpha4` for the `α₄` part in product form. -/
theorem spin_commutes_beta (a1 a2 β : R)
    (h1β : a1 * β = -(β * a1)) (h2β : a2 * β = -(β * a2)) :
    a1 * a2 * β = β * (a1 * a2) := by
  calc a1 * a2 * β = a1 * (a2 * β) := by noncomm_ring
    _ = -(a1 * β * a2) := by rw [h2β]; noncomm_ring
    _ = β * (a1 * a2) := by rw [h1β]; noncomm_ring

/-- `α₁α₂` commutes with `α₄`. -/
theorem spin_commutes_alpha4 (a1 a2 α4 : R)
    (h14 : a1 * α4 = -(α4 * a1)) (h24 : a2 * α4 = -(α4 * a2)) :
    a1 * a2 * α4 = α4 * (a1 * a2) :=
  spin_commutes_beta a1 a2 α4 h14 h24

/-- `α₁` anticommutes with `α₁α₂`, hence with `Σ_z = −i α₁α₂`. -/
theorem spin_anticommutes_alpha1 (a1 a2 : R) (h1 : a1 * a1 = 1)
    (hac : a1 * a2 = -(a2 * a1)) :
    a1 * (a1 * a2) = -(a1 * a2 * a1) := by
  have h' : a2 * a1 = -(a1 * a2) := by rw [hac, neg_neg]
  have e : a1 * a2 * a1 = -a2 := by
    calc a1 * a2 * a1 = a1 * (a2 * a1) := by noncomm_ring
      _ = a1 * (-(a1 * a2)) := by rw [h']
      _ = -(a1 * a1 * a2) := by noncomm_ring
      _ = -a2 := by rw [h1, one_mul]
  rw [e, neg_neg, ← mul_assoc, h1, one_mul]

/-- `α₂` anticommutes with `α₁α₂`, hence with `Σ_z = −i α₁α₂`. -/
theorem spin_anticommutes_alpha2 (a1 a2 : R) (h2 : a2 * a2 = 1)
    (hac : a1 * a2 = -(a2 * a1)) :
    a2 * (a1 * a2) = -(a1 * a2 * a2) := by
  have h' : a2 * a1 = -(a1 * a2) := by rw [hac, neg_neg]
  have e : a1 * a2 * a2 = a1 := by rw [mul_assoc, h2, mul_one]
  rw [e, ← mul_assoc, h', neg_mul, mul_assoc, h2, mul_one]

/-- The hop coefficient is a partial isometry: `c² = 0` and `cc† + c†c = 1` give `c c† c = c`. -/
theorem coefficient_partial (c cd : R) (h0 : c * c = 0) (h1 : c * cd + cd * c = 1) :
    c * cd * c = c := by
  calc c * cd * c = c * (c * cd + cd * c) - c * c * cd := by noncomm_ring
    _ = c := by rw [h1, h0]; noncomm_ring

/-- A block-unitary completion: if `W V = Q` for an idempotent `Q` that `V` and `W` live
inside, then `(W + (1 − Q))(V + (1 − Q)) = 1`. -/
theorem block_completion (Q V W : R) (hQQ : Q * Q = Q) (hWQ : W * Q = W) (hQV : Q * V = V)
    (hWV : W * V = Q) : (W + (1 - Q)) * (V + (1 - Q)) = 1 := by
  calc (W + (1 - Q)) * (V + (1 - Q))
      = W * V + (W - W * Q) + (V - Q * V) + (1 - Q - Q + Q * Q) := by noncomm_ring
    _ = 1 := by rw [hWV, hWQ, hQV, hQQ]; abel

end Spin

section AxisStep
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The walk's axis step on a finite region: `a` on the modes the truncated hop `N` covers
(`N²`), the hop itself with amplitude `b`, and the identity on the face modes `1 − N²`. For the
substrate walk, `a = cos τ` and `b = i sin τ`. -/
def axisStep (N : Matrix n n ℂ) (a b : ℂ) : Matrix n n ℂ :=
  a • (N * N) + b • N + (1 - N * N)

theorem axisStep_conjTranspose (N : Matrix n n ℂ) (hN : N.IsHermitian) (a b : ℂ) :
    (axisStep N a b)ᴴ = axisStep N (star a) (star b) := by
  simp only [axisStep, conjTranspose_add, conjTranspose_sub, conjTranspose_smul,
    conjTranspose_mul, conjTranspose_one, hN.eq]

/-- **The axis step is unitary.** For a Hermitian truncated hop with `N³ = N`, the step
`R = a N² + b N + (1 − N²)` satisfies `R† R = 1` when `|a|² + |b|² = 1` and `ā b + b̄ a = 0`. -/
theorem axisStep_unitary (N : Matrix n n ℂ) (hN : N.IsHermitian) (hN3 : N * N * N = N)
    (a b : ℂ) (h1 : star a * a + star b * b = 1) (h2 : star a * b + star b * a = 0) :
    (axisStep N a b)ᴴ * axisStep N a b = 1 := by
  have hNQ : N * (N * N) = N := by rw [← mul_assoc, hN3]
  have hQQ : N * N * (N * N) = N * N := by rw [← mul_assoc, hN3]
  rw [axisStep_conjTranspose N hN]
  have hWV : (star a • (N * N) + star b • N) * (a • (N * N) + b • N) = N * N := by
    rw [show (star a • (N * N) + star b • N) * (a • (N * N) + b • N)
        = (star a * a + star b * b) • (N * N) + (star a * b + star b * a) • N by
      simp only [add_mul, mul_add, smul_mul_smul_comm, hQQ, hN3, hNQ]; module]
    rw [h1, h2, one_smul, zero_smul, add_zero]
  have hWQ : (star a • (N * N) + star b • N) * (N * N) = star a • (N * N) + star b • N := by
    simp only [add_mul, smul_mul_assoc, hQQ, hNQ]
  have hQV : N * N * (a • (N * N) + b • N) = a • (N * N) + b • N := by
    simp only [mul_add, mul_smul_comm, hQQ, hN3]
  have := block_completion (N * N) (a • (N * N) + b • N) (star a • (N * N) + star b • N)
    hQQ hWQ hQV hWV
  simpa only [axisStep, add_assoc] using this

/-- The walk's case: `a = cos τ`, `b = i sin τ`. -/
theorem axisStep_unitary' (N : Matrix n n ℂ) (hN : N.IsHermitian) (hN3 : N * N * N = N)
    (τ : ℝ) :
    (axisStep N (Real.cos τ) (Complex.I * Real.sin τ))ᴴ *
      axisStep N (Real.cos τ) (Complex.I * Real.sin τ) = 1 := by
  apply axisStep_unitary N hN hN3
  · have h := Real.cos_sq_add_sin_sq τ
    have hC : ((Real.cos τ : ℂ)) ^ 2 + ((Real.sin τ : ℂ)) ^ 2 = 1 := by exact_mod_cast h
    simp only [RCLike.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
    linear_combination hC - ((Real.sin τ : ℂ)) ^ 2 * Complex.I_sq
  · simp only [RCLike.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring

end AxisStep

end PMAction.ConfinedCarrier
