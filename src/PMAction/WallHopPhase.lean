import PMAction.ConcreteFermion

/-!
# The phase an in-wall hop carries on one chirality: a quarter turn that cancels in every loop

`PersistenceMechanics.InformationTransfer`: every transfer channel carries a phase and a cost,
amplitude `e^{iφ − βc/2}`. For generation mixing the channel is a carrier hop on one wall
(`PMFlavor.GenerationLabel`: a single-wall shift), and the charged current acts on one wall and one
chirality (`WallChiralCurrent`). This module computes the phase of such a hop.

A lattice hop along direction `j` is the Wilson form `−(i αⱼ + r β)/2` (`DomainWall`). On one
chirality, with `P = 1 + Γ` (twice the projector):
* `sandwich_beta`, `sandwich_beta_minus`: `P β P = 0`, because `β` anticommutes with `Γ`
  (`ConcreteFermion.beta_gamma`) and `Γ² = 1`. The Wilson term leaves the chirality.
* `chiral_hop`: so `P · hop · P = −(i/2) · P αⱼ P`. Restricted to one chirality, an in-wall hop is
  a quarter turn `−i` times a Hermitian matrix (`alpha_hermitian`, `alpha_gamma`): its amplitude is
  `−i/2` times a real eigenvalue.
* `quarter_turns_cancel`: a reduced coupling through a class joins one leg to the conjugate of the
  other (`PMFlavor.LinkFlux.kronC`, `t₁ t̄₂`). Two quarter-turn legs give a real product. So
  in-wall kinetic hops alone give every reduced coupling a real value, and the loop flux is `0` or
  `π`: no CP phase.

So the CP flux the CKM needs (`PMFlavor.TransferGenerator`, numerically `49.1 ± 1.1°`) does not come
from the in-wall kinetic hop. What is left: the node-crossing hops, which are spinor-class
displacements with a time-axis component `±1` (`PMFlavor.ExchangeAxis.spinor_touch`), where the
hop is not a spatial `αⱼ` term; or a background holonomy around the transfer loop. Neither is
computed here.
-/

noncomputable section
namespace PMAction.WallHopPhase
open Matrix ConcreteFermion Complex

theorem gamma_beta : gamma * beta = -(beta * gamma) := by
  rw [beta_gamma, neg_neg]

/-- **The Wilson term leaves the chirality**: `(1 + Γ) β (1 + Γ) = 0`. -/
theorem sandwich_beta : (1 + gamma) * beta * (1 + gamma) = 0 := by
  calc (1 + gamma) * beta * (1 + gamma) = (beta + gamma * beta) * (1 + gamma) := by
        rw [add_mul, one_mul]
    _ = (beta - beta * gamma) * (1 + gamma) := by rw [gamma_beta, sub_eq_add_neg]
    _ = beta * (1 - gamma * gamma) := by noncomm_ring
    _ = 0 := by rw [gamma_square, sub_self, mul_zero]

/-- The same on the other chirality: `(1 − Γ) β (1 − Γ) = 0`. -/
theorem sandwich_beta_minus : (1 - gamma) * beta * (1 - gamma) = 0 := by
  calc (1 - gamma) * beta * (1 - gamma) = (beta - gamma * beta) * (1 - gamma) := by
        rw [sub_mul, one_mul]
    _ = (beta + beta * gamma) * (1 - gamma) := by rw [gamma_beta, sub_neg_eq_add]
    _ = beta * (1 - gamma * gamma) := by noncomm_ring
    _ = 0 := by rw [gamma_square, sub_self, mul_zero]

/-- The Wilson hop along spatial direction `j` (with `r = 1`). -/
def hop (j : Fin 3) : Spin := (-(1 / 2 : ℂ)) • (I • alpha j + beta)

/-- **On one chirality an in-wall hop is a quarter turn**: `P · hop · P = −(i/2) · P αⱼ P`. -/
theorem chiral_hop (j : Fin 3) :
    (1 + gamma) * hop j * (1 + gamma) = (-(I / 2)) • ((1 + gamma) * alpha j * (1 + gamma)) := by
  set P : Spin := 1 + gamma with hP
  have hs : P * beta * P = 0 := by rw [hP]; exact sandwich_beta
  simp only [hop, smul_add, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hs, smul_zero,
    add_zero, smul_smul]
  congr 1
  ring

/-- **Two quarter-turn legs give a real coupling**: `(i a)·conj(i b) = a b`. A reduced coupling
`t₁ t̄₂` of in-wall kinetic legs is real, so their loop flux is `0` or `π`. -/
theorem quarter_turns_cancel (a b : ℝ) :
    (I * a) * (starRingEnd ℂ) (I * b) = ((a * b : ℝ) : ℂ) := by
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  linear_combination (-(a : ℂ) * b) * I_sq

end PMAction.WallHopPhase
