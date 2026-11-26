import PMAction.ConcreteFermion

/-!
# The chirality-flip part of an in-wall hop is the on-site mass operator

`PMAction.CompositeSchur` places the composite mass in the on-site chirality-flip slot `δβ`, under
the premise that a single-wall carrier flips chirality. This module checks that premise against the
hop's own Dirac structure.

An in-wall hop along direction `j` is the Wilson form `−(i αⱼ + r β)/2` (`DomainWall`,
`WallHopPhase`). With the concrete representation of `ConcreteFermion`:
* `hop_split`: the hop is `keep j + flip r`, with `keep j = −(i/2) αⱼ` and `flip r = −(r/2) β`.
* `keep_commutes`: `keep j` commutes with `Γ` (`alpha_gamma`): it keeps chirality.
* `flip_anticommutes`: `flip r` anticommutes with `Γ` (`beta_gamma`): it flips chirality.
* `flip_is_mass`: `flip r` is the on-site mass operator `β` times `−r/2`, so it acts in the slot of
  `δβ` (`WallSeesaw`: `a ↔ b` on wall 1, `d ↔ c` on wall 2).

So the premise holds for the Wilson part: a carrier hop of amplitude `t` puts `−r t/2` in the
chirality-flip slot, and its kinetic part keeps chirality and gives no mass. At the Wilson point
`r = 1` that is `κ = −t/2` for every class, so the ratios of the composite masses
(`CompositeSchur.composite_expansion`) are the ratios of the carrier hop amplitudes. `NodeAmplitude` supplies the class admittance ratio. Identifying it with a Hamiltonian-rate
ratio requires the native event duration and update law, and the crossing-to-flip rate remains open.

Premise kept: the class carrier is an in-wall hop of this Wilson form. A carrier with another Dirac
structure would need its own split.
-/

noncomputable section
namespace PMAction.CarrierFlip
open Matrix ConcreteFermion

/-- An in-wall hop along `j` with Wilson parameter `r`. -/
def hop (r : ℂ) (j : Fin 3) : Spin := (-(1 / 2 : ℂ)) • (Complex.I • alpha j + r • beta)

/-- Its kinetic part. -/
def keep (j : Fin 3) : Spin := (-(1 / 2 : ℂ) * Complex.I) • alpha j

/-- Its Wilson part. -/
def flip (r : ℂ) : Spin := (-(r / 2)) • beta

/-- **The hop is a kinetic part plus a Wilson part.** -/
theorem hop_split (r : ℂ) (j : Fin 3) : hop r j = keep j + flip r := by
  ext i k
  simp only [hop, keep, flip, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- **The kinetic part keeps chirality.** -/
theorem keep_commutes (j : Fin 3) : keep j * gamma = gamma * keep j := by
  rw [keep, Matrix.smul_mul, Matrix.mul_smul, alpha_gamma]

/-- **The Wilson part flips chirality.** -/
theorem flip_anticommutes (r : ℂ) : flip r * gamma = -(gamma * flip r) := by
  rw [flip, Matrix.smul_mul, Matrix.mul_smul, beta_gamma, smul_neg]

/-- **The Wilson part is the on-site mass operator `β`**, scaled by `−r/2`. -/
theorem flip_is_mass (r : ℂ) : flip r = (-(r / 2)) • beta := rfl

end PMAction.CarrierFlip
