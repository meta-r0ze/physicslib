import PMAction.WallExchange
import PMAction.WallSeesaw
import Mathlib.Analysis.Matrix.PosDef
import PMConstants.HermitianMass

/-!
# θ̄ = θ from the wall exchange that is a symmetry

`HermitianMass` needed the link mass matrices to be Hermitian, argued from "the two D₄ sectors are
copies, so the update is invariant under exchanging them". Paper II showed that the plain swap of
the walls is not a symmetry of the domain-wall Hamiltonian (`WallChiralCurrent.plain_wall_exchange_fails`),
because the walls carry opposite chirality. Paper II's `WallExchange` supplies the exchange that is
one: swap the walls *and* apply the spinor parity `β`, reversing momentum. With a flavour link `Y`
between the walls, it maps `H_Y(k)` to `H_{Yᴴ}(−k)`, so it is a symmetry exactly when `Yᴴ = Y`.

* `link_hermitian`: invariance under the wall-parity exchange makes the inter-wall link Hermitian.
* `thetaBar_from_exchange`: with invariant up and down links of positive spectrum, `θ̄ = θ`
  (`HermitianMass.thetaBar_eq_theta`). With `PersistenceClosures.strict_vafa_witten` and
  `VacuumModulus.strict_modulus`, `θ̄ = 0`.

Relation to `SectorExchange`: its `exchange_hermitian` uses the plain swap on an abstract block
generator and says informally that the exchange is combined with parity. This module makes that
precise on the actual Hamiltonian: the plain swap fails, the wall-parity exchange holds, and it
forces the link to be Hermitian. `SectorExchange.thetaBar_zero` (the doublet phase cancelling)
still applies on top.

**The light masses** (`thetaBar_from_light`). The zero-mode masses are not the link itself.
Paper II's `WallSeesaw` computes them: the zero-energy Schur complement onto the chiral zero modes
gives the Dirac mass `M = δ² Y⁻¹` (a seesaw: `M Mᴴ = δ⁴ (Yᴴ Y)⁻¹`, light masses `δ²/σᵢ(Y)`). A
Hermitian positive link gives a Hermitian positive light mass, so with exchange-symmetric,
positive up and down links the light masses give `θ̄ = θ`.

Premise (narrowed): the vacuum update is invariant under the wall-parity exchange, the symmetry of
the actual Hamiltonian that relates the two identical sectors, and the zero-mode mass matrices
are these inter-wall links.
-/

noncomputable section
namespace PMConstants.WallParityExchange
open Matrix PMAction WallExchange

/-- **Invariance under the wall-parity exchange makes the link Hermitian.** -/
theorem link_hermitian {f : Type*} [Fintype f] [DecidableEq f] (k : Fin 3 → ℝ) (δ : ℝ)
    (Y : Matrix f f ℂ) (hsym : P * H k δ Y * P = H (-k) δ Y) : Y.IsHermitian :=
  (exchange_symmetry_iff k δ Y).mp hsym

/-- **θ̄ = θ from the exchange symmetry.** -/
theorem thetaBar_from_exchange (θ : ℝ) {Mu Md : Matrix (Fin 3) (Fin 3) ℂ} (k : Fin 3 → ℝ) (δ : ℝ)
    (su : P * H k δ Mu * P = H (-k) δ Mu) (sd : P * H k δ Md * P = H (-k) δ Md)
    (pu : ∀ i, 0 < (link_hermitian k δ Mu su).eigenvalues i)
    (pd : ∀ i, 0 < (link_hermitian k δ Md sd).eigenvalues i) :
    HermitianMass.thetaBar θ Mu Md = θ :=
  HermitianMass.thetaBar_eq_theta θ _ _ pu pd

open scoped ComplexOrder in
/-- **θ̄ = θ for the light (seesaw) masses.** -/
theorem thetaBar_from_light (θ δ : ℝ) (hδ : δ ≠ 0) {Yu Yd : Matrix (Fin 3) (Fin 3) ℂ}
    (pu : Yu.PosDef) (pd : Yd.PosDef) :
    HermitianMass.thetaBar θ (WallSeesaw.light δ Yu) (WallSeesaw.light δ Yd) = θ :=
  HermitianMass.thetaBar_eq_theta θ (WallSeesaw.light_posDef Yu pu δ hδ).1
    (WallSeesaw.light_posDef Yd pd δ hδ).1
    (Matrix.PosDef.eigenvalues_pos (WallSeesaw.light_posDef Yu pu δ hδ))
    (Matrix.PosDef.eigenvalues_pos (WallSeesaw.light_posDef Yd pd δ hδ))

end PMConstants.WallParityExchange

