import PMConstants.CarrierActions
import PMAction.Machine.CarrierWeyl

/-!
# Where the doublet sign lives, and why the wire cannot see it

The up and down protocols (and `ν`, `e`) are weak partners: carriers `±2eᵢ` on one axis.

* `weak_partner_is_antipode`: the weak sign exchange (`CarrierActions.signExchange`, the refresh's
  action on the reference's sector) is the antipode `v ↦ −v` (`CarrierParity.antipode`).
* `words_commute_antipode`: every native root word (`CarrierWeyl.lookup`, including `β`) commutes
  with the antipode.

So every native operator treats a carrier and its weak partner identically: the up and down
protocols (and `ν`, `e`) have equal matrix elements under any operator built from the native
words. This is the general form of `DoubletReflection`.

**The wire.** The wire's vacuum sector is the antipodally odd sector
(`CarrierVacuumSector.range_iff_odd`): an admitted state has `ψ(−v) = −ψ(v)`, equal weight on both
weak partners. The even complement is given zero action "by our extension convention, not ruled
out as nonpersistent" (`CarrierVacuumEvolution.even_inert`; "selecting the physical odd sector is
still an obligation"). A single protocol carrier `|±2eᵢ⟩ = (|oddᵢ⟩ ± |evenᵢ⟩)/√2` reads the same odd
mode with opposite sign, which no mass (`|·|`) sees.

**What a wire mode is (correction, 2026-11).** The odd modes of one class are the wire's eight
Dirac components: `4` axes × `2` sectors are the four spinor components on each of the two walls
(`CarrierVacuumSector.embedding`, `beta_intertwining`: the wall's `β`, `Γ`, `αⱼ` act on these axis
modes). So a wire mode is a spinor component, not a protocol. An earlier reading here put the lepton
pair on axis `0` and the up/down pair of colour `i` on axis `i`; that assigns protocols to spinor
components and is withdrawn. With it, colour would act on the spinor index, which no colour action that
commutes with `β` and the `αⱼ` can do (`PMAction.ColourRegister.commutant_scalar`). On the wire the
antipode is `−1` on every component (a global sign), so the weak exchange carries no protocol
information there. Protocol identity (lepton or quark, colour, weak partner) is a separate register
from the wire's spinor components; the 16-carrier packet (`CarrierActions.Packet`) is that register's
count and its gauge actions, not the wire's spinor space.

**Consequence.** Nothing on the wire tells the up protocol from the down protocol, and with the
correction above this is structural: the partners are not wire modes at all. For any
Hamiltonian `H`, the two partners' expectations differ by `2 Re ⟨odd|H|even⟩`, the odd/even cross
term, which is zero whenever `H` commutes with the antipode or the even sector is inert. This is
why every up/down source tried so far failed.

The partner (up/down, `ν`/`e`) difference must come from the protocol register: a coupling that
depends on its charges (the right-handed hypercharge, PMElementaryParticles REVIEW) or on how a
protocol reads the wire.
-/

namespace PMElementaryParticles.DoubletSign
open PMAction PMAction.CarrierEvents PMConstants.CarrierRepresentation

theorem weak_partner_is_antipode : ∀ v : V,
    PMConstants.CarrierActions.signExchange v = CarrierParity.antipode 0 v := by decide +kernel

theorem words_commute_antipode : ∀ (c : Fin 3) (g : Fin 6) (v : Carrier c),
    CarrierWeyl.lookup c g (CarrierParity.antipode c v) =
      CarrierParity.antipode c (CarrierWeyl.lookup c g v) := by decide +kernel

end PMElementaryParticles.DoubletSign
