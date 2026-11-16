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

**How many wires.** The 16 channels are the vector-class carriers in the two sectors
(`CarrierActions.Packet = V ⊕ V`, the same as `CarrierVacuumSector.Labels 0`). The wire's admitted
modes are the antipodally odd combinations: `4` axes × `2` sectors = `8` modes per class
(`CarrierVacuumEvolution.odd_finrank`). So there are not 16 wires: each wire mode is one axis in
one sector, shared by an antipodal pair, which is a weak pair. Axis `0` carries the lepton pair
(`ν`/`e` in the left sector; the sterile vacancy and `e` in the right), axis `i = 1, 2, 3` carries
the up and down pair of colour `i`. A protocol is the sign with which a channel reads its axis
mode. With the three classes (generation labels) this is `24` modes, the observed single-carrier
count (`CarrierClassBundle.observed_card`).

**Consequence.** As written, nothing on the wire tells the up protocol from the down protocol: the
native operators commute with the antipode, and the wire keeps only antipode-odd states. For any
Hamiltonian `H`, the two partners' expectations differ by `2 Re ⟨odd|H|even⟩`, the odd/even cross
term, which is zero whenever `H` commutes with the antipode or the even sector is inert. This is
why every up/down source tried so far failed.

**Where the sign can enter (both outside the current wire model).**
1. *The reference.* It is one carrier, `+2e₀`, not its antipode (`CarrierParity.no_fixed_antipode`).
   As a state it has an even component, and any operator involving it (its maintenance, a
   projection onto it) need not commute with the antipode. This is the only antipode-odd object in
   the setup. `BetaReference`: `β` carries axis `2` to the reference axis, so the reference's sign
   becomes up-versus-down on that axis.
2. *The even complement.* If it carries action, the cross term `⟨odd|H|even⟩` is where the up/down
   difference lives. Its dynamics is a convention today.
Hypercharge (`Y = B − L + 2T₃` on the right) also distinguishes the partners, but as a charge
value; the native words do not carry it.

**Test.** Give the even complement the action induced by the reference's maintenance (the only
antipode-odd input), compute the cross term per (protocol, label), and check whether it is nonzero
only where `BetaReference` puts it (the up protocol's vector-class label on the paired axis) and
with which size. If the cross term is zero, the wire as built cannot carry the observed up/down
difference, and the up/down difference must come from the protocol layer (how a protocol reads the
wire), not from the wire.
-/

namespace PMElementaryParticles.DoubletSign
open PMAction PMAction.CarrierEvents PMConstants.CarrierRepresentation

theorem weak_partner_is_antipode : ∀ v : V,
    PMConstants.CarrierActions.signExchange v = CarrierParity.antipode 0 v := by decide +kernel

theorem words_commute_antipode : ∀ (c : Fin 3) (g : Fin 6) (v : Carrier c),
    CarrierWeyl.lookup c g (CarrierParity.antipode c v) =
      CarrierParity.antipode c (CarrierWeyl.lookup c g v) := by decide +kernel

end PMElementaryParticles.DoubletSign
