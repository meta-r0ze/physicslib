import PMChecks.PMElementaryParticles.EPLabel

/-!

**Retired (2026-11-23).** This module uses the internal-D4 placement, which breaks colour and
the weak flip (no internal-D4 placement keeps them). `PMElementaryParticles.EPSector` replaces
it, on the derived sector of `PMElementaryParticles.GaugeSector`. Kept as a check.
# Channel placement per generation

The library wall rule puts a generation-`g` channel in internal class
`ControlledGluedRegister.wallClass g (active c)`. `ChannelPlacement.channelE8`
is the placement for the reference generation `g = 0`
(`ChannelPlacement.libraryIndex_channelKey`). Generation `g`'s placement is
the certified internal triality (`GluedRegister.triality`, order three,
moving each carrier class to the next) applied `g` times to the channel
coordinates (`channelE8Gen`).

* `channelKeyGen_wallClass`: in every generation every channel sits in the
  class the wall rule requires.
* `channelGen_glueKey`, `channelGen_internalContent_injective`: the
  rotated vectors still carry no glue key and still separate the labels.
* `genIndex`: the library index of a generation's glue coset
  (`(0,1) ↦ 0`, the clock coset; `(1,0) ↦ 1`; `(1,1) ↦ 2`;
  `ChannelPlacement.library_table`).

`spine_generations`: every generation and visible class has a program meeting
all six pillars whose packet carries that generation's own channel vector, in
the wall-rule class, and keeps generation and label on every ring walk.
-/

noncomputable section

namespace PMElementaryParticles.EPLabelGen

open PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment PMKAutomaton.ClockSites
open PMConstants.PacketGaugeActions
open PMElementaryParticles.ChannelVectors PMElementaryParticles.ChannelPlacement
open PMElementaryParticles.ProtocolInventory
open PMElementaryParticles.ProgramClasses PMElementaryParticles.EPSpine
open PMElementaryParticles.EPLabel

/-- Generation `g`'s channel coordinates: triality applied `g` times. -/
def channelCoordGen (g : Fin 3) (c : Channels) : Fin 4 → ℤ :=
  (PMElementaryParticles.GluedRegister.triality)^[g.val] (channelCoord c)

/-- Generation `g`'s channel vector in E8. -/
def channelE8Gen (g : Fin 3) (c : Channels) : V :=
  sector1Embed (d4FromEps (channelCoordGen g c))

/-- The halved internal pairings: the channel's internal class. -/
def channelKeyGen (g : Fin 3) (c : Channels) : Key :=
  ((((pair (channelE8Gen g c) PMKAutomaton.AlignedSectors.p +
      pair (channelE8Gen g c) t) / 2 : ℤ) : ZMod 2),
   (((pair (channelE8Gen g c) PMKAutomaton.AlignedSectors.p +
      pair (channelE8Gen g c) PMKAutomaton.AlignedSectors.s) / 2 : ℤ) : ZMod 2))

/-- Generation `0` is the reference placement. -/
theorem channelE8Gen_zero (c : Channels) : channelE8Gen 0 c = channelE8 c := rfl

/-- The rotated coordinates are D4 vectors (even coordinate sum). -/
theorem channelCoordGen_sum_even : ∀ (g : Fin 3) (c : Channels),
    Even (∑ i, channelCoordGen g c i) := by
  decide +kernel

/-- **Every channel sits in the class the wall rule requires, in every generation.** -/
theorem channelKeyGen_wallClass : ∀ (g : Fin 3) (c : Channels),
    libraryIndex (channelKeyGen g c) = ControlledGluedRegister.wallClass g (active c) := by
  decide +kernel

/-- The rotated channel vectors carry no glue key. -/
theorem channelGen_glueKey : ∀ (g : Fin 3) (c : Channels), glueKey (channelE8Gen g c) = 0 := by
  decide +kernel

/-- In every generation, different labels have different internal content. -/
theorem channelGen_internalContent_injective : ∀ g : Fin 3,
    Function.Injective fun c : Channels => internalContent (channelE8Gen g c) := by
  decide +kernel

/-- The library index of a generation's glue coset. -/
def genIndex (g : Generation) : Fin 3 :=
  if g.1 = (0, 1) then 0 else if g.1 = (1, 0) then 1 else 2

theorem genIndex_bijective : Function.Bijective genIndex := by decide

/-- A coset root carrying its generation's channel vector. -/
def genPacket (p : Program) : V := p.packet + channelE8Gen (genIndex p.generation) p.label

theorem genPacket_key (p : Program) : glueKey (genPacket p) = p.generation.1 := by
  rw [genPacket, glueKey_add, channelGen_glueKey, add_zero, p.packet_key]

/-- The label reads back from the packet on every walk. -/
theorem genPacket_readout (p : Program) (f : V) (hf : f ∈ clockAxisRoots) (n : ℕ) :
    internalContent (genPacket p + n • f) - internalContent p.packet =
      internalContent (channelE8Gen (genIndex p.generation) p.label) := by
  rw [walk_keeps_label _ f hf, genPacket, internalContent_add]
  abel

/-- **The spine, per generation.** Every generation and visible class has a
program meeting all six pillars whose packet carries that generation's own
channel vector, in the wall-rule class, and keeps its generation and its label
on every forward walk of the ring. -/
theorem spine_generations (g : Generation) (k : Fin 6) (hk : k ≠ 4) :
    ∃ p : Program, p.generation = g ∧ classOf p.label = k ∧ p.Pillars ∧
      libraryIndex (channelKeyGen (genIndex g) p.label) =
        ControlledGluedRegister.wallClass (genIndex g) (active p.label) ∧
      ∀ f ∈ clockAxisRoots, clockReading f = 1 → ∀ n : ℕ,
        glueKey (genPacket p + n • f) = g.1 ∧
        internalContent (genPacket p + n • f) - internalContent p.packet =
          internalContent (channelE8Gen (genIndex g) p.label) := by
  obtain ⟨p, hg, hc, hp⟩ := spine g k hk
  subst hg
  refine ⟨p, rfl, hc, hp, channelKeyGen_wallClass _ _, fun f hf h1 n => ⟨?_, ?_⟩⟩
  · rw [(forward_walk _ f hf h1 n).1, genPacket_key]
  · exact genPacket_readout p f hf n

end PMElementaryParticles.EPLabelGen

end
