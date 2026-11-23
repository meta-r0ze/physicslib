import PMElementaryParticles.EPSpine
import PMElementaryParticles.ChannelPlacement

/-!

**Retired (2026-11-23).** This module uses the internal-D4 placement, which breaks colour and
the weak flip (no internal-D4 placement keeps them). `PMElementaryParticles.EPSector` replaces
it, on the derived sector of `PMElementaryParticles.GaugeSector`. Kept as a check.
# The label rides the packet

A labelled packet is a coset root plus the label's channel vector:
`labelledPacket r c = r + channelE8 c`. Its state has three parts:

| Part | Read by | Ring step |
| --- | --- | --- |
| site | clock reading (`ClockSites.site`) | moves one place (`EPSpine.forward_walk`) |
| generation | glue key (`ClockAlignment.glueKey`) | unchanged (`EPSpine.step_keeps_generation`) |
| label | internal content: pairings with the internal simple roots `p, q, r, s` (`internalContent`) | unchanged (`step_keeps_label`) |

* Channel vectors carry no glue key (`channel_glueKey`): the label never
  changes the generation (`labelledPacket_key`).
* Ring steps are spacetime roots with zero internal content
  (`clockAxis_internalContent`), so they never change the label
  (`walk_keeps_label`).
* Different labels give different internal content
  (`channel_internalContent_injective`), so the label can be read back from the
  packet at any time, relative to its coset root (`label_readout`).

`spine_labelled`: every generation and visible class has a program meeting
all six pillars whose labelled packet keeps its generation and its label while
it walks the ring.

Open: the library's wall rule puts a generation-`g` channel in class
`wallClass g (active c)`. `channelE8` is the placement for the reference
generation `g = 0` (`ChannelPlacement.libraryIndex_channelKey`). For `g = 1, 2`
the placement is not yet rotated by triality; here every generation carries
the same channel vectors.
-/

noncomputable section

namespace PMElementaryParticles.EPLabel

open PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment PMKAutomaton.ClockSites
open PMConstants.PacketGaugeActions
open PMElementaryParticles.ChannelPlacement
open PMElementaryParticles.ProgramClasses PMElementaryParticles.EPSpine

/-- Internal content: the pairings with the internal simple roots. -/
def internalContent (z : V) : Fin 4 → ℤ :=
  ![pair z PMKAutomaton.AlignedSectors.p, pair z PMKAutomaton.AlignedSectors.q,
    pair z PMKAutomaton.AlignedSectors.r, pair z PMKAutomaton.AlignedSectors.s]

theorem internalContent_add (z w : V) :
    internalContent (z + w) = internalContent z + internalContent w := by
  funext i
  fin_cases i <;> simp [internalContent, pair_add_left]

theorem internalContent_nsmul (z : V) (n : ℕ) :
    internalContent (n • z) = n • internalContent z := by
  induction n with
  | zero =>
    funext i; fin_cases i <;> simp [internalContent, pair]
  | succ n ih => rw [succ_nsmul, internalContent_add, ih, succ_nsmul]

/-- Ring steps have zero internal content. -/
theorem clockAxis_internalContent : ∀ f ∈ clockAxisRoots, internalContent f = 0 := by
  decide +kernel

/-- Channel vectors carry no glue key. -/
theorem channel_glueKey : ∀ c : Channels, glueKey (channelE8 c) = 0 := by
  decide +kernel

/-- Different labels have different internal content. -/
theorem channel_internalContent_injective :
    Function.Injective fun c : Channels => internalContent (channelE8 c) := by
  decide +kernel

/-- A coset root carrying a label. -/
def labelledPacket (r : V) (c : Channels) : V := r + channelE8 c

/-- The label never changes the generation. -/
theorem labelledPacket_key (r : V) (c : Channels) :
    glueKey (labelledPacket r c) = glueKey r := by
  rw [labelledPacket, glueKey_add, channel_glueKey, add_zero]

/-- **A ring step never changes the label.** -/
theorem step_keeps_label (z f : V) (hf : f ∈ clockAxisRoots) :
    internalContent (z + f) = internalContent z := by
  rw [internalContent_add, clockAxis_internalContent f hf, add_zero]

theorem walk_keeps_label (z f : V) (hf : f ∈ clockAxisRoots) (n : ℕ) :
    internalContent (z + n • f) = internalContent z := by
  rw [internalContent_add, internalContent_nsmul, clockAxis_internalContent f hf,
    smul_zero, add_zero]

/-- The label is read back from the packet, relative to its coset root. -/
theorem label_readout (r : V) (c : Channels) (f : V) (hf : f ∈ clockAxisRoots) (n : ℕ) :
    internalContent (labelledPacket r c + n • f) - internalContent r =
      internalContent (channelE8 c) := by
  rw [walk_keeps_label _ f hf, labelledPacket, internalContent_add]
  abel

/-- Two labels on the same coset root stay distinguishable on the ring. -/
theorem labels_distinct (r : V) (c c' : Channels) (f : V) (hf : f ∈ clockAxisRoots)
    (n : ℕ) (h : c ≠ c') :
    internalContent (labelledPacket r c + n • f) ≠
      internalContent (labelledPacket r c' + n • f) := by
  intro he
  apply h
  apply channel_internalContent_injective
  have h1 := label_readout r c f hf n
  have h2 := label_readout r c' f hf n
  simp only at h1 h2 ⊢
  rw [← h1, ← h2, he]

/-- **The labelled spine.** Every generation and visible class has a program
meeting all six pillars whose labelled packet keeps its generation and its
label on every forward walk of the ring. -/
theorem spine_labelled (g : Generation) (k : Fin 6) (hk : k ≠ 4) :
    ∃ p : Program, p.generation = g ∧ classOf p.label = k ∧ p.Pillars ∧
      ∀ f ∈ clockAxisRoots, clockReading f = 1 → ∀ n : ℕ,
        glueKey (labelledPacket p.packet p.label + n • f) = g.1 ∧
        internalContent (labelledPacket p.packet p.label + n • f) - internalContent p.packet =
          internalContent (channelE8 p.label) := by
  obtain ⟨p, hg, hc, hp⟩ := spine g k hk
  refine ⟨p, hg, hc, hp, fun f hf h1 n => ⟨?_, label_readout _ _ f hf n⟩⟩
  rw [(forward_walk _ f hf h1 n).1, labelledPacket_key, p.packet_key, hg]

end PMElementaryParticles.EPLabel

end
