import PMKAutomaton.AlignedSectors
import PMElementaryParticles.ChannelVectors
import PMConstants.PreparationSelection
import PMElementaryParticles.WireReferenceCost

/-!
# Placing the sixteen channels in the aligned internal D4

`ChannelVectors.channelCoord` writes each channel in the doubled epsilon
coordinates of a D4. `PMKAutomaton.AlignedSectors` supplies a clock-aligned
internal D4 with simple roots `p, q, r, s`. This module converts the channel
coordinates to those simple-root coordinates and embeds them in E8 through the
sector-1 columns.

The internal class is read from the halved pairings with `p`, `r` and `s`.
`internalKey` computes the corresponding class directly on E8 roots. On the
192 glued roots it is a fixed bijection of `ClockAlignment.glueKey`; the inverse
table is stated in `matchingGlueKey`.

From the library definitions, `ControlledGluedRegister.wallClass g b = if b
then g - 1 else g + 1` and `ProtocolInventory.active` is the wall bit. With the
generation's own class the third key `(1,0)`, the library class indices are

* `0`: internal key `(1,0)`, matching `glueKey` coset `(0,1)`, the vector coset
  carrying `cu`, signature `(7,7,2)`;
* `1`: internal key `(1,1)`, matching `glueKey` coset `(1,0)`, signature
  `(4,4,8)`;
* `2`: internal key `(0,1)`, matching `glueKey` coset `(1,1)`, signature
  `(4,4,0)`.

Thus library class `0` is the clock-carrying vector coset. The reference
identification `g = 0` is then a consequence of the library conventions, not a
separate premise.
-/

noncomputable section

namespace PMElementaryParticles.ChannelPlacement

open Matrix
open PMKAutomaton.ClockRing
open PMKAutomaton.ClockAlignment
open PMKAutomaton.AlignedSectors
open PMSubstrate
open PMSubstrate.Channels
open PMElementaryParticles.ChannelVectors
open PMElementaryParticles.ProtocolInventory

abbrev Key := ZMod 2 × ZMod 2

/-- The internal simple root named `r` in `AlignedSectors`, renamed here to
avoid clashes with root variables. -/
def t : V := PMKAutomaton.AlignedSectors.r

/-- The internal D4 class key: the two parity pairings with the internal
simple system. -/
def internalKey (z : V) : Key :=
  (((PMSubstrate.Lattices.pairing z p + PMSubstrate.Lattices.pairing z t : ℤ) : ZMod 2),
    ((PMSubstrate.Lattices.pairing z p + PMSubstrate.Lattices.pairing z s : ℤ) : ZMod 2))

theorem internalKey_add (z w : V) :
    internalKey (z + w) = internalKey z + internalKey w := by
  ext <;> simp [internalKey, pair_add_left] <;> ring

theorem internalKey_spacetime :
    ∀ z ∈ spacetimeRoots, internalKey z = 0 := by
  decide +kernel

theorem internalKey_internal :
    ∀ z ∈ internalRoots, internalKey z = 0 := by
  decide +kernel

/-- The 192 roots in the three nonzero glue cosets. -/
def cosetRoots : List V := rootList.filter fun z => glueKey z ≠ 0

theorem cosetRoots_length : cosetRoots.length = 192 := by decide +kernel

/-- The inverse table from an internal key to its matching `glueKey` coset. -/
def matchingGlueKey (k : Key) : Key :=
  if k = (1, 0) then (0, 1) else if k = (1, 1) then (1, 0) else (1, 1)

/-- **The internal key is a fixed bijection of the glue key on the cosets.** -/
theorem matchingGlueKey_internal (z : V) (hz : z ∈ cosetRoots) :
    matchingGlueKey (internalKey z) = glueKey z := by
  revert z
  decide +kernel

/-- The three-pair table, written in the internal-to-glue direction. -/
theorem matchingGlueKey_table :
    matchingGlueKey (1, 0) = (0, 1) ∧
      matchingGlueKey (1, 1) = (1, 0) ∧
      matchingGlueKey (0, 1) = (1, 1) := by
  decide

/-- Inverse of `d4Basis`: a doubled epsilon vector with even coordinate sum
gives integer D4 simple-root coordinates. -/
def d4FromEps (y : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![y 0, y 0 + y 1, ((∑ i, y i) / 2) - y 3, (∑ i, y i) / 2]

theorem d4Basis_mulVec_fromEps (y : Fin 4 → ℤ) (hy : Even (∑ i, y i)) :
    d4Basis *ᵥ d4FromEps y = y := by
  obtain ⟨a, ha⟩ := hy
  ext i
  fin_cases i <;>
    (simp [d4Basis, d4FromEps, mulVec, dotProduct, Fin.sum_univ_succ] at ha ⊢; try omega)

theorem channelCoord_sum_even (c : PMConstants.PacketGaugeActions.Channels) :
    Even (∑ i, channelCoord c i) := by
  revert c
  decide +kernel

theorem channelCoord_d4 (c : PMConstants.PacketGaugeActions.Channels) :
    d4Basis *ᵥ d4FromEps (channelCoord c) = channelCoord c :=
  d4Basis_mulVec_fromEps (channelCoord c) (channelCoord_sum_even c)

/-- Put a four-vector in the last four coordinates, leaving sector 0 zero. -/
def liftSector1 (w : Fin 4 → ℤ) : Fin 8 → ℤ :=
  fun i => if h : (i : ℕ) < 4 then 0 else w ⟨(i : ℕ) - 4, by omega⟩

/-- The sector-1 E8 embedding. -/
def sector1Embed (w : Fin 4 → ℤ) : V :=
  alignedSectorBasis *ᵥ liftSector1 w

/-- The E8 vector of a channel. It is twice the internal D4 minimal vector. -/
def channelE8 (c : PMConstants.PacketGaugeActions.Channels) : V :=
  sector1Embed (d4FromEps (channelCoord c))

/-- The halved internal pairings define the channel's internal class. -/
def channelKey (c : PMConstants.PacketGaugeActions.Channels) : Key :=
  ((((PMSubstrate.Lattices.pairing (channelE8 c) p + PMSubstrate.Lattices.pairing (channelE8 c) t) / 2 : ℤ) : ZMod 2),
   (((PMSubstrate.Lattices.pairing (channelE8 c) p + PMSubstrate.Lattices.pairing (channelE8 c) s) / 2 : ℤ) : ZMod 2))

theorem channelE8_injective : Function.Injective channelE8 := by
  decide +kernel

/-- Inactive channels all carry the internal vector key. -/
theorem inactive_channelKey (c : PMConstants.PacketGaugeActions.Channels)
    (hc : active c = false) : channelKey c = (1, 1) := by
  revert c
  decide +kernel

/-- Active channels all carry the internal triality key. -/
theorem active_channelKey (c : PMConstants.PacketGaugeActions.Channels)
    (hc : active c = true) : channelKey c = (0, 1) := by
  revert c
  decide +kernel

theorem channel_keys_distinct :
    ((1, 1) : Key) ≠ (0, 1) ∧ ((1, 1) : Key) ≠ 0 ∧ ((0, 1) : Key) ≠ 0 := by
  decide

/-- The library class index read from `wallClass` with the generation's own
class the third key. -/
def libraryIndex (k : Key) : Fin 3 :=
  if k = (1, 0) then 0 else if k = (1, 1) then 1 else 2

/-- `ControlledGluedRegister.wallClass` says `false` is `g + 1` and `true` is
`g - 1`. With `g = 0` (the reference class), `active = false` is class `1` and
`active = true` is class `2`. -/
theorem wallClass_zero :
    ControlledGluedRegister.wallClass 0 false = 1 ∧
      ControlledGluedRegister.wallClass 0 true = 2 := by
  decide

theorem libraryIndex_channelKey (c : PMConstants.PacketGaugeActions.Channels) :
    libraryIndex (channelKey c) = ControlledGluedRegister.wallClass 0 (active c) := by
  revert c
  decide +kernel

/-- The table in library order. -/
theorem library_table :
    libraryIndex (1, 0) = 0 ∧ matchingGlueKey (1, 0) = (0, 1) ∧
    libraryIndex (1, 1) = 1 ∧ matchingGlueKey (1, 1) = (1, 0) ∧
    libraryIndex (0, 1) = 2 ∧ matchingGlueKey (0, 1) = (1, 1) := by
  decide

/-- **The reference class is the clock-carrying vector coset.** -/
theorem referenceClass_eq_clock :
    libraryIndex (1, 0) = 0 ∧ matchingGlueKey (1, 0) = glueKey ClockPlane.cu := by
  refine ⟨by decide, ?_⟩
  rw [cu_key]
  decide

/-- The two restoring classes: `g = 1` is the conjugate-spinor coset, `g = 2`
the spinor coset. -/
theorem restoring_classes :
    libraryIndex (1, 1) = 1 ∧ libraryIndex (0, 1) = 2 ∧
      matchingGlueKey (1, 1) = (1, 0) ∧ matchingGlueKey (0, 1) = (1, 1) := by
  decide

/-! ## The packet channels in the substrate channel set -/

/-- The packet's sixteen channels placed in the substrate channel set: the
internal (`true`) sector of `ChannelSymmetry.channels`, at the derived
coordinates `channelCoord`.  The sector `true` is the second (`p,q,r,s`) block
of `AlignedSectors.alignedSectorBasis`, the internal D4; `ChannelSymmetry.channels`
indexes the two D4 factors by `Bool` (`false` = first, `true` = second). -/
def packetChannel (c : PMConstants.PacketGaugeActions.Channels) :
    Bool × PMSubstrate.ChannelSymmetry.V4 :=
  (true, channelCoord c)

/-- The derived placement is injective. -/
theorem packetChannel_injective : Function.Injective packetChannel := by
  intro c d h
  exact channelCoord_injective (congrArg Prod.snd h)

/-- The derived placement lands in the substrate's 32 channels. -/
theorem packetChannel_mem : ∀ c, packetChannel c ∈ PMSubstrate.ChannelSymmetry.channels := by
  decide +kernel

/-- **The packet preparation is uniform** through the derived placement.  This
is the placement-free `PreparationSelection.packet_preparation_uniform`
instantiated at `packetChannel`, so it needs no chosen `chanTable` entries. -/
theorem packet_preparation_uniform_channelCoord
    (P : Bool × PMSubstrate.ChannelSymmetry.V4 → ℝ)
    (hP : ∀ i, ∀ x ∈ PMSubstrate.ChannelSymmetry.channels,
      P (PMSubstrate.ChannelSymmetry.gen i x) = P x)
    (p : PMConstants.PacketGaugeActions.Channels → ℝ) (k : ℝ)
    (hp : ∀ c, p c = k * P (packetChannel c)) (hsum : ∑ c, p c = 1) :
    p = PersistenceMechanics.LawSelection.uniform :=
  PMConstants.PreparationSelection.packet_preparation_uniform
    packetChannel packetChannel_injective packetChannel_mem P hP p k hp hsum

/-- The `WireReferenceCost` uniformity bound through the derived placement. -/
theorem uniform_if_inherited_channelCoord
    (P : Bool × PMSubstrate.ChannelSymmetry.V4 → ℝ)
    (hP : ∀ i, ∀ x ∈ PMSubstrate.ChannelSymmetry.channels,
      P (PMSubstrate.ChannelSymmetry.gen i x) = P x)
    (p : PMConstants.PacketGaugeActions.Channels → ℝ) (k : ℝ)
    (hp : ∀ c, p c = k * P (packetChannel c))
    (hsum : ∑ c, p c = 1) (c : PMConstants.PacketGaugeActions.Channels) : p c = 1 / 16 :=
  PMElementaryParticles.WireReferenceCost.uniform_if_inherited
    packetChannel packetChannel_injective packetChannel_mem P hP p k hp hsum c

end PMElementaryParticles.ChannelPlacement
