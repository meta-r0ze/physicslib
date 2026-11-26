import PMElementaryParticles.FootprintNoGo
import PMElementaryParticles.TierLedger
import PMKAutomaton.ClockPlaneProjection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Two-root excursions: algebraic candidates and the typed-program boundary

No event-count reading is selected here. `restoringPairs` enumerates ordered
pairs of roots in the starting generation's own glue class. The sum has zero
internal content. `relabelPairs` instead tests distinct weak or colour partners
with the same electric charge, using the generation's existing channel placement.
Labels are read relative to the original coset root, as in EPLabel.label_readout;
no new seed or vacuum readout is chosen at the endpoint.

EPLabel has no operational predicate for an admissible intermediate state.
If that state must itself be a packet represented by `EPSpine.Program`, the
requested first hop is impossible: k + k = 0, while Program requires a nonzero
key. `programCompatiblePairs` imposes only this necessary key condition and
is already empty. This does not prohibit a temporary zero-key state in a larger
machine model; that admission rule is not present in EPLabel.

The unadmitted algebraic candidates are reported separately. Their relative
spacetime geometry can change with the glue class. It is not a physical event
count. Projection coordinates are twice the usual orthonormal D4 epsilon
coordinates. The clock covector on that space is minus half their sum before
doubling. `spatialPart` removes the component along that covector, and is
multiplied by four to keep integer arithmetic. Neither scale changes a span.
The zero displacement is counted separately from pure clock or spatial moves.

Finite certificates use `decide +kernel`. Real-span consequences use linear
algebra; finrank over the reals is not a decidable enumeration.

## Per-generation and visible-species report

| Generation / glue key | Visible class | Base species | Channels | Typed-compatible pairs | Raw pairs / displacements | Raw spacetime span | Raw clock histogram | Raw spatial span | Declared tiers, unassigned |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 / (0,1) | 0 | up | 3 | 0 | 512 / 33 | 4 | A | 3 | {0,2,3} |
| 0 / (0,1) | 0 | down | 3 | 0 | 512 / 33 | 4 | A | 3 | {0,1,2} |
| 0 / (0,1) | 1 | up | 3 | 0 | 512 / 33 | 4 | A | 3 | {0,2,3} |
| 0 / (0,1) | 2 | down | 3 | 0 | 512 / 33 | 4 | A | 3 | {0,1,2} |
| 0 / (0,1) | 3 | electron | 1 | 0 | 512 / 33 | 4 | A | 3 | {0,1,2} |
| 0 / (0,1) | 3 | neutrino | 1 | 0 | 512 / 33 | 4 | A | 3 | {0,1,2} |
| 0 / (0,1) | 5 | electron | 1 | 0 | 512 / 33 | 4 | A | 3 | {0,1,2} |
| 1 / (1,0) | 0 | up | 3 | 0 | 512 / 33 | 4 | B | 3 | {0,2,3} |
| 1 / (1,0) | 0 | down | 3 | 0 | 512 / 33 | 4 | B | 3 | {0,1,2} |
| 1 / (1,0) | 1 | up | 3 | 0 | 512 / 33 | 4 | B | 3 | {0,2,3} |
| 1 / (1,0) | 2 | down | 3 | 0 | 512 / 33 | 4 | B | 3 | {0,1,2} |
| 1 / (1,0) | 3 | electron | 1 | 0 | 512 / 33 | 4 | B | 3 | {0,1,2} |
| 1 / (1,0) | 3 | neutrino | 1 | 0 | 512 / 33 | 4 | B | 3 | {0,1,2} |
| 1 / (1,0) | 5 | electron | 1 | 0 | 512 / 33 | 4 | B | 3 | {0,1,2} |
| 2 / (1,1) | 0 | up | 3 | 0 | 512 / 33 | 4 | B | 3 | {0,2,3} |
| 2 / (1,1) | 0 | down | 3 | 0 | 512 / 33 | 4 | B | 3 | {0,1,2} |
| 2 / (1,1) | 1 | up | 3 | 0 | 512 / 33 | 4 | B | 3 | {0,2,3} |
| 2 / (1,1) | 2 | down | 3 | 0 | 512 / 33 | 4 | B | 3 | {0,1,2} |
| 2 / (1,1) | 3 | electron | 1 | 0 | 512 / 33 | 4 | B | 3 | {0,1,2} |
| 2 / (1,1) | 3 | neutrino | 1 | 0 | 512 / 33 | 4 | B | 3 | {0,1,2} |
| 2 / (1,1) | 5 | electron | 1 | 0 | 512 / 33 | 4 | B | 3 | {0,1,2} |

A counts distinct displacements: `-2:1, -1:6, 0:19, +1:6, +2:1`.
B counts distinct displacements: `-1:10, 0:13, +1:10`.
Negative readings are the signed representatives of residues 41 and 42 modulo 43.
Counts are per channel; no colour multiplicity or traffic weight is applied.
All typed-compatible displacement sets and clock histograms are empty; both spans are zero.
All raw charge-conserving label-changing pair sets are empty, with zero spans and empty histograms.

`ProtocolInventory.baseProtocol_carrier` derives the base-species names from
`CarrierChannels.axis`, `positiveSign` and `wall`. Class 0 contains both up and
down; class 3 contains both electron and neutrino. Thus there are seven visible
class/species groups, and 21 report rows, covering 45 channel/generation indices.
This does not change the 15 class/generation witnesses of `EPSpine.programs_card`.
No generation is named electron/muon/tau or up/charm/top here.

`generationAt_index` agrees with `EPLabelGen.genIndex`: index 0 is key (0,1),
index 1 is (1,0), and index 2 is (1,1). This map comes from the channel placement,
not the tier ledger. `TierLedger.tiersFor` supplies sets; `wireTier` takes a free
`WireTierAssignment`. No derived map connects a generation index to an entry.

No computed column reproduces the lepton/down set {0,1,2} or the up set {0,2,3}.
Numerically, pure-clock displacement counts (2,0,0) share {0,2} with both sets,
but miss 1 and 3, identify two generations, and have no species dependence.
Treating those counts as tiers would itself select a new reading; none is selected.
The full raw displacement sets are distinct, so a functional can read generation
information from their shapes. The constraints supply no event-count functional.

-/

namespace PMElementaryParticles.GluedExcursions
open Matrix
open PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment
open PMElementaryParticles.EPSpine PMElementaryParticles.EPLabel
open PMElementaryParticles.EPLabelGen PMConstants.PacketGaugeActions

abbrev Key := ZMod 2 × ZMod 2
abbrev Wt := Fin 4 → ℤ

/-- The established library index, not a species tier assignment. -/
def generationAt : Fin 3 → Generation
  | 0 => ⟨(0, 1), by decide⟩
  | 1 => ⟨(1, 0), by decide⟩
  | 2 => ⟨(1, 1), by decide⟩

theorem generationAt_index : ∀ g, genIndex (generationAt g) = g := by decide +kernel

theorem key_double_zero : ∀ k : Key, k + k = 0 := by decide +kernel

/-- A returning pair need not use the starting key. Using that key kills the
nonzero intermediate generation slot. -/
theorem intermediate_key_nonzero_iff : ∀ k h : Key, k + h ≠ 0 ↔ h ≠ k := by
  decide +kernel

theorem first_hop_key_zero (p : Program) (r : V)
    (hr : glueKey r = p.generation.1) : glueKey (genPacket p + r) = 0 := by
  rw [glueKey_add, genPacket_key, hr, key_double_zero]

theorem no_typed_intermediate (p : Program) (r : V)
    (hr : glueKey r = p.generation.1) :
    ¬ ∃ q : Program, genPacket q = genPacket p + r := by
  rintro ⟨q, hq⟩
  have hk := congrArg glueKey hq
  rw [genPacket_key, first_hop_key_zero p r hr] at hk
  exact q.generation.2 hk

/-- The 64 roots of the selected glue key, with content calculated once. -/
def rootData (g : Fin 3) : List (V × Wt) :=
  (rootsOfKey (generationAt g).1).map fun r => (r, internalContent r)

def rootPairs (g : Fin 3) : List (V × V) :=
  (rootsOfKey (generationAt g).1).flatMap fun r =>
    (rootsOfKey (generationAt g).1).map fun s => (r, s)

/-- Raw ordered pairs with internal content restored. No admission is asserted. -/
def restoringPairs (g : Fin 3) : List (V × V) :=
  (rootData g).flatMap fun x =>
    ((rootData g).filter fun y => x.2 + y.2 = 0).map fun y => (x.1, y.1)

/-- Distinct one-action partners; electric charge must be conserved. -/
def partners (c : Channels) : Finset Channels :=
  (Finset.univ : Finset Channels).filter fun d =>
    d ≠ c ∧ (d = flipWeak c ∨ ∃ a b : Fin 3, d = permuteColour a b c) ∧
      CarrierChannels.electric d = CarrierChannels.electric c

def targetIncrements (g : Fin 3) (c : Channels) : Finset Wt :=
  (partners c).image fun d => internalContent (channelE8Gen g d) -
    internalContent (channelE8Gen g c)

def rootContents (g : Fin 3) : Finset Wt :=
  ((rootsOfKey (generationAt g).1).map internalContent).toFinset

def internalIncrements (g : Fin 3) : Finset Wt :=
  (rootContents g).biUnion fun x => (rootContents g).image fun y => x + y

/-- Raw label-changing and charge-conserving ordered pairs. -/
def relabelPairs (g : Fin 3) (c : Channels) : List (V × V) :=
  (rootPairs g).filter fun p =>
    internalContent p.1 + internalContent p.2 ∈ targetIncrements g c

/-- Necessary condition for the intermediate state to be any typed EP program.
It fails before any additional admission or traffic conditions can be tested. -/
def programCompatiblePairs (g : Fin 3) (c : Channels) (changeLabel : Bool) : List (V × V) :=
  ((rootData g).filter fun x => (generationAt g).1 + glueKey x.1 ≠ 0).flatMap fun x =>
    ((rootData g).filter fun y =>
      if changeLabel then x.2 + y.2 ∈ targetIncrements g c else x.2 + y.2 = 0).map
        fun y => (x.1, y.1)

def displacements (g : Fin 3) : Finset V :=
  ((restoringPairs g).map fun p => p.1 + p.2).toFinset

/-- Twice the orthogonal spacetime epsilon coordinates in the aligned placement. -/
def projection2 : Matrix (Fin 4) (Fin 8) ℤ :=
  !![-1,0,0,0,0,0,0,0; -1,0,0,0,0,0,0,2;
     -1,0,0,0,0,0,2,-2; -1,0,0,0,0,2,-2,0]

def epsilon2 (z : V) : Wt := projection2 *ᵥ z

def spacetimeColumns : Matrix (Fin 8) (Fin 4) ℤ :=
  fun i j => (![a, b, c, beta] j) i

/-- The projection is fixed by the aligned Gram pairing, not fitted to counts. -/
theorem projection_pairings :
    projection2.transpose * PMSubstrate.Channels.d4Basis =
      (2 : ℤ) • (PMSubstrate.Lattices.gram * spacetimeColumns) := by decide +kernel

theorem projection_coordinates : projection2 * spacetimeColumns =
    (2 : ℤ) • PMSubstrate.Channels.d4Basis := by decide +kernel

def epsilonDisplacements (g : Fin 3) : Finset Wt := (displacements g).image epsilon2

/-- Four times the part orthogonal to the induced clock covector. -/
def spatialPart (v : Wt) : Wt := fun i => 4 * v i - ∑ j, v j

def spatialDisplacements (g : Fin 3) : Finset Wt :=
  (epsilonDisplacements g).image spatialPart

def clockHistogram (g : Fin 3) : List (ℕ × ℕ) :=
  (List.range 43).filterMap fun (n : ℕ) =>
    let count := ((displacements g).filter fun z => clockReading z = (n : ZMod 43)).card
    if count = 0 then none else some (n, count)

def pairClockHistogram (g : Fin 3) : List (ℕ × ℕ) :=
  (List.range 43).filterMap fun (n : ℕ) =>
    let count := ((restoringPairs g).filter fun p => clockReading (p.1 + p.2) = (n : ZMod 43)).length
    if count = 0 then none else some (n, count)

/-- Zero, pure clock, pure spatial and mixed distinct displacement counts. -/
def splitCounts (g : Fin 3) : ℕ × ℕ × ℕ × ℕ :=
  let S := epsilonDisplacements g
  ((S.filter (· = 0)).card,
   (S.filter fun v => v ≠ 0 ∧ spatialPart v = 0).card,
   (S.filter fun v => v ≠ 0 ∧ ∑ i, v i = 0).card,
   (S.filter fun v => (∑ i, v i) ≠ 0 ∧ spatialPart v ≠ 0).card)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Complete finite raw-pair geometry in library generation order. -/
theorem restoring_counts : ∀ g : Fin 3,
    (restoringPairs g).length = 512 ∧ (displacements g).card = 33 ∧
      (epsilonDisplacements g).card = 33 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem displacement_clocks :
    clockHistogram 0 = [(0,19),(1,6),(2,1),(41,1),(42,6)] ∧
      clockHistogram 1 = [(0,13),(1,10),(42,10)] ∧
      clockHistogram 2 = [(0,13),(1,10),(42,10)] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ordered_pair_clocks :
    pairClockHistogram 0 = [(0,304),(1,96),(2,8),(41,8),(42,96)] ∧
      pairClockHistogram 1 = [(0,256),(1,128),(42,128)] ∧
      pairClockHistogram 2 = [(0,256),(1,128),(42,128)] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem displacement_split : splitCounts 0 = (1,2,18,12) ∧
    splitCounts 1 = (1,0,12,20) ∧ splitCounts 2 = (1,0,12,20) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Clock readings here are the actual ClockRing readings of spacetime sums. -/
theorem clock_projection_certificate : ∀ g : Fin 3, ∀ z ∈ displacements g,
    PMSubstrate.Lattices.pairing z PMSubstrate.ClockPlane.cv = 0 ∧
      4 * PMSubstrate.Lattices.pairing z PMSubstrate.ClockPlane.cu = -(∑ i, epsilon2 z i) ∧
      clockReading z = (((-(∑ i, epsilon2 z i)) / 4 : ℤ) : ZMod 43) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- No same-starting-key pair has a typed-program intermediate, for any label. -/
theorem programCompatible_empty : ∀ (g : Fin 3) (c : Channels) (change : Bool),
    programCompatiblePairs g c change = [] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The doubled channel code has no charge-conserving partner increment among
these two-root internal increments. This test does not use intermediate admission. -/
theorem partner_increments_disjoint : ∀ (g : Fin 3) (c : Channels),
    Disjoint (targetIncrements g c) (internalIncrements g) := by decide +kernel

theorem relabelPairs_empty (g : Fin 3) (c : Channels) : relabelPairs g c = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro p hp ht
  have ht' := of_decide_eq_true ht
  have hi : internalContent p.1 + internalContent p.2 ∈ internalIncrements g := by
    obtain ⟨r, hr, h⟩ := List.mem_flatMap.mp hp
    obtain ⟨s, hs, he⟩ := List.mem_map.mp h
    cases he
    exact Finset.mem_biUnion.mpr ⟨internalContent r,
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩),
      Finset.mem_image.mpr ⟨internalContent s,
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨s, hs, rfl⟩), rfl⟩⟩
  exact Finset.disjoint_left.mp (partner_increments_disjoint g c) ht' hi

/-- The report groups channels by the existing carrier axis/sign species rule. -/
def speciesChannels (k : Fin 6) (b : ProtocolInventory.BaseProtocol) : Finset Channels :=
  Finset.univ.filter fun c => ProgramClasses.classOf c = k ∧
    ProtocolInventory.baseProtocol c = some b

/-- Multiplicities of the seven visible class/species groups. -/
theorem class_species_inventory :
    (speciesChannels 0 .up).card = 3 ∧ (speciesChannels 0 .down).card = 3 ∧
    (speciesChannels 1 .up).card = 3 ∧ (speciesChannels 2 .down).card = 3 ∧
    (speciesChannels 3 .electron).card = 1 ∧ (speciesChannels 3 .neutrino).card = 1 ∧
    (speciesChannels 5 .electron).card = 1 ∧
    (∀ c ∈ ProgramClasses.visibleChannels, ∃ b, c ∈ speciesChannels (ProgramClasses.classOf c) b) := by
  decide +kernel

/-- Two equal-key increments restore the original glue coset. -/
theorem pair_returns (z r₁ r₂ : V) (k : Key)
    (h₁ : glueKey r₁ = k) (h₂ : glueKey r₂ = k) :
    glueKey ((z + r₁) + r₂) = glueKey z := by
  rw [glueKey_add, glueKey_add, h₁, h₂, add_assoc, key_double_zero, add_zero]

/-- This condition is exactly restoration of the fixed-base EPLabel readout. -/
theorem restoringPairs_mem (g : Fin 3) (r₁ r₂ : V) :
    (r₁, r₂) ∈ restoringPairs g ↔
      r₁ ∈ rootsOfKey (generationAt g).1 ∧ r₂ ∈ rootsOfKey (generationAt g).1 ∧
        internalContent (r₁ + r₂) = 0 := by
  simp [restoringPairs, rootData, List.mem_flatMap, internalContent_add]

/-- A nontrivial weak flip changes electric charge. -/
theorem weak_partner_charge_changes : ∀ c : Channels,
    flipWeak c ≠ c → CarrierChannels.electric (flipWeak c) ≠ CarrierChannels.electric c := by
  decide +kernel

theorem partner_counts : ∀ c : Channels,
    (partners c).card = if CarrierChannels.axis c = 0 then 0 else 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Equal ranks do not identify the full raw displacement sets. -/
theorem displacement_sets_distinct :
    epsilonDisplacements 0 ≠ epsilonDisplacements 1 ∧
      epsilonDisplacements 0 ≠ epsilonDisplacements 2 ∧
      epsilonDisplacements 1 ≠ epsilonDisplacements 2 := by decide +kernel

/-! ## Real span: finite integer witnesses and field-independent consequences -/

/-- Four independent spacetime directions present in every raw displacement set. -/
def frame : Fin 4 → Wt :=
  ![![2,2,0,0], ![2,-2,0,0], ![0,0,2,2], ![0,0,2,-2]]

/-- Three independent directions in the clock-orthogonal spatial hyperplane. -/
def spaceFrame (i : Fin 3) : Wt := fun j =>
  if j = i.castSucc then 8 else if j = 3 then -8 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem frame_mem : ∀ (g : Fin 3) (i : Fin 4), frame i ∈ epsilonDisplacements g := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem spaceFrame_mem : ∀ (g : Fin 3) (i : Fin 3), spaceFrame i ∈ spatialDisplacements g := by
  decide +kernel

noncomputable section

def asReal (v : Wt) : Fin 4 → ℝ := fun i => (v i : ℝ)

def realSpan (S : Finset Wt) : Submodule ℝ (Fin 4 → ℝ) :=
  Submodule.span ℝ (asReal '' (S : Set Wt))

private theorem realSpan_empty : realSpan ∅ = ⊥ := by
  unfold realSpan
  rw [Finset.coe_empty, Set.image_empty, Submodule.span_empty]

private theorem mem_realSpan {S : Finset Wt} {v : Wt} (h : v ∈ S) :
    asReal v ∈ realSpan S := Submodule.subset_span ⟨v, h, rfl⟩

private def axisCoefficients : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1/4,1/4,0,0; 1/4,-1/4,0,0; 0,0,1/4,1/4; 0,0,1/4,-1/4]

private theorem axis_expansion (i : Fin 4) :
    (∑ j : Fin 4, axisCoefficients i j • asReal (frame j)) = Pi.single i 1 := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [axisCoefficients, asReal, frame, Fin.sum_univ_four]

/-- The real span has all four aligned spacetime dimensions. -/
theorem spacetime_span_top (g : Fin 3) : realSpan (epsilonDisplacements g) = ⊤ := by
  have haxis : ∀ i : Fin 4, Pi.single i (1 : ℝ) ∈ realSpan (epsilonDisplacements g) := by
    intro i
    rw [← axis_expansion i]
    exact (realSpan _).sum_mem fun j _ =>
      (realSpan _).smul_mem _ (mem_realSpan (frame_mem g j))
  apply top_unique
  intro v _
  have hv : v = ∑ i : Fin 4, v i • Pi.single i (1 : ℝ) := by
    ext j
    fin_cases j <;> simp [Pi.single_apply]
  rw [hv]
  exact (realSpan _).sum_mem fun i _ => (realSpan _).smul_mem _ (haxis i)

theorem spacetime_span_dimension (g : Fin 3) :
    Module.finrank ℝ (realSpan (epsilonDisplacements g)) = 4 := by
  rw [spacetime_span_top]; simp

/-- The clock-orthogonal spatial hyperplane in this orthonormal coordinate chart. -/
def sumLinear : (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, v i
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.mul_sum]

theorem spatial_span_ker (g : Fin 3) : realSpan (spatialDisplacements g) = sumLinear.ker := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    change (∑ i, asReal (spatialPart w) i) = 0
    norm_num [asReal, spatialPart, Fin.sum_univ_four]
  · intro v hv
    have hs : v 0 + v 1 + v 2 + v 3 = 0 := by
      simpa [sumLinear, Fin.sum_univ_four, add_assoc] using hv
    have hexpr : v = ∑ i : Fin 3, (v i.castSucc / 8) • asReal (spaceFrame i) := by
      ext j
      fin_cases j <;> norm_num [asReal, spaceFrame, Fin.sum_univ_three] <;> linarith
    rw [hexpr]
    exact (realSpan _).sum_mem fun i _ =>
      (realSpan _).smul_mem _ (mem_realSpan (spaceFrame_mem g i))

/-- Removing one nonzero clock direction leaves three real spatial dimensions. -/
theorem spatial_span_dimension (g : Fin 3) :
    Module.finrank ℝ (realSpan (spatialDisplacements g)) = 3 := by
  rw [spatial_span_ker]
  have hr : LinearMap.range sumLinear = ⊤ := LinearMap.range_eq_top.mpr (by
    intro y
    exact ⟨Pi.single 0 y, by simp [sumLinear]⟩)
  have h := sumLinear.finrank_range_add_finrank_ker
  rw [hr] at h
  have h' : 1 + Module.finrank ℝ sumLinear.ker = 4 := by simpa using h
  omega

/-- No typed-compatible displacement survives the necessary intermediate-key test. -/
def compatibleDisplacements (g : Fin 3) (c : Channels) (change : Bool) : Finset Wt :=
  ((programCompatiblePairs g c change).map fun p => epsilon2 (p.1 + p.2)).toFinset

theorem compatible_geometry_empty (g : Fin 3) (c : Channels) (change : Bool) :
    compatibleDisplacements g c change = ∅ := by
  simp [compatibleDisplacements, programCompatible_empty]

theorem compatible_span_dimension (g : Fin 3) (c : Channels) (change : Bool) :
    Module.finrank ℝ (realSpan (compatibleDisplacements g c change)) = 0 := by
  rw [compatible_geometry_empty, realSpan_empty, finrank_bot]

/-- The compatible family also has zero spatial span. -/
theorem compatible_spatial_span_dimension (g : Fin 3) (c : Channels) (change : Bool) :
    Module.finrank ℝ (realSpan ((compatibleDisplacements g c change).image spatialPart)) = 0 := by
  rw [compatible_geometry_empty, Finset.image_empty, realSpan_empty, finrank_bot]

def compatibleClockReadings (g : Fin 3) (c : Channels) (change : Bool) : Finset (ZMod 43) :=
  ((programCompatiblePairs g c change).map fun p => clockReading (p.1 + p.2)).toFinset

theorem compatible_clock_empty (g : Fin 3) (c : Channels) (change : Bool) :
    compatibleClockReadings g c change = ∅ := by
  simp [compatibleClockReadings, programCompatible_empty]

/-- Empty raw partner family: no intermediate-admission choice changes this result. -/
def relabelDisplacements (g : Fin 3) (c : Channels) : Finset Wt :=
  ((relabelPairs g c).map fun p => epsilon2 (p.1 + p.2)).toFinset

theorem relabel_geometry_empty (g : Fin 3) (c : Channels) : relabelDisplacements g c = ∅ := by
  simp [relabelDisplacements, relabelPairs_empty]

theorem relabel_span_dimension (g : Fin 3) (c : Channels) :
    Module.finrank ℝ (realSpan (relabelDisplacements g c)) = 0 := by
  rw [relabel_geometry_empty, realSpan_empty, finrank_bot]

end

end PMElementaryParticles.GluedExcursions
