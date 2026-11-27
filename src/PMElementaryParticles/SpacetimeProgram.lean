import PMElementaryParticles.EPSpine
import PMElementaryParticles.FootprintNoGo
import PMSubstrate.SpeciesFootprints
import PMSubstrate.PersistencePremises
import PMKAutomaton.ClockSymmetry

/-!
# Ring capacity and spatial extension

A registration is traffic. A held event is occupancy. No equality of these
counts is assumed here. The ring bound applies to registrations, including
programs that do not satisfy the pillars.

A family of ring programs lifts the existing ring predicates pointwise. It
is not yet a spatial execution: no root path is identified with those rings.
The aligned chart has no root along a fixed spatial clock line. Thus an
exact geometric one-line reduction to EPSpine.Program needs an additional
encoding or a different meaning of line. It cannot be claimed from the
pointwise family equivalence.

Margin applies only to differing bit rings. It gives 42 per bit ring, not
42 per two-bit spatial line. An arbitrary spatial line has bound 84 for its
relevant registrations. With Hamming distance one that bound improves to 42.
The requirements R and the identification with held events remain open.
-/

noncomputable section
namespace PMElementaryParticles.SpacetimeProgram
open PMElementaryParticles.IsolatedExcitation
open PMElementaryParticles.RingRates PMElementaryParticles.ProgramWitness
open PMElementaryParticles.RingSurvivors
open PMElementaryParticles.HeavyFlipControl

open PMKAutomaton
open PMSubstrate.E8Values

/-- A port step preserves the number of occupied Boolean ports. -/
theorem portStep_population {n : ℕ} (either : Bool)
    (r : Fin n → IsolatedRequests) (P : RingReceiver.PortField n) :
    portBitCountN n (RingReceiver.portStep either r P) = portBitCountN n P := by
  calc
    _ = portBitCountN n (RingReceiver.arrivals P) := by
      unfold portBitCountN
      apply Finset.sum_congr rfl
      intro x _
      rw [portStep_apply]
      exact portBitCount_applyGuard _ _
    _ = _ := portBitCountN_arrivals n P

/-- One localized bit can register at most once per tick. -/
theorem tickCount_le_population {n : ℕ} (either : Bool)
    (r : Fin n → IsolatedRequests) (P : RingReceiver.PortField n) :
    tickCount either r P ≤ portBitCountN n P := by
  rw [← portBitCountN_arrivals n P]
  apply Finset.sum_le_sum
  intro x _
  generalize RingReceiver.arrivals P x = q
  rcases q with ⟨a,b⟩
  cases a <;> cases b <;> simp [portBitCountPorts] <;> split <;> omega

/-- This holds for every request field and every horizon, without Capacity. -/
theorem registrations_le_horizon {n : ℕ} (either : Bool)
    (r : Fin n → IsolatedRequests) (x0 : Fin n) (T : ℕ) :
    localizedSumN n either r x0 T ≤ T := by
  have hp : ∀ t : ℕ, portBitCountN n
      ((RingReceiver.portStep either r)^[t] (localizedPortsN n x0 activePacket)) = 1 := by
    intro t
    induction t with
    | zero => simpa [active_activePacket] using localizedPortsN_occupancy n x0 activePacket
    | succ t ih => rw [Function.iterate_succ_apply', portStep_population, ih]
  calc
    _ ≤ ∑ _t ∈ Finset.range T, 1 := by
      apply Finset.sum_le_sum
      intro t _
      rw [sum_flag_eq_tick]
      exact (tickCount_le_population either r _).trans_eq (hp t)
    _ = T := by simp

def registrationTotal (p : EPSpine.Program) : ℕ :=
  registrations p.toRing 0 + registrations p.toRing 1

theorem program_registration_bound (p : EPSpine.Program) :
    registrationTotal p ≤ 2 * Delta := by
  have h0 := registrations_le_horizon true (p.firing 0) p.x0 43
  have h1 := registrations_le_horizon true (p.firing 1) p.x0 43
  change registrations p.toRing 0 + registrations p.toRing 1 ≤ 86
  change localizedSumN 43 true (p.firing 0) p.x0 43 +
    localizedSumN 43 true (p.firing 1) p.x0 43 ≤ 86
  omega

/-- A footprint bound needs its explicit traffic-to-occupancy bridge. -/
theorem footprint_bound (p : EPSpine.Program) (f : PMSubstrate.OccupancyCost.Footprint)
    (h : f.events = registrationTotal p) : f.events ≤ 2 * Delta := by
  rw [h]; exact program_registration_bound p

/-- An indexed family, before identifying its indices with spatial lattice lines. -/
abbrev RingFamily (L : Type*) := L → EPSpine.Program

/-- Independent line ticks are reversible. This supplies no spatial coupling. -/
def familyTick (L : Type*) (either : Bool) : Equiv.Perm (L → RingReceiver.State 43) where
  toFun s l := RingReceiver.tick 43 either (s l)
  invFun s l := (RingReceiver.tick 43 either).symm (s l)
  left_inv s := by funext l; exact (RingReceiver.tick 43 either).symm_apply_apply (s l)
  right_inv s := by funext l; exact (RingReceiver.tick 43 either).apply_symm_apply (s l)

theorem family_protocol (L : Type*) (either : Bool) : Function.Bijective (familyTick L either) :=
  (familyTick L either).bijective

def FamilyPillars {L : Type*} (p : RingFamily L) : Prop := ∀ l, (p l).Pillars

def familyRegistrations {L : Type*} [Fintype L] (p : RingFamily L) : ℕ :=
  ∑ l, registrationTotal (p l)

theorem family_capacity {L : Type*} [Fintype L] (p : RingFamily L) :
    familyRegistrations p ≤ Fintype.card L * (2 * Delta) := by
  calc
    _ ≤ ∑ _l : L, 2 * Delta := Finset.sum_le_sum fun l _ => program_registration_bound (p l)
    _ = _ := by simp

theorem family_margin {L : Type*} (p : RingFamily L) (h : FamilyPillars p)
    (l : L) (b : Fin 2) (hd : differs (p l).toRing b) :
    registrations (p l).toRing b < 43 := (h l).2.1 b hd

theorem family_toll {L : Type*} (p : RingFamily L) (h : FamilyPillars p)
    (l : L) (b : Fin 2) (hd : differs (p l).toRing b) :
    1 ≤ registrations (p l).toRing b := (h l).2.2.2.2.1 b hd

theorem family_map_governor {L : Type*} (p : RingFamily L) (h : FamilyPillars p) (l : L) :
    MapRecord (p l).toRing ∧ MapClass (p l).toRing ∧ Governor (p l).toRing :=
  ⟨(h l).2.2.1, (h l).2.2.2.1, (h l).2.2.2.2.2⟩

/-- Exact equivalence of the data for a singleton family, not a lattice embedding. -/
def singletonFamilyEquiv : RingFamily Unit ≃ EPSpine.Program where
  toFun p := p ()
  invFun p := fun _ => p
  left_inv p := by funext u; cases u; rfl
  right_inv _ := rfl

theorem singleton_pillars (p : RingFamily Unit) : FamilyPillars p ↔ (p ()).Pillars := by
  constructor
  · intro h; exact h ()
  · intro h u; cases u; exact h

/-- Relevant registrations: only the bit rings differing from the reference. -/
def relevant (p : EPSpine.Program) : ℕ := ringTotal p.label p.reference p.firing p.x0

theorem relevant_margin_bound (p : EPSpine.Program) (h : p.Pillars) :
    relevant p ≤ 2 * (Delta - 1) := by
  calc
    _ ≤ ∑ _b : Fin 2, 42 := by
      unfold relevant ringTotal
      apply Finset.sum_le_sum
      intro b _
      split_ifs with hd
      · have hm := h.2.1 b hd
        change localizedSumN 43 true (p.firing b) p.x0 43 < 43 at hm
        omega
      · omega
    _ = _ := by norm_num [Delta_eq]

/-- Toll and Map force at least one relevant registration. -/
theorem relevant_floor (p : EPSpine.Program) (h : p.Pillars) : 1 ≤ relevant p := by
  apply h.2.2.1.trans
  apply ringTotal_ge_hamming
  intro b hb
  apply (ring43_toll_iff (p.firing b) p.x0).mp
  have ht := h.2.2.2.2.1 b hb
  exact lt_of_lt_of_le Nat.zero_lt_one ht

/-- Every generation and visible channel admits the same relevant minimum.
This is a pillar witness, not a held-event minimum. -/
theorem one_relevant_in_every_generation
    (g : EPSpine.Generation) (c : PMConstants.PacketGaugeActions.Channels)
    (hc : PMElementaryParticles.ProgramClasses.classOf c ≠ 4) :
    ∃ p : EPSpine.Program, p.generation = g ∧ p.label = c ∧ p.Pillars ∧ relevant p = 1 := by
  obtain ⟨r, hr, hk⟩ := EPSpine.exists_root_of_key g
  refine ⟨⟨c, g, leastRef c, fun _ => oneFiringN 43 0, r, hr, hk⟩,
    rfl, rfl, EPSpine.witnessAt_pillars c _ hc, ?_⟩
  exact (ringTotal_oneSite c (leastRef c) (fun _ => 0) _).trans (leastRef_hamming c)

/-- The proposed 42-per-line bound is valid when the record Hamming distance is one. -/
theorem relevant_one_bit_bound (p : EPSpine.Program) (h : p.Pillars)
    (hh : hamming (labelRecord p.label) (refRecord p.reference) = 1) :
    relevant p ≤ Delta - 1 := by
  have hb (b : Fin 2)
      (hd : bitOf (labelRecord p.label) b ≠ bitOf (refRecord p.reference) b) :
      localizedSumN 43 true (p.firing b) p.x0 43 ≤ 42 := by
    have hm := h.2.1 b hd
    change localizedSumN 43 true (p.firing b) p.x0 43 < 43 at hm
    omega
  have hsum : (if bitOf (labelRecord p.label) 0 ≠ bitOf (refRecord p.reference) 0 then 1 else 0) +
      (if bitOf (labelRecord p.label) 1 ≠ bitOf (refRecord p.reference) 1 then 1 else 0) = (1 : ℕ) := by
    simpa [hamming, bitOf] using hh
  unfold relevant ringTotal
  rw [Fin.sum_univ_two]
  change (if bitOf (labelRecord p.label) 0 ≠ bitOf (refRecord p.reference) 0 then _ else _) +
    (if bitOf (labelRecord p.label) 1 ≠ bitOf (refRecord p.reference) 1 then _ else _) ≤ 42
  by_cases h0 : bitOf (labelRecord p.label) 0 ≠ bitOf (refRecord p.reference) 0 <;>
    by_cases h1 : bitOf (labelRecord p.label) 1 ≠ bitOf (refRecord p.reference) 1
  · simp [h0, h1] at hsum
  · simpa only [ite_eq_left h0, ite_eq_right h1, add_zero] using hb 0 h0
  · simpa only [ite_eq_right h0, ite_eq_left h1, zero_add] using hb 1 h1
  · simp only [ite_eq_right h0, ite_eq_right h1]; omega

/-- A general packing lemma, with the ceiling expressed by natural division. -/
theorem required_lines {L : Type*} [Fintype L] (a : L → ℕ) (R cap : ℕ)
    (hcap : 0 < cap) (hb : ∀ l, a l ≤ cap) (hR : R ≤ ∑ l, a l) :
    (R + cap - 1) / cap ≤ Fintype.card L := by
  have hs : (∑ l, a l) ≤ Fintype.card L * cap := by
    calc _ ≤ ∑ _l : L, cap := Finset.sum_le_sum fun l _ => hb l
         _ = _ := by simp
  have hR' : R ≤ Fintype.card L * cap := hR.trans hs
  have ht : R + cap - 1 < (Fintype.card L + 1) * cap := by
    rw [Nat.add_mul, one_mul]; omega
  have := (Nat.div_lt_iff_lt_mul hcap).2 ht
  omega

theorem family_spreading {L : Type*} [Fintype L] (p : RingFamily L)
    (h : FamilyPillars p) (R : ℕ) (hR : R ≤ ∑ l, relevant (p l)) :
    (R + 83) / 84 ≤ Fintype.card L := by
  exact required_lines (fun l => relevant (p l)) R 84 (by decide)
    (fun l => relevant_margin_bound (p l) (h l)) hR

theorem family_one_bit_spreading {L : Type*} [Fintype L] (p : RingFamily L)
    (h : FamilyPillars p)
    (hh : ∀ l, hamming (labelRecord (p l).label) (refRecord (p l).reference) = 1)
    (R : ℕ) (hR : R ≤ ∑ l, relevant (p l)) :
    (R + 41) / 42 ≤ Fintype.card L := by
  exact required_lines (fun l => relevant (p l)) R 42 (by decide)
    (fun l => relevant_one_bit_bound (p l) (h l) (hh l)) hR

/-- No spacetime root lies on a fixed spatial line in the aligned chart. -/
theorem no_fixed_spatial_root : ∀ r ∈ ClockAlignment.spacetimeRoots,
    ¬ (ClockSymmetry.chart r 1 = 0 ∧ ClockSymmetry.chart r 2 = 0 ∧
       ClockSymmetry.chart r 3 = 0) := by decide +kernel

/-- One primitive spacetime root per tick, with no extra firing rule. -/
structure RootExecution where
  position : ℕ → ClockRing.V
  event : ℕ → {r : ClockRing.V // r ∈ ClockAlignment.spacetimeRoots}
  next : ∀ t, position (t+1) = position t + (event t).val

/-- Already one tick cannot remain on a fixed spatial clock line. -/
theorem execution_changes_space (p : RootExecution) (t : ℕ) :
    ¬ (ClockSymmetry.chart (p.position (t+1)) 1 = ClockSymmetry.chart (p.position t) 1 ∧
       ClockSymmetry.chart (p.position (t+1)) 2 = ClockSymmetry.chart (p.position t) 2 ∧
       ClockSymmetry.chart (p.position (t+1)) 3 = ClockSymmetry.chart (p.position t) 3) := by
  intro h
  have ha (z w : ClockRing.V) : ClockSymmetry.chart (z+w) =
      ClockSymmetry.chart z + ClockSymmetry.chart w := Matrix.mulVec_add _ _ _
  rw [p.next t, ha] at h
  apply no_fixed_spatial_root (p.event t).val (p.event t).property
  exact ⟨by simpa using h.1, by simpa using h.2.1, by simpa using h.2.2⟩

/-- The full allowed displacement words retain the exact upstream step set. -/
def rootReachable (ticks : ℕ) : Set ClockRing.V :=
  {z | ∃ w : List ClockRing.V, w.length = ticks ∧
    (∀ r ∈ w, r ∈ ClockAlignment.spacetimeRoots) ∧ w.sum = z}

/-- A finite enumeration of that set, suitable for small certified horizons. -/
def rootReachableFinset : ℕ → Finset ClockRing.V
  | 0 => {0}
  | t + 1 => (ClockAlignment.spacetimeRoots.toFinset ×ˢ rootReachableFinset t).image
      (fun q => q.1 + q.2)

/-- The enumerator is exactly the upstream word-reachability definition. -/
theorem mem_rootReachableFinset (t : ℕ) (z : ClockRing.V) :
    z ∈ rootReachableFinset t ↔ z ∈ rootReachable t := by
  induction t generalizing z with
  | zero => simp [rootReachableFinset, rootReachable]
  | succ t ih =>
    constructor
    · intro h
      obtain ⟨⟨r,d⟩, hrd, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hr, hd⟩ := Finset.mem_product.mp hrd
      obtain ⟨w, hw, hmem, rfl⟩ := (ih d).mp hd
      exact ⟨r :: w, by simp [hw], by simpa using And.intro (List.mem_toFinset.mp hr) hmem, by simp⟩
    · rintro ⟨w, hw, hm, rfl⟩
      cases w with
      | nil => simp at hw
      | cons r w =>
        apply Finset.mem_image.mpr
        refine ⟨(r, w.sum), Finset.mem_product.mpr ⟨?_, ?_⟩, by simp⟩
        · exact List.mem_toFinset.mpr (hm r (by simp))
        · apply (ih w.sum).mpr
          exact ⟨w, by simpa using hw, fun r hr => hm r (by simp [hr]), rfl⟩

/-- Restrict to the first supplied number of spatial chart axes.
This restricts every step, not only its endpoint. -/
def directionRoots (directions : ℕ) : List ClockRing.V :=
  ClockAlignment.spacetimeRoots.filter fun r =>
    ∀ i : Fin 3, directions ≤ i.val → ClockSymmetry.chart r ⟨i.val+1, by omega⟩ = 0

theorem direction_root_counts :
    (directionRoots 0).length = 0 ∧ (directionRoots 1).length = 4 ∧
    (directionRoots 2).length = 12 ∧ (directionRoots 3).length = 24 := by decide +kernel

/-- The first event has exactly the existing 24 possible endpoints. -/
theorem root_first_card : (rootReachableFinset 1).card = 24 := by decide +kernel

/-- The cube envelope uses the same one-dimensional slices as causal_cone_card.
This is an envelope count, not a root-path footprint. -/
def boxConeCount (directions period : ℕ) : ℕ :=
  ∑ t ∈ Finset.range period, (2*t+1)^directions

theorem box_one (period : ℕ) : boxConeCount 1 period = period^2 := by
  unfold boxConeCount
  simp only [pow_one]
  rw [← PMSubstrate.PersistencePremises.causal_cone_card period]
  apply Finset.sum_congr rfl
  intro t _
  exact (PMSubstrate.PersistencePremises.slice_card t).symm

theorem box_counts :
    boxConeCount 0 Delta = 43 ∧ boxConeCount 1 Delta = 1849 ∧
    boxConeCount 2 Delta = 105995 ∧ boxConeCount 3 Delta = 6835753 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- Integer event fields, not total costs or measured values. -/
theorem declared_event_counts :
    PMSubstrate.SpeciesFootprints.Lepton.muonFootprint.events = 215 ∧
    PMSubstrate.SpeciesFootprints.Lepton.tauFootprint.events = 3483 ∧
    PMSubstrate.SpeciesFootprints.Quark.upFootprint.events = 4 ∧
    PMSubstrate.SpeciesFootprints.Quark.downFootprint.events = 4 ∧
    PMSubstrate.SpeciesFootprints.Quark.strangeFootprint.events = 173 ∧
    PMSubstrate.SpeciesFootprints.Quark.charmFootprint.events = 2479 ∧
    PMSubstrate.SpeciesFootprints.Quark.bottomFootprint.events = 7439 ∧
    PMSubstrate.SpeciesFootprints.Quark.topFootprint.events = 337904 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change sigma * Delta = 215
    norm_num [sigma_eq, Delta_eq]
  · change chi * Delta ^ 2 - sigma * Delta = 3483
    norm_num [chi_eq, sigma_eq, Delta_eq]
  · change ⌊PMSubstrate.SpeciesFootprints.Quark.anchorPoint / PMSubstrate.SpeciesFootprints.Quark.η⌋₊ = 4
    apply Nat.floor_eq_on_Ico
    norm_num [Set.mem_Ico, PMSubstrate.SpeciesFootprints.Quark.anchorPoint,
      PMSubstrate.SpeciesFootprints.Quark.η, overhead, D_eq, RM_eq]
  · change ⌊PMSubstrate.SpeciesFootprints.Quark.anchorPoint / PMSubstrate.SpeciesFootprints.Quark.η⌋₊ = 4
    apply Nat.floor_eq_on_Ico
    norm_num [Set.mem_Ico, PMSubstrate.SpeciesFootprints.Quark.anchorPoint,
      PMSubstrate.SpeciesFootprints.Quark.η, overhead, D_eq, RM_eq]
  · change ⌊PMSubstrate.SpeciesFootprints.Quark.anchorLine / PMSubstrate.SpeciesFootprints.Quark.η⌋₊ = 173
    apply Nat.floor_eq_on_Ico
    norm_num [Set.mem_Ico, PMSubstrate.SpeciesFootprints.Quark.anchorLine,
      PMSubstrate.SpeciesFootprints.Quark.η, overhead, D_eq, Delta_eq, RM_eq]
  · change ⌊PMSubstrate.SpeciesFootprints.Quark.anchorArea /
      (PMSubstrate.SpeciesFootprints.Quark.η * PMSubstrate.SpeciesFootprints.Quark.colourDim)⌋₊ = 2479
    apply Nat.floor_eq_on_Ico
    norm_num [Set.mem_Ico, PMSubstrate.SpeciesFootprints.Quark.anchorArea,
      PMSubstrate.SpeciesFootprints.Quark.η, PMSubstrate.SpeciesFootprints.Quark.colourDim,
      overhead, D_eq, Delta_eq, sigma_eq, chi_eq, RM_eq]
  · change ⌊PMSubstrate.SpeciesFootprints.Quark.anchorArea / PMSubstrate.SpeciesFootprints.Quark.η⌋₊ = 7439
    apply Nat.floor_eq_on_Ico
    norm_num [Set.mem_Ico, PMSubstrate.SpeciesFootprints.Quark.anchorArea,
      PMSubstrate.SpeciesFootprints.Quark.η, overhead, D_eq, Delta_eq, RM_eq]
  · change ⌊PMSubstrate.SpeciesFootprints.Quark.anchorVolume + PMSubstrate.SpeciesFootprints.Quark.capLeakTerm⌋₊ = 337904
    apply Nat.floor_eq_on_Ico
    norm_num [Set.mem_Ico, PMSubstrate.SpeciesFootprints.Quark.anchorVolume,
      PMSubstrate.SpeciesFootprints.Quark.capLeakTerm, PMSubstrate.SpeciesFootprints.Quark.capLeak,
      D_eq, Delta_eq]

end PMElementaryParticles.SpacetimeProgram
