import PMElementaryParticles.WireSchedule
import PMConstants.PreparationSelection
import PMConstants.ReferenceEconomy
import PMSubstrate.PersistenceMaximin

/-!
# The population cost of the two electric record references

The individual flags come from the electric reader. Aggregate costs need
a population or a set of required reads. Neither the reader nor the
survival conversion supplies that population.
-/

noncomputable section
namespace PMElementaryParticles.WireReferenceCost
open PMConstants.PacketGaugeActions ProtocolInventory Finset
open PMSubstrate.NetCost
open scoped BigOperators

/-- Uniform sampling on the full packet gives the inventory multiplicities
divided by sixteen. The absence of a base protocol is its own event. -/
theorem uniform_slot_weights :
    prob (univ.filter fun c : Channels => baseProtocol c = some .electron) = 2 / 16 ∧
    prob (univ.filter fun c : Channels => baseProtocol c = some .down) = 6 / 16 ∧
    prob (univ.filter fun c : Channels => baseProtocol c = some .up) = 6 / 16 ∧
    prob (univ.filter fun c : Channels => baseProtocol c = some .neutrino) = 1 / 16 ∧
    prob (univ.filter fun c : Channels => baseProtocol c = none) = 1 / 16 := by
  obtain ⟨hu, hd, he, hn, hv⟩ := inventory_split
  simp [prob, he, hd, hu, hn, hv]

/-- A protocol's copies on one wall. The quark copies are the `Fin 3`
colour coordinates of the two sum types. -/
def wallSlots (wall : Bool) (label : Option BaseProtocol) : Finset Channels :=
  univ.filter fun c => active c = wall ∧ baseProtocol c = label

theorem wall_inventory (wall : Bool) :
    (wallSlots wall (some .electron)).card = 1 ∧
    (wallSlots wall (some .down)).card = 3 ∧
    (wallSlots wall (some .up)).card = 3 ∧
    (wallSlots wall (some .neutrino)).card = (if wall then 1 else 0) ∧
    (wallSlots wall none).card = (if wall then 0 else 1) := by
  cases wall <;> decide +kernel

/-- The full-packet maximin premise forces the uniform slot sampling law. -/
theorem uniform_if_maximin (p : Channels → ℝ)
    (h : PMSubstrate.PersistenceMaximin.Maximin p) (c : Channels) : p c = 1 / 16 := by
  simpa [channels_card] using
    (PMSubstrate.PersistenceMaximin.maximin_iff p).mp h c

/-- An alternative uniformity proof when the writer's inputs really inherit
the invariant 32-carrier preparation by restriction and renormalization. -/
theorem uniform_if_inherited
    (P : Bool × PMSubstrate.ChannelSymmetry.V4 → ℝ)
    (hP : ∀ i, ∀ x ∈ PMSubstrate.ChannelSymmetry.channels,
      P (PMSubstrate.ChannelSymmetry.gen i x) = P x)
    (p : Channels → ℝ) (k : ℝ)
    (hp : ∀ c, p c = k * P (PMConstants.PreparationSelection.toChannel c))
    (hsum : ∑ c, p c = 1) (c : Channels) : p c = 1 / 16 := by
  rw [PMConstants.PreparationSelection.packet_preparation_uniform P hP p k hp hsum,
    PersistenceMechanics.LawSelection.uniform, channels_card]
  norm_num

/-- A packet comparison sees the supplied input populations. Diagonality
eliminates cross terms even for coherent input; it assigns no populations. -/
theorem packet_flag (t : ℝ) (φ : Channels → ℂ) :
    PMAction.CommonResponse.stateFlag (hypercharge t) φ =
      ∑ c, Complex.normSq (φ c) * ProtocolToll.hyperchargeFlag t c := by
  simp only [ProtocolToll.hyperchargeFlag, VacancyProjection.hypercharge_flag]
  exact PMAction.DiagonalReadout.state_flag charge_hermitian _
    VacancyProjection.charge_real t φ

/-- Compressing a two-wall pair to one massive state takes the mean of
the two flags. The weight of that massive state in a traffic law is separate. -/
theorem massive_pair_flag (t : ℝ) (c : Channels) :
    PMAction.CommonResponse.stateFlag (hypercharge t)
      (fun d => if d = ControlledGluedRegister.opposite c ∨ d = c
        then ((Real.sqrt 2)⁻¹ : ℂ) else 0) =
    (ProtocolToll.hyperchargeFlag t (ControlledGluedRegister.opposite c) +
      ProtocolToll.hyperchargeFlag t c) / 2 := by
  have h : ControlledGluedRegister.opposite c ≠ c := by
    intro h
    have hh := ControlledGluedRegister.opposite_active c
    rw [h] at hh
    cases hc : active c <;> simp_all
  exact EventRequirements.massive_flag t _ _ h


open ProtocolToll ControlledGluedRegister HeavyFlipControl
open PMAction.DiagonalReadout

theorem bitToll_opposite (pol : Bool) (c : Channels) :
    WireSchedule.bitToll pol (opposite c) = WireSchedule.bitToll pol c := by
  obtain ⟨hq, hs⟩ := ElectricHeavyRecord.same_wall_pair c
  simp [WireSchedule.bitToll, hq, hs]

/-- A vacancy slot has no occupied payload. If its basis slot is probed
by this particular reader, its two output flags are those of the neutral
partner. This is a statement about the operator, not about admission. -/
theorem neutral_slot_tolls :
    WireSchedule.bitToll true neutrinoStatic = 1 ∧
    WireSchedule.bitToll false neutrinoStatic = 0 ∧
    WireSchedule.bitToll true (opposite neutrinoStatic) = 1 ∧
    WireSchedule.bitToll false (opposite neutrinoStatic) = 0 := by
  obtain ⟨_, _, _, hc⟩ := HeavyFlipRecords.orbit_record_tolls 0
  obtain ⟨_, _, _, hl⟩ := ElectricHeavyRecord.lepton_reference_toll 0
  have h : WireSchedule.bitToll true neutrinoStatic = 1 := by
    simpa only [WireSchedule.bitToll, ElectricHeavyRecord.colour_reference_toll] using hc
  exact ⟨h, hl, (bitToll_opposite _ _).trans h, (bitToll_opposite _ _).trans hl⟩

theorem sector_bit (c : Channels) : (labelRecord c).1 = !colourBulk c := by
  revert c
  decide +kernel

/-- The position flag cancels for every slot. The sector flag reverses. -/
theorem bitToll_difference (c : Channels) :
    WireSchedule.bitToll true c - WireSchedule.bitToll false c =
      if colourBulk c = true then -1 else 1 := by
  rw [WireSchedule.bitToll, WireSchedule.bitToll, ElectricHeavyRecord.phase_sector,
    ElectricHeavyRecord.phase_sector_lepton_reference, sector_bit]
  cases colourBulk c <;> simp

/-- A common booked population can omit idle slots. The gap depends only
on the two sector masses among the inputs that actually run the writer. -/
theorem booked_population_difference (p : Channels → ℝ) :
    (∑ c, p c * WireSchedule.bitToll true c) -
        (∑ c, p c * WireSchedule.bitToll false c) =
      2 * (∑ c ∈ univ.filter (fun c : Channels => colourBulk c = false), p c) -
        (∑ c, p c) := by
  rw [← sum_sub_distrib]
  calc
    _ = ∑ c, (2 * (if colourBulk c = false then p c else 0) - p c) := by
      apply sum_congr rfl
      intro c _
      rw [← mul_sub, bitToll_difference]
      cases colourBulk c <;> simp [two_mul]
    _ = _ := by rw [sum_sub_distrib, ← mul_sum, sum_filter]

/-- For normalized inputs that all run the writer, its total booked mass is one. -/
theorem population_difference (p : Channels → ℝ) (hnorm : ∑ c, p c = 1) :
    (∑ c, p c * WireSchedule.bitToll true c) -
        (∑ c, p c * WireSchedule.bitToll false c) =
      2 * (∑ c ∈ univ.filter (fun c : Channels => colourBulk c = false), p c) - 1 := by
  rw [booked_population_difference, hnorm]

/-- `full` chooses the sample space. `probeVacancy` below instead decides
whether a sampled vacant slot runs either comparison. -/
def sampleSlots (full : Bool) : Finset Channels :=
  univ.filter fun c => full = true ∨ baseProtocol c ≠ none

abbrev Sample (full : Bool) := ↥(sampleSlots full)

/-- Position comparison first, sector second. The exact output flags
are the indicators of these events. -/
def recordEvents (full probeVacancy colourReference : Bool) (i : Fin 2) :
    Finset (Sample full) :=
  univ.filter fun c =>
    (probeVacancy = true ∨ baseProtocol c.val ≠ none) ∧
      (if i = 0 then (labelRecord c.val).2 = true
       else (labelRecord c.val).1 = colourReference)

theorem expectedRecordCost_eq_mean (full probeVacancy pol : Bool) :
    expectedCost 1 (recordEvents full probeVacancy pol) =
      (∑ c : Sample full, if probeVacancy = true ∨ baseProtocol c.val ≠ none
        then WireSchedule.bitToll pol c.val else 0) / Fintype.card (Sample full) := by
  unfold expectedCost
  simp only [one_mul, Fin.sum_univ_two]
  congr 1
  apply sum_congr rfl
  intro c _
  cases pol <;> by_cases h : probeVacancy = true ∨ baseProtocol c.val ≠ none <;>
    cases ha : (labelRecord c.val).1 <;> cases hb : (labelRecord c.val).2 <;>
    simp [recordEvents, h, ha, hb, WireSchedule.bitToll, ElectricHeavyRecord.phase_position,
      ElectricHeavyRecord.phase_sector, ElectricHeavyRecord.phase_sector_lepton_reference]

theorem sample_card (full : Bool) :
    Fintype.card (Sample full) = if full then 16 else 15 := by
  cases full <;> decide +kernel

theorem record_event_counts (full probeVacancy pol : Bool) :
    (recordEvents full probeVacancy pol 0).card = 8 ∧
      (recordEvents full probeVacancy pol 1).card =
        (if pol then if full && probeVacancy then 4 else 3 else 12) := by
  cases full <;> cases probeVacancy <;> cases pol <;> decide +kernel

/-- Unit registration cost, with the normalization of `NetCost.expectedCost`. -/
theorem packet_record_cost (full probeVacancy pol : Bool) :
    expectedCost 1 (recordEvents full probeVacancy pol) =
      (8 + (if pol then if full && probeVacancy then 4 else 3 else 12)) /
        (if full then 16 else 15) := by
  obtain ⟨hpos, hsec⟩ := record_event_counts full probeVacancy pol
  rw [expected_count_linear, one_mul, Fin.sum_univ_two, prob, prob, hpos, hsec, sample_card]
  cases full <;> cases probeVacancy <;> cases pol <;> norm_num

theorem packet_record_difference (full probeVacancy : Bool) :
    expectedCost 1 (recordEvents full probeVacancy true) -
      expectedCost 1 (recordEvents full probeVacancy false) =
      if full then (if probeVacancy then -(1 / 2) else -(9 / 16)) else -(3 / 5) := by
  rw [packet_record_cost, packet_record_cost]
  cases full <;> cases probeVacancy <;> norm_num


/-- For the two principal root writers, each half-unit baseline is the
two quarter flags from `ElectricHeavyRecord.pulse_flags`. Each signed kick
contributes half of its marked output bit, for either polarity. -/
def factorFlagToll (colourReference : Bool) (c : Channels) : ℝ :=
  (1 / 2 + (if (labelRecord c).2 = true then 1 / 2 else 0)) +
    (1 / 2 + (if (labelRecord c).1 = colourReference then 1 / 2 else 0))

theorem factorFlagToll_eq (pol : Bool) (c : Channels) :
    factorFlagToll pol c = 1 + WireSchedule.bitToll pol c / 2 := by
  cases pol <;>
    cases hp : (labelRecord c).2 <;> cases hs : (labelRecord c).1 <;>
    norm_num [factorFlagToll, WireSchedule.bitToll, ElectricHeavyRecord.phase_position,
      ElectricHeavyRecord.phase_sector, ElectricHeavyRecord.phase_sector_lepton_reference, hp, hs]

theorem factor_flag_difference (c : Channels) :
    factorFlagToll true c - factorFlagToll false c =
      (WireSchedule.bitToll true c - WireSchedule.bitToll false c) / 2 := by
  rw [factorFlagToll_eq, factorFlagToll_eq]
  ring

/-- If the refresh family and the writer are served by the same catalog
of maintenance jobs, an already serviced job is paid only once. The job
identity must include any distinct time, restoration or output obligation. -/
theorem added_maintenance_eq {J : Type*} [DecidableEq J]
    (price : J → ℝ) (baseline writer : Finset J) :
    (∑ j ∈ baseline ∪ writer, price j) - (∑ j ∈ baseline, price j) =
      ∑ j ∈ writer \ baseline, price j := by
  have he : baseline ∪ writer = baseline ∪ (writer \ baseline) := by
    ext j
    simp only [mem_union, mem_sdiff]
    tauto
  have hd : Disjoint baseline (writer \ baseline) := by
    rw [Finset.disjoint_left]
    intro j hj hw
    exact (mem_sdiff.mp hw).2 hj
  rw [he, sum_union hd]
  ring

theorem shared_maintenance_free {J : Type*} [DecidableEq J] (price : J → ℝ)
    (baseline writer : Finset J) (h : writer ⊆ baseline) :
    (∑ j ∈ baseline ∪ writer, price j) - (∑ j ∈ baseline, price j) = 0 := by
  rw [added_maintenance_eq, sdiff_eq_empty_iff_subset.mpr h, sum_empty]


/-- The remainder is in registrations per sampled input. These comparisons
apply to the two admitted schedules that pay the electric output flags. -/
theorem reference_threshold (full probeVacancy : Bool) (R : Bool → ℝ) :
    let C pol := expectedCost 1 (recordEvents full probeVacancy pol) + R pol
    let threshold : ℝ := if full then (if probeVacancy then 1 / 2 else 9 / 16) else 3 / 5
    (C true < C false ↔ R true - R false < threshold) ∧
    (C true = C false ↔ R true - R false = threshold) ∧
    (C false < C true ↔ threshold < R true - R false) := by
  dsimp only
  have h := packet_record_difference full probeVacancy
  refine ⟨?_, ?_, ?_⟩ <;> cases full <;> cases probeVacancy <;>
    norm_num at h ⊢ <;> constructor <;> intro hh <;> linarith

end PMElementaryParticles.WireReferenceCost
