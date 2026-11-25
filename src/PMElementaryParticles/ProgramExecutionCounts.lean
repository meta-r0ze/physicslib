import PMElementaryParticles.EPLabelGen
import PMElementaryParticles.RestoringOccupiedHistory
import PMKAutomaton.RestoringExtraction

/-!
# What the fifteen EP program entries count

An index is a generation and a visible class. A witness supplies one
actual label and root for an index. Count each indexed witness once
before imposing any distribution over programs or over root trials.
The existing one-site witness and the booked banked restoring execution
use distinct receiver itineraries.

## Scope of the witness count

`EPSpine.programs_card` counts 15 generation-by-visible-class indices.
`ProgramClasses.visible_channels_card` counts 15 visible channel labels.
Taking each label in each generation gives 45 label indices. The ring
registration theorem is parameterized by a channel. The separately billed
aggregate here runs one representative per spine index.

The least-Toll witnesses give one flag per run and zero live exits in the
two-site restoring projection. Using the same request for both root phases
returns the probe to its input. A retained successful closed marker gives
43 flags on the differing record ring. The booked banked route gives two.
-/

namespace PMElementaryParticles.ProgramExecutionCounts

open EPSpine ProgramClasses ProgramWitness RingRates RingSurvivors IsolatedExcitation
open PMAction PMKAutomaton
open scoped BigOperators

/-- The fifteen entries in the spine theorem. -/
abbrev ProgramIndex := Generation × {k : Fin 6 // k ≠ 4}

private def IsWitness (j : ProgramIndex) (p : Program) : Prop :=
  p.generation = j.1 ∧ classOf p.label = j.2.val ∧
    p.reference = leastRef p.label ∧ p.firing = (fun _ => oneFiringN 43 0) ∧ p.Pillars

private theorem witness_exists (j : ProgramIndex) : ∃ p : Program, IsWitness j p := by
  obtain ⟨c, hc⟩ := classOf_surjective j.2.val
  obtain ⟨root, hRoot, hKey⟩ := exists_root_of_key j.1
  exact ⟨⟨c, j.1, leastRef c, fun _ => oneFiringN 43 0, root, hRoot, hKey⟩,
    rfl, hc, rfl, rfl, witnessAt_pillars c (PMKAutomaton.ClockSites.site root) (by simpa only [hc] using j.2.property)⟩

/-- Choose one of the existing least-Toll witnesses at each index. -/
noncomputable def representative (j : ProgramIndex) : Program :=
  Classical.choose (witness_exists j)

private theorem representative_spec (j : ProgramIndex) : IsWitness j (representative j) :=
  Classical.choose_spec (witness_exists j)

theorem representative_qualifies (j : ProgramIndex) :
    (representative j).generation = j.1 ∧ classOf (representative j).label = j.2.val ∧
      (representative j).Pillars := by
  obtain ⟨hG, hC, _, _, hP⟩ := representative_spec j
  exact ⟨hG, hC, hP⟩

/-- Distinct generation/class indices pick genuinely distinct programs. -/
theorem representative_injective : Function.Injective representative := by
  intro i j h
  obtain ⟨hiG, hiC, _⟩ := representative_qualifies i
  obtain ⟨hjG, hjC, _⟩ := representative_qualifies j
  rw [h] at hiG hiC
  exact Prod.ext (hiG.symm.trans hjG) (Subtype.ext (hiC.symm.trans hjC))

/-- The class entries do not have a common channel multiplicity. -/
theorem channel_fibre_sizes (k : Fin 6) :
    (Finset.univ.filter (fun c : PMConstants.PacketGaugeActions.Channels => classOf c = k)).card =
      (![6, 3, 3, 2, 1, 1] : Fin 6 → ℕ) k := by
  fin_cases k <;> decide +kernel

/-- Every geometric generation address has five entries. This count
concerns route addresses before imposing an occupied species or an
admitted mass insertion. -/
theorem entries_per_address (g : Fin 3) :
    (Finset.univ.filter (fun j : ProgramIndex => EPLabelGen.genIndex j.1 = g)).card = 5 := by
  fin_cases g <;> decide +kernel

/-- The existing witness has one flag on the ring whose record differs
from its reference, in the stated two-ring Toll account. -/
theorem representative_toll (j : ProgramIndex) :
    let p := representative j
    ringTotal p.label p.reference p.firing p.x0 = 1 := by
  intro p
  obtain ⟨_, _, hRef, hFire, _⟩ := representative_spec j
  change p.reference = leastRef p.label at hRef
  change p.firing = (fun _ => oneFiringN 43 0) at hFire
  rw [hRef, hFire, ringTotal_oneSite _ _ (fun _ => 0), leastRef_hamming]

/-- One separately billed execution per index gives fifteen flags. -/
theorem counted_witness_toll :
    (∑ j : ProgramIndex, let p := representative j
      ringTotal p.label p.reference p.firing p.x0) = 15 := by
  classical
  simp only [representative_toll, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    programs_card, Nat.cast_ofNat]

/-- Normalization is available when the sampling unit really is one
execution per index. The event count is defined before that choice. -/
theorem once_per_index_fraction (event : Finset ProgramIndex) :
    PMSubstrate.NetCost.prob event = (event.card : ℝ) / 15 := by
  rw [PMSubstrate.NetCost.prob, programs_card, Nat.cast_ofNat]

/-- A single firing site cannot enable both adjacent restoring receivers. -/
theorem one_site_no_restoring_exit (either : Bool) (s : Fin Delta) :
    RestoringRingHistory.liveExit either (oneFiringN Delta s 0, oneFiringN Delta s 42) = false := by
  rw [RestoringRingHistory.live_exit, exchange_oneFiring, exchange_oneFiring]
  by_cases h : (0 : Fin Delta) = s
  · subst s
    decide +kernel
  · simp [h]

/-- Projecting the old witness requests onto the restoring entry and
exit sites gives zero live exits across all fifteen entries, on either
record-bit ring. -/
theorem counted_witness_restoring_exits (either : Bool) (b : Fin 2) :
    (∑ j : ProgramIndex, if RestoringRingHistory.liveExit either
      ((representative j).firing b 0, (representative j).firing b 42)
      then (1 : ℕ) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [(representative_spec j).2.2.2.1]
  change (if RestoringRingHistory.liveExit either
    (oneFiringN Delta 0 0, oneFiringN Delta 0 42) then (1 : ℕ) else 0) = 0
  simp only [one_site_no_restoring_exit either (0 : Fin Delta), Bool.false_eq_true, ite_false]

/-- If an old witness request is reused for both phases of the root
trial, that trial has no net changed endpoint. The witness fields are
paired requests, including at the one active site. -/
theorem witness_trial_endpoint (j : ProgramIndex) (b : Fin 2) (x : Fin Delta)
    (z : SubstrateReflection.Lattice) :
    let request := (representative j).firing b x
    (ClockedRootTrials.tick (ClockedRootTrials.tick (request, (z, 0)))).2.1 = z := by
  intro request
  have hr : request = oneFiringN Delta 0 x := by
    dsimp only [request]
    rw [(representative_spec j).2.2.2.1]
  rw [hr]
  by_cases hx : x = 0 <;>
    simp only [oneFiringN, hx, ite_true, ite_false, ClockedRootTrials.shared_request_returns]

/-- The old closed-ring Margin fails if its differing record ring is
assigned to the successful adjacent restoring seed and left to circulate.
The program's recorded start needs to be the marker site. -/
theorem retained_restoring_fails_margin (p : RingProgram) (b : Fin 2)
    (hbit : differs p b) (q : RestoringRingHistory.History)
    (hLive : RestoringRingHistory.liveExit true q = true)
    (hstart : p.x0 = 42) (hreq : p.firing b = (RestoringRingHistory.seed q).2.1)
    (vacuum : VacuumLabel 0) : ¬ Margin p := by
  intro hMargin
  have hseed : localizedEmbedN Delta 0 vacuum activePacket 42
        (mkFieldsN Delta (RestoringRingHistory.seed q).2.1) = RestoringRingHistory.seed q :=
    localized_restoring_seed 0 vacuum activePacket active_activePacket q false false
  have hsum : ((localizedSumN Delta true (RestoringRingHistory.seed q).2.1 42 Delta : ℕ) : ℝ) =
      RestoringRingHistory.receiverToll true q Delta := by
    unfold localizedSumN RestoringRingHistory.receiverToll
    simp only [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro x _
    have hflag := localizedFlagN_eq_nat Delta true
      (RestoringRingHistory.seed q).2.1 vacuum 42 k x
    rw [hseed] at hflag
    exact hflag.symm
  rw [RestoringRingHistory.successful_receiver_toll_period true q hLive] at hsum
  have hcount : localizedSumN Delta true (RestoringRingHistory.seed q).2.1 42 Delta = Delta :=
    by exact_mod_cast hsum
  have hreg : localizedSumN Delta true (RestoringRingHistory.seed q).2.1 42 Delta < Delta := by
    simpa only [registrations, hstart, hreq] using hMargin b hbit
  rw [hcount] at hreg
  exact (lt_irrefl Delta) hreg

/-- A successful banked attempt has the registration count needed by
the same numerical Margin and Toll inequalities. Its extraction is a
new itinerary, so this is a receiver-account bound. -/
theorem banked_receiver_period_margin (either : Bool) (q : RestoringRingHistory.History)
    (hLive : RestoringRingHistory.liveExit either q = true) :
    let count := RestoringRingHistory.receiverToll either q 2 +
      ∑ i ∈ Finset.range (Delta - 2), ∑ x,
        RingReceiver.receiverFlag either
          ((RingReceiver.tick Delta either)^[i] (RestoringExtraction.extract either q).1) x
    1 ≤ count ∧ count < (Delta : ℝ) := by
  intro count
  have hc : count = 2 := RestoringExtraction.extracted_prefix_receiver_toll either q hLive (Delta - 2)
  rw [hc]
  change (1 : ℝ) ≤ 2 ∧ (2 : ℝ) < 43
  norm_num

end PMElementaryParticles.ProgramExecutionCounts
