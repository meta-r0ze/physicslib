import PMKAutomaton.PhaseTimedRing
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# A native one-gate clock cycle

Within the stated marker-independent kind-1/kind-4 subclass, phase zero is
the unique invariant singleton gate. The native two-request trial already
has this one-slot guard. This module proves a Boolean electron CANDIDATE:
all 43-site single-packet states return in 86 ticks, turn twice, and have
zero lifted displacement. Arbitrary marker words and phase-offset starts
are included. This is not an electromagnetic or labelled E8 identification.

The phase action used is the descending clock symmetry action. The ENTIRE
clock-root stabilizer does not act on the phase alone; imposing its scalar
invariance instead forces constancy (ClockPhaseSymmetry.full_root_invariance_constant).
Physical admission with the retained clock-plane reference remains open.
-/
noncomputable section
namespace PMKAutomaton.ClockGatedCycle
open PMKAutomaton.AutonomousRing PMKAutomaton.PhaseTimedRing

abbrev Phase := PhaseTimedRing.Phase

def gates : Finset Phase := {0}
def rule : Table := gateTable gates

theorem gate_invariant : ClockPhaseSymmetry.Invariant gates := by decide +kernel

theorem native_trial_guard : ∀ t : Phase,
    decide (t ∈ gates) = ClockedRootTrials.fire (true,false) t := by decide +kernel

theorem rule_admissible : PhaseTimedRing.Admissible rule := gate_admissible gates

theorem rule_inverse_paired : InversePaired rule := gate_inverse_paired gates gate_invariant

abbrev Heading := Phase × Bool

def heading {n : ℕ} (s : Packet n) : Heading := (s.1,s.2.1.2)

def headingStep (h : Heading) : Heading := (finRotate 43 h.1,xor h.2 (decide (h.1 = 0)))

theorem heading_step {n : ℕ} (s : Packet n) :
    heading (packetStep rule s) = headingStep (heading s) := by
  rcases s with ⟨t,⟨⟨x,d⟩,m⟩⟩
  rw [show rule = gateTable gates from rfl,gate_packet_formula]
  simp [heading,headingStep,gates]
  rfl

theorem heading_iterate {n : ℕ} (s : Packet n) (t : ℕ) :
    heading ((packetStep rule)^[t] s) = headingStep^[t] (heading s) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',heading_step,ih,Function.iterate_succ_apply']

def headingTurns (h : Heading) (t : ℕ) : ℕ := AutonomousRing.reversals headingStep Prod.snd h t

def headingDisplacement (h : Heading) (t : ℕ) : ℤ :=
  ∑ j ∈ Finset.range t, if (headingStep^[j+1] h).2 then -1 else 1

theorem native_turns_heading {n : ℕ} (s : Packet n) (t : ℕ) :
    PhaseTimedRing.reversals rule s t = headingTurns (heading s) t := by
  unfold PhaseTimedRing.reversals headingTurns
  rw [AutonomousRing.reversals_eq_sum,AutonomousRing.reversals_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (if (heading ((packetStep rule)^[j+1] s)).2 ≠
    (heading ((packetStep rule)^[j] s)).2 then 1 else 0) = _
  rw [heading_iterate,heading_iterate]

theorem native_displacement_heading {n : ℕ} (s : Packet n) (t : ℕ) :
    PhaseTimedRing.displacement rule s t = headingDisplacement (heading s) t := by
  unfold PhaseTimedRing.displacement headingDisplacement
  apply Finset.sum_congr rfl
  intro j _
  rw [← Function.iterate_succ_apply' (packetStep rule) j s]
  change (if (heading ((packetStep rule)^[j+1] s)).2 then -1 else 1) = _
  rw [heading_iterate]

/-- A bounded native heading potential; its one-step change is the streamed velocity. -/
def positionPotential (h : Heading) : ℤ :=
  if h.2 then (if h.1 = 0 then -43 else -(h.1.val : ℤ))
  else if h.1 = 0 then 0 else (h.1.val : ℤ)-43

theorem potential_bounds : ∀ h : Heading, -43 ≤ positionPotential h ∧ positionPotential h ≤ 0 := by
  decide +kernel

theorem velocity_potential : ∀ h : Heading,
    positionPotential (headingStep h)-positionPotential h =
      (if (headingStep h).2 then -1 else 1) := by decide +kernel

theorem displacement_potential (h : Heading) (t : ℕ) :
    headingDisplacement h t = positionPotential (headingStep^[t] h)-positionPotential h := by
  induction t with
  | zero => simp [headingDisplacement]
  | succ t ih =>
    have hs : headingDisplacement h (t+1) = headingDisplacement h t +
        (if (headingStep^[t+1] h).2 then -1 else 1) := by
      simp only [headingDisplacement,Finset.sum_range_succ]
    have hv := velocity_potential (headingStep^[t] h)
    rw [hs,ih,Function.iterate_succ_apply']
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_heading_certificate : ∀ h : Heading,
    headingStep^[43] h = (h.1,!h.2) ∧ headingStep^[86] h = h ∧
      headingTurns h 43 = 1 ∧ headingTurns h 86 = 2 := by decide +kernel

theorem heading_certificate (h : Heading) :
    headingStep^[43] h = (h.1,!h.2) ∧ headingStep^[86] h = h ∧
    headingTurns h 43 = 1 ∧ headingTurns h 86 = 2 ∧ headingDisplacement h 86 = 0 := by
  have hc := finite_heading_certificate h
  refine ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,?_⟩
  rw [displacement_potential,hc.2.1]
  omega

/-- All-time localization on the unwrapped ring, not just zero winding at return. -/
theorem excursion_certificate (h : Heading) (t : ℕ) : |headingDisplacement h t| ≤ 43 := by
  rw [displacement_potential]
  have hi := potential_bounds h
  have hf := potential_bounds (headingStep^[t] h)
  rw [abs_le]
  omega

theorem localization_bound {n : ℕ} (s : Packet n) (t : ℕ) :
    |PhaseTimedRing.displacement rule s t| ≤ 43 := by
  rw [native_displacement_heading]
  exact excursion_certificate _ _

/-- Compact form used for the native finite certificate; equality to packetStep is proved. -/
def simpleStep {n : ℕ} (s : Packet n) : Packet n :=
  let d := xor s.2.1.2 (decide (s.1 = 0))
  (finRotate 43 s.1,((move s.2.1.1 d,d),fun y => if y = s.2.1.1 then !s.2.2 y else s.2.2 y))

theorem native_simple {n : ℕ} : (packetStep rule : Packet n → Packet n) = simpleStep := by
  funext s
  rcases s with ⟨t,⟨⟨x,d⟩,m⟩⟩
  rw [show rule = gateTable gates from rfl,gate_packet_formula]
  simp [simpleStep,gates]
  funext y
  by_cases hy : y = x <;> simp [hy]

def initial (d : Bool) : Packet 43 := (0,((0,d),fun _ => false))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zero_return : ∀ d, (packetStep rule)^[86] (initial d) = initial d := by
  rw [native_simple]
  decide +kernel

/-- Translations and marker XOR offsets preserve the native gate dynamics. -/
def translated {n : ℕ} [NeZero n] (a : Fin n) (s : Packet n) : Packet n :=
  (s.1,((s.2.1.1+a,s.2.1.2),fun y => s.2.2 (y-a)))

theorem step_translate {n : ℕ} [NeZero n] (a : Fin n) (s : Packet n) :
    packetStep rule (translated a s) = translated a (packetStep rule s) := by
  rcases s with ⟨t,⟨⟨x,d⟩,m⟩⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp [translated,rule,gate_packet_formula,move,finRotate_apply,finRotate_symm_apply,
        apply_ite,ite_add,add_assoc,add_comm,add_left_comm,sub_eq_add_neg]
    · funext y
      simp [translated,rule,gate_packet_formula,sub_eq_iff_eq_add]

theorem iterate_translate {n : ℕ} [NeZero n] (a : Fin n) (s : Packet n) (t : ℕ) :
    (packetStep rule)^[t] (translated a s) = translated a ((packetStep rule)^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_translate,Function.iterate_succ_apply']

theorem phase_zero_return (s : Packet 43) (hp : s.1 = 0) : (packetStep rule)^[86] s = s := by
  rcases s with ⟨t,⟨⟨x,d⟩,m⟩⟩
  change t = 0 at hp
  subst t
  have h := congrArg (markerOffset m) (congrArg (translated x) (zero_return d))
  rw [← iterate_translate] at h
  change markerOffset m ((packetStep (gateTable gates))^[86] (translated x (initial d))) = _ at h
  rw [← iterate_offset] at h
  have hz : markerOffset m (translated x (initial d)) = (0,((x,d),m)) := by
    simp [translated,markerOffset,initial]
  rw [hz] at h
  exact h

theorem native_phase_trace {n : ℕ} (s : Packet n) (t : ℕ) :
    ((packetStep rule)^[t] s).1 = (finRotate 43)^[t] s.1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    change finRotate 43 (((packetStep rule)^[t] s).1) = _
    rw [ih,Function.iterate_succ_apply']

theorem packet_injective {n : ℕ} : Function.Injective (packetStep rule : Packet n → Packet n) := by
  intro s t h
  have he : PhaseTimedRing.embed (packetStep rule s) = PhaseTimedRing.embed (packetStep rule t) := congrArg _ h
  rw [← realizes_tick rule rule_admissible,← realizes_tick rule rule_admissible] at he
  have hz := (PhaseTimedRing.tick n rule).injective he
  apply Prod.ext
  · exact congrArg (fun u : PhaseTimedRing.State n => u.1) hz
  · exact AutonomousRing.embed_injective (congrArg (fun u : PhaseTimedRing.State n => u.2) hz)

set_option maxRecDepth 100000 in
theorem phase_preimage_zero : ∀ t u : Phase, (finRotate 43)^[t.val] u = t → u = 0 := by decide +kernel

/-- Every phase offset is included, via the native reversible clock update. -/
theorem full_return (s : Packet 43) : (packetStep rule)^[86] s = s := by
  have hi : Function.Injective ((packetStep rule : Packet 43 → Packet 43)^[s.1.val]) :=
    packet_injective.iterate s.1.val
  have hs := Finite.surjective_of_injective hi
  obtain ⟨q,hq⟩ := hs s
  have hp : q.1 = 0 := phase_preimage_zero s.1 q.1
    ((native_phase_trace q s.1.val).symm.trans (congrArg Prod.fst hq))
  calc
    (packetStep rule)^[86] s = (packetStep rule)^[86] ((packetStep rule)^[s.1.val] q) := by rw [hq]
    _ = (packetStep rule)^[s.1.val] ((packetStep rule)^[86] q) := by
      rw [← Function.iterate_add_apply,← Function.iterate_add_apply,Nat.add_comm]
    _ = s := by rw [phase_zero_return q hp,hq]

theorem unit_cycle (s : Packet 43) :
    (packetStep rule)^[86] s = s ∧ PhaseTimedRing.reversals rule s 86 = 2 ∧
      PhaseTimedRing.displacement rule s 86 = 0 ∧ average (PhaseTimedRing.reversals rule s 86) 86 = 1 := by
  have hh := heading_certificate (heading s)
  refine ⟨full_return s,?_,?_,?_⟩
  · rw [native_turns_heading]; exact hh.2.2.2.1
  · rw [native_displacement_heading]; exact hh.2.2.2.2
  · rw [native_turns_heading,hh.2.2.2.1]
    norm_num [average,PMSubstrate.E8Values.Delta,PMSubstrate.E8Values.Delta_eq]

/-- Arbitrary marker perturbations, positions, directions and phase-offset starts are included. -/
theorem marker_phase_robust (s : Packet 43) (m : Fin 43 → Bool) (t : Phase) :
    average (PhaseTimedRing.reversals rule (t,(s.2.1,m)) 86) 86 = 1 := (unit_cycle _).2.2.2

end PMKAutomaton.ClockGatedCycle
