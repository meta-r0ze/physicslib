import PMElementaryParticles.RetainedMap
import PMElementaryParticles.GluedExcursions

/-!
# Audit of generation readout and vacuum contact

The requested forced-contact implication is not a consequence of StrongMap.
A zero-key increment preserves generation; it does not erase a pre-existing
record. The native tick retains its request field. `codedProgram` puts the
three generation codes in that field initially, and `reader` recovers them
at every positive period end. One shared reader meets StrongMap for this
family. Its exchange pattern and one-reversal total are unchanged.
This is a countermodel permitted by the present predicates, not a derived
physical preparation or an admitted joint E8/ring execution. Its initial
encoding is deliberately explicit. No new physical encoding rule is selected.
A requirement to acquire fresh generation information in each period is absent.

The generic no-reader result is equality-of-observations implies equality of
references. It cannot be strengthened from equal observations to zero-key
words alone: different initially encoded observations can remain different.
The carrier's own glue key is also still directly readable after a zero-key word.

Nonzero step key does not imply a visit to zero. For a starting key k and a
step key h different from k, k -> k+h -> k avoids zero. GluedExcursions uses
the particular choice h=k; its 512 raw pairs therefore go through zero by
construction. Their label-restoration and clock histograms are algebraic.
No action of such a pair on a native stream direction is supplied. A native
one-tick ring reversal is compatible with a single zero-key clock-root
position increment. This is positional compatibility, not a new admitted
root-to-register operator. Root-sum decompositions do not factor an executed
one-event word into two executed events.

A two-root word has length two. Its net clock reading in ZMod 43 is not its
elapsed tick count. The existing raw histograms are reused without calling
them reversal counts. No filter of reversing pairs is invented.

Admission stop: the lattice vector after the first hop is in ClockRing.V.
A vacuumMode is a normalized complex vector on VacuumLabel; occupiedInput is
a Boolean IndependentRegisters configuration. A zero glue key is not an
identification with either native object. The one missing definition is an
operational admission/representation relation for this lattice intermediate
in the certified vacuum tensor packet/ring state, including the native state
on which the next root acts. A free choice of a vacuum label would not fill it.
GluedExcursions.no_typed_intermediate already excludes its representation by
EPSpine.Program. No contact-reversal minimization is attempted after this stop.

The requested literal "Higgs move" is absent from current PMAction source.
CarrierFlip proves a Wilson matrix chirality split; CarrierActions acts on
finite signed carriers. NativeCarrierProtocol also has root-mediated port
routing, and RootCliffordCompletion constructs coherent internal rotations.
None of these identifies the additive GluedExcursions pair with this Boolean
step or identifies its lattice intermediate with a stationary vacuum mode.
-/

noncomputable section
namespace PMElementaryParticles.GenerationReadoutContact
open PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment PMKAutomaton.ClockSites
open PMElementaryParticles.EPSpine PMElementaryParticles.EPLabelGen
open PMElementaryParticles.RetainedMap PMElementaryParticles.ReversalEvents
open PMElementaryParticles.IsolatedExcitation PMElementaryParticles.RingRates
open PMElementaryParticles.ProgramWitness PMElementaryParticles.HeavyFlipControl
open PMConstants.PacketGaugeActions
open PMKAutomaton

/-- A zero-key word keeps information in the key; it does not make the key unreadable. -/
theorem zero_key_word_preserves (z : V) (w : List V)
    (h : ∀ r ∈ w, glueKey r = 0) : glueKey (z+w.sum) = glueKey z := by
  induction w generalizing z with
  | nil => simp
  | cons r w ih =>
    rw [List.sum_cons, ← add_assoc]
    exact (ih (z+r) (fun s hs => h s (by simp [hs]))).trans
      (FootprintNoGo.zero_key_preserves z r (h r (by simp)))

/-- The valid generalization is about observation collisions, not about step keys. -/
theorem readable_equal_observations (read : RingObservation → RetainedReference)
    (p q : Program) (hp : ReadableReference read p) (hq : ReadableReference read q)
    (n : ℕ) (he : observe p ((n+1)*43) = observe q ((n+1)*43)) : reference p = reference q := by
  exact (hp n).symm.trans ((congrArg read he).trans (hq n))

theorem no_reader_equal_initial_states (p q : Program) (hne : p.generation ≠ q.generation)
    (hinit : ∀ b, initialRing p b = initialRing q b) :
    ¬ ∃ read : RingObservation → RetainedReference,
      ReadableReference read p ∧ ReadableReference read q := by
  rintro ⟨read, hp, hq⟩
  have ho : observe p 43 = observe q 43 := by
    funext b
    exact congrArg ((RingReceiver.tick 43 true)^[43]) (hinit b)
  have he := readable_equal_observations read p q hp hq 0 ho
  exact hne (congrArg Prod.fst he)

/-- Three distinct nonempty requests with the same OR exchange decision. -/
def code (g : Generation) : IsolatedRequests :=
  (![ (true,false), (false,true), (true,true)] : Fin 3 → IsolatedRequests) (genIndex g)

def decode (q : IsolatedRequests) : Generation :=
  if q = (true,false) then GluedExcursions.generationAt 0
  else if q = (false,true) then GluedExcursions.generationAt 1
  else GluedExcursions.generationAt 2

theorem decode_code : ∀ g : Generation, decode (code g) = g := by decide +kernel

def exampleChannel : Channels := .inr (.inr (.inr 1))

/-- The generation is preloaded in a retained request, not acquired during the period. -/
def codedFiring (g : Generation) : Fin 2 → Fin 43 → IsolatedRequests := fun b x =>
  if b = 1 ∧ x = 0 then code g else (false,false)

theorem coded_exchange : ∀ (g : Generation) (b : Fin 2) (x : Fin 43),
    RingReceiver.exchange true (codedFiring g b x) =
      RingReceiver.exchange true (quietEqualRing exampleChannel b x) := by decide +kernel

private theorem portStep_of_exchange {n : ℕ} (r s : Fin n → IsolatedRequests)
    (h : ∀ x, RingReceiver.exchange true (r x) = RingReceiver.exchange true (s x)) :
    RingReceiver.portStep true r = RingReceiver.portStep true s := by
  apply Equiv.ext
  intro P
  funext x
  rw [portStep_apply, portStep_apply, h x]

private theorem sum_of_exchange {n : ℕ} (r s : Fin n → IsolatedRequests)
    (h : ∀ x, RingReceiver.exchange true (r x) = RingReceiver.exchange true (s x))
    (x0 : Fin n) (T : ℕ) : localizedSumN n true r x0 T = localizedSumN n true s x0 T := by
  have hp := portStep_of_exchange r s h
  simp only [localizedSumN, localizedFlagNatN, hp, h]

theorem coded_count (g : Generation) (b : Fin 2) (x0 : Fin 43) :
    localizedSumN 43 true (codedFiring g b) x0 43 =
      if bitOf (labelRecord exampleChannel) b ≠ bitOf (refRecord (leastRef exampleChannel)) b
      then 1 else 0 := by
  rw [sum_of_exchange _ _ (coded_exchange g b)]
  exact quiet_count exampleChannel x0 b

theorem coded_sum (g : Generation) (x0 : Fin 43) :
    localizedSumN 43 true (codedFiring g 0) x0 43 +
      localizedSumN 43 true (codedFiring g 1) x0 43 = 1 := by
  rw [sum_of_exchange _ _ (coded_exchange g 0), sum_of_exchange _ _ (coded_exchange g 1)]
  exact quiet_total exampleChannel x0

def codedProgram (g : Generation) : Program :=
  ⟨exampleChannel, g, leastRef exampleChannel, codedFiring g, rootAtOne g,
    (rootAtOne_spec g).1, (rootAtOne_spec g).2.1⟩

theorem coded_pillars (g : Generation) : (codedProgram g).Pillars := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (coded_sum g _).le.trans (by decide)
  · intro b hd
    change bitOf (labelRecord exampleChannel) b ≠ bitOf (refRecord (leastRef exampleChannel)) b at hd
    change localizedSumN 43 true (codedFiring g b) _ 43 < 43
    rw [coded_count, ite_eq_left hd]
    decide
  · exact (leastRef_hamming exampleChannel).symm.le
  · change ProgramClasses.classOf exampleChannel ≠ 4
    decide +kernel
  · intro b hd
    change bitOf (labelRecord exampleChannel) b ≠ bitOf (refRecord (leastRef exampleChannel)) b at hd
    change 1 ≤ localizedSumN 43 true (codedFiring g b) _ 43
    rw [coded_count, ite_eq_left hd]
  · refine ⟨0, 1, ?_⟩
    change RingReceiver.exchange true (codedFiring g 0 1) = false
    simp [codedFiring, RingReceiver.exchange]

theorem coded_total_one (g : Generation) : total (codedProgram g) = 1 := by
  rw [total_eq_registrations]
  exact coded_sum g _

/-- This same native field is present at every tick, not only the period ends. -/
theorem code_retained (g : Generation) (t : ℕ) :
    ((observe (codedProgram g) t 1).2.1 0) = code g := by
  change (((RingReceiver.tick 43 true)^[t] (initialRing (codedProgram g) 1)).2.1) 0 = code g
  rw [RingReceiver.requests_iterate]
  rfl

def reader (s : RingObservation) : RetainedReference :=
  reference (codedProgram (decode ((s 1).2.1 0)))

theorem coded_readable (g : Generation) : ReadableReference reader (codedProgram g) := by
  intro n
  unfold reader
  rw [code_retained, decode_code]

theorem coded_strong (g : Generation) : StrongMap reader (codedProgram g) :=
  ⟨coded_pillars g, coded_readable g⟩

/-- This countermodel has minimum one under the same reader; no physical encoding is inferred. -/
theorem coded_minimum (g : Generation) :
    total (codedProgram g) = 1 ∧
      ∀ q : Program, StrongMap reader q → total (codedProgram g) ≤ total q := by
  refine ⟨coded_total_one g, ?_⟩
  intro q hq
  rw [coded_total_one]
  exact strong_floor reader q hq

/-- A single shared reader works for all generations of this preloaded family. -/
theorem preloaded_strong_family :
    ∃ read : RingObservation → RetainedReference, ∃ family : Generation → Program,
      ∀ g, (family g).generation = g ∧ StrongMap read (family g) ∧ total (family g) = 1 :=
  ⟨reader, codedProgram, fun g => ⟨rfl, coded_strong g, coded_total_one g⟩⟩

/-- Neither current predicate links period-end decoding to a new nonzero-key action. -/
theorem readable_with_zero_key_word (g : Generation) (w : List V)
    (h : ∀ r ∈ w, glueKey r = 0) :
    StrongMap reader (codedProgram g) ∧
      glueKey (genPacket (codedProgram g)+w.sum) = g.val :=
  ⟨coded_strong g, (zero_key_word_preserves _ w h).trans (genPacket_key _)⟩

/-- The same readout countermodel coexists with every ring-root word and its conserved label.
The current predicates do not supply an admitted joint interpretation of those two traces. -/
theorem readable_with_ring_word (g : Generation) (w : List V)
    (h : ∀ r ∈ w, r ∈ clockAxisRoots) :
    StrongMap reader (codedProgram g) ∧
      glueKey (genPacket (codedProgram g)+w.sum) = g.val ∧
      EPLabel.internalContent (genPacket (codedProgram g)+w.sum) =
        EPLabel.internalContent (genPacket (codedProgram g)) :=
  ⟨coded_strong g, program_identity_conserved (codedProgram g) w h⟩

/-- Another nonzero key gives a returning route that does not visit zero. -/
theorem other_key_avoids_zero : ∀ k h : GluedExcursions.Key,
    k ≠ 0 → h ≠ 0 → h ≠ k →
      k+h ≠ 0 ∧ k+h ≠ k ∧ (k+h)+h = k := by decide +kernel

theorem roots_closed_under_negation : ∀ r ∈ rootList, -r ∈ rootList := by decide +kernel

theorem negative_key (r : V) : glueKey (-r) = glueKey r := by
  have h := glueKey_add r (-r)
  rw [add_neg_cancel, show glueKey (0 : V) = 0 by decide +kernel] at h
  apply add_left_cancel (a := glueKey r)
  rw [← h, GluedExcursions.key_double_zero]

/-- A concrete first hop removes the coset root but leaves the placed label vector.
It is a lattice identity, not an identification with a native stationary vacuum. -/
theorem cancelling_first_hop (p : Program) :
    -p.packet ∈ rootList ∧ glueKey (-p.packet) = p.generation.val ∧
      genPacket p+(-p.packet) = channelE8Gen (genIndex p.generation) p.label := by
  refine ⟨roots_closed_under_negation p.packet p.packet_root, ?_, ?_⟩
  · rw [negative_key, p.packet_key]
  · unfold genPacket
    abel

/-- A root and its negative restore the label without passing through zero when h differs from k.
This is a lattice-word statement; no intermediate admission is asserted. -/
theorem returning_pair_avoids_zero (p : Program) (g : Generation) (hg : g.val ≠ p.generation.val) :
    ∃ r ∈ rootList, -r ∈ rootList ∧ glueKey r = g.val ∧
      glueKey (genPacket p+r) ≠ 0 ∧ genPacket p+r+(-r) = genPacket p := by
  obtain ⟨r, hr, hk⟩ := exists_root_of_key g
  refine ⟨r, hr, roots_closed_under_negation r hr, hk, ?_, by abel⟩
  rw [glueKey_add, genPacket_key, hk]
  exact (other_key_avoids_zero _ _ p.generation.property g.property hg).1

/-- One native forward-to-backward turn has a compatible single zero-key position increment. -/
theorem zero_key_turn_at_site (z : V) (hz : site z = 42) :
    ∃ f ∈ clockAxisRoots, glueKey f = 0 ∧ clockReading f = 1 ∧
      glueKey (z+f) = glueKey z ∧ site (z+f) = 0 ∧
      (ReversalEvents.step true (oneFiringN 43 0) (site z, false)).2 = true := by
  obtain ⟨f, hf, h1⟩ := exists_forward
  refine ⟨f, hf, clockAxis_key hf, h1, step_keeps_generation z f hf, ?_, ?_⟩
  · rw [site_add_forward f z h1, hz]
    decide +kernel
  · rw [hz]
    decide +kernel

/-- Word length is not the signed modular reading of its sum. -/
theorem pair_word_length (r s : V) : ([r,s] : List V).length = 2 := rfl

theorem one_event_is_not_two (f r s : V) : ([f] : List V) ≠ [r,s] := by
  intro h
  have hn := congrArg List.length h
  simp at hn

/-- Same-starting-key algebraic excursions still have no typed EP intermediate. -/
theorem zero_key_not_a_program (z : V) (hz : glueKey z = 0) :
    ¬ ∃ p : Program, genPacket p = z := by
  rintro ⟨p, hp⟩
  have hk := genPacket_key p
  rw [hp, hz] at hk
  exact p.generation.property hk.symm

/-- The native admission criterion is exactly one supplied label in each bank.
It does not mention a lattice vector or certify a selected coherent vacuum mode. -/
theorem native_admission_iff (c : Fin 3) (q : OccupiedConfig c) :
    IsolatedExcitation.Admitted q ↔
      ∃ v : VacuumLabel c, ∃ l : PacketLabel, q = occupiedInput c v l := by
  constructor
  · intro h
    obtain ⟨⟨v,l⟩, he⟩ := (PMAction.IndependentRegisters.valid_iff q).mp h
    exact ⟨v, l, he.symm⟩
  · rintro ⟨v,l,rfl⟩
    exact occupiedInput_admitted c v l

end PMElementaryParticles.GenerationReadoutContact
