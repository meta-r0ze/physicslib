import PMKAutomaton.AutonomousCensus
import PMKAutomaton.ClockPhaseSymmetry

/-!
# Phase-controlled native stream/marker dynamics

The clock is part of the state and advances exactly as RingReceiver.tick.
A table specifies a local site permutation at each phase; this is one
homogeneous autonomous update, not an externally supplied firing trace.
The general table space is very large. The marker-independent gates below
are a stated subclass: kind 1 between gate phases, kind 4 at a gate.
Every tick flips the marker at the packet, and routing depends only on
native phase. No distance to a chosen record code is used.

Time reversal must reverse a tick, not commute with clock advance. In the
incoming-port chart it includes the native collision chart conversion.
Bare phase negation plus stream exchange alone is not that reversal.
The inverse-paired local table condition below gives the chart-corrected
reversing involution; invariant phase gates satisfy that condition.
-/
noncomputable section
namespace PMKAutomaton.PhaseTimedRing
open PMKAutomaton.AutonomousRing
abbrev Phase := Fin 43
abbrev Table := Phase → Rule
abbrev State (n : ℕ) := Phase × AutonomousRing.State n
abbrev Packet (n : ℕ) := Phase × OnePacket n

def Admissible (r : Table) : Prop := ∀ t, AutonomousRing.Admissible (r t)

def tick (n : ℕ) (r : Table) : Equiv.Perm (State n) :=
  (Equiv.prodCongrRight fun t => AutonomousRing.tick n (r t)).trans
    (Equiv.prodCongr (finRotate 43) (Equiv.refl _))

def packetStep {n : ℕ} (r : Table) (s : Packet n) : Packet n :=
  (finRotate 43 s.1,AutonomousRing.packetStep (r s.1) s.2)

def embed {n : ℕ} (s : Packet n) : State n := (s.1,AutonomousRing.embed s.2)

theorem realizes_tick {n : ℕ} (r : Table) (h : Admissible r) (s : Packet n) :
    tick n r (embed s) = embed (packetStep r s) := by
  apply Prod.ext
  · rfl
  · exact packetStep_realizes_tick _ (h s.1) s.2

def reversals {n : ℕ} (r : Table) (s : Packet n) (t : ℕ) : ℕ :=
  AutonomousRing.reversals (packetStep r) (fun s => s.2.1.2) s t

def displacement {n : ℕ} (r : Table) (s : Packet n) (t : ℕ) : ℤ :=
  ∑ j ∈ Finset.range t, if (packetStep r ((packetStep r)^[j] s)).2.1.2 then -1 else 1

/-- Reverse local scattering when the clock reading is negated. -/
def InversePaired (r : Table) : Prop := ∀ t z, r (-t) (r t z) = z

def swapStreams {n : ℕ} (s : AutonomousRing.State n) : AutonomousRing.State n :=
  fun x => exchangeStreams (s x)

theorem swapStreams_involutive {n : ℕ} : Function.Involutive (swapStreams (n := n)) := by
  intro s; funext x; rfl

theorem swap_scatter {n : ℕ} (f : Rule) (h : AutonomousRing.Admissible f) (s : AutonomousRing.State n) :
    swapStreams (scatter n f s) = scatter n f (swapStreams s) := by
  funext x
  exact (h.2.2.1 (s x)).symm

theorem swap_stream {n : ℕ} (s : AutonomousRing.State n) :
    swapStreams (stream n s) = (stream n).symm (swapStreams s) := rfl

/-- Chart-corrected time reversal; the phase action is exactly t -> -t. -/
def timeReverse {n : ℕ} (r : Table) (s : State n) : State n :=
  (-s.1,scatter n (r s.1) (swapStreams s.2))

theorem reverse_involutive {n : ℕ} (r : Table) (ha : Admissible r) (hr : InversePaired r) :
    Function.Involutive (timeReverse (n := n) r) := by
  rintro ⟨t,s⟩
  apply Prod.ext
  · simp [timeReverse]
  · change scatter n (r (-t)) (swapStreams (scatter n (r t) (swapStreams s))) = s
    rw [swap_scatter _ (ha t),swapStreams_involutive]
    funext x
    exact hr t (s x)

/-- Exact reversing identity for the native shift/scatter clock update. -/
theorem reverse_tick {n : ℕ} (r : Table) (ha : Admissible r) (hr : InversePaired r) (s : State n) :
    tick n r (timeReverse r (tick n r s)) = timeReverse r s := by
  rcases s with ⟨t,s⟩
  have hp : finRotate 43 (-(finRotate 43 t)) = -t := by
    simp [finRotate_apply,neg_add_rev,add_comm]
  apply Prod.ext
  · exact hp
  · change stream n (scatter n (r (-(finRotate 43 t)))
      (scatter n (r (finRotate 43 t)) (swapStreams (stream n (scatter n (r t) s))))) =
      scatter n (r t) (swapStreams s)
    have hc (u : AutonomousRing.State n) :
        scatter n (r (-(finRotate 43 t))) (scatter n (r (finRotate 43 t)) u) = u := by
      funext x; exact hr (finRotate 43 t) (u x)
    rw [hc,swap_stream,Equiv.apply_symm_apply,swap_scatter _ (ha t)]

/-- A literal commuting action would already contradict the native phase advance. -/
theorem negation_does_not_commute_with_advance :
    -(finRotate 43 (0 : Phase)) ≠ finRotate 43 (-(0 : Phase)) := by decide +kernel

/-- Explicit marker-independent phase-gate subclass, not the general table space. -/
def gateTable (s : Finset Phase) (t : Phase) : Rule := explicitRule (if t ∈ s then 4 else 1) false

theorem gate_admissible (s : Finset Phase) : Admissible (gateTable s) := by
  intro t; exact explicit_admissible _ _

theorem gate_involutions : ∀ (k : Fin 5), (k = 1 ∨ k = 4) →
    ∀ z, explicitRule k false (explicitRule k false z) = z := by decide +kernel

theorem gate_inverse_paired (s : Finset Phase) (h : ClockPhaseSymmetry.Invariant s) :
    InversePaired (gateTable s) := by
  intro t z
  have hm : -t ∈ s ↔ t ∈ s := (h t).symm
  by_cases ht : t ∈ s
  · simp only [gateTable,ht,hm.mpr ht,ite_true]
    exact gate_involutions 4 (Or.inr rfl) z
  · have hn : -t ∉ s := fun hn => ht (hm.mp hn)
    simp only [gateTable,ht,hn,ite_false]
    exact gate_involutions 1 (Or.inl rfl) z

/-- At every site only the native phase determines the turn, never the marker value. -/
theorem gate_single_output (s : Finset Phase) (t : Phase) (d m : Bool) :
    gateTable s t (single d m) = single (xor d (decide (t ∈ s))) (!m) := by
  by_cases ht : t ∈ s <;> cases d <;> cases m <;>
    simp [gateTable,ht,explicitRule,ruleFunction,single]

/-- Closed form derived from the native site permutation, not a new dynamics assumption. -/
theorem gate_packet_formula {n : ℕ} (g : Finset Phase) (t : Phase) (x : Fin n) (d : Bool)
    (m : Fin n → Bool) :
    packetStep (gateTable g) (t,((x,d),m)) =
      (finRotate 43 t,((move x (xor d (decide (t ∈ g))),xor d (decide (t ∈ g))),
        fun y => if y = x then !m x else m y)) := by
  unfold packetStep AutonomousRing.packetStep
  rw [gate_single_output]
  rfl

def markerOffset {n : ℕ} (v : Fin n → Bool) (s : Packet n) : Packet n :=
  (s.1,(s.2.1,fun x => xor (s.2.2 x) (v x)))

theorem step_offset {n : ℕ} (g : Finset Phase) (v : Fin n → Bool) (s : Packet n) :
    packetStep (gateTable g) (markerOffset v s) = markerOffset v (packetStep (gateTable g) s) := by
  rcases s with ⟨t,⟨⟨x,d⟩,m⟩⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp only [markerOffset,gate_packet_formula]
    · funext y
      by_cases hy : y = x <;> cases hm : m x <;> cases hv : v x <;>
        simp [markerOffset,gate_packet_formula,hy,hm,hv]

theorem iterate_offset {n : ℕ} (g : Finset Phase) (v : Fin n → Bool) (s : Packet n) (t : ℕ) :
    (packetStep (gateTable g))^[t] (markerOffset v s) =
      markerOffset v ((packetStep (gateTable g))^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_offset,Function.iterate_succ_apply']

end PMKAutomaton.PhaseTimedRing
