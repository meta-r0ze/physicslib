import PMKAutomaton.Components
import PMSubstrate.Pillars

/-!
# What the existing joint-successor interface constrains

The one-way projection is a restriction: the background trajectory cannot
respond to which packet was supplied. It does NOT say that the packet is
inactive, that gross consumption vanishes, or that no positive consumption
can be restored during a period. A net resource loss and a gross consumed
amount are different quantities.

`packet_independent_background` proves the actual structural restriction.
`net_debit_independent` makes its resource consequence explicit, conditional
on a background reserve and an EXTRA, identified net-debit equation.
`zero_baseline_forces_zero_net_debit` then excludes a packet-dependent net
debit when the algebraic zero-bank baseline has none. These hypotheses are visible;
there is no assertion that the tree already supplies that account.

The scalar Capacity mechanism in PMSubstrate.Pillars permits positive matched
consumption and intake with an unchanged reserve. `positive_matched_flows`
certifies this arithmetic fact using that mechanism. It is not a derivation of
an intake source. Further, the existing FIFO supplies a conservative one-way
packet cycle: a populated slot moves and returns in 43 ticks while the
background is fixed. This is an algebraic example, not an admitted isolated
excitation or a physical consumption/restoration account. It does not select
a successor from the proposed constraint set.

## Stop before defining the proposed set A

| Requested clause | Existing definition | Missing connection |
| --- | --- | --- |
| Reversible | Equiv.Perm and Components.joint_bijective_iff. | No gap for this clause alone. |
| One local root event per joint tick | RecordTransport.tick_local, RingReceiver's specific stencil, ClockedRootTrials' specific pulses. | No primitive-event/locality predicate for arbitrary Background x PacketBank permutations, nor an admitted root-event implementation of such a successor. This is the FIRST missing clause of A. |
| Joint charges and labels | Carrier/channel charges and the specific occupation/norm conservation theorems. | No identified total charge/label readout on this generic Background x PacketBank state, tied to its physical vacuum/packet encoding. |
| Closure covariance | ClockSymmetry.Gplus acts on the E8 lattice. | No specified Gplus action on this joint background/register state. Closure states weight invariance, not successor equivariance. Gplus also need not fix the 43-state reading using cv. |
| No-packet vacuum restriction | PacketBank has an algebraic zero; OddReferenceSource certifies rest modes. | No physical no-packet embedding and no joint-state encoding of the stationary mode family. An algebraic zero is not by itself that identification. |
| Background clamped | A supplied family packet b of bank permutations exists. | No intervention/clamping definition or selected packet operation. Requiring both factor projections globally would simply reimpose the old one-way form. |

The new phrase "every packet consumption is restored within the period" has
no existing execution-level consumption, readiness, or restoration counter on
this joint state. BoundaryErasure counts supplied resets of exported bits; it
does not define that account. PM conservation is injectivity in Requirements;
an additive resource-conservation equation would also need an identified
observable. Thus the requested zero-GROSS-consumption/back-reaction theorem
cannot be inferred from the supplied clauses as they stand.

A is not defined using placeholder predicates or assumed actions. Its
emptiness, cardinality, a faithful finite reduction, selection and the loaded
seed derivation are not established. PacketBank remains complex-valued and
infinite even with finitely many cells. A finite basis is not by itself a
finite space of arbitrary successor permutations. In particular a finite example below is
not a faithfulness theorem for the occupied 43-ring. No symmetry, packet rule,
restoring source, or mass reading is chosen.
-/

noncomputable section
namespace PMKAutomaton.JointSuccessorConstraints
open PMKAutomaton.Components
open PMAction

/-- The background endpoint is independent of the entire initial packet bank. -/
theorem packet_independent_background {B : Type*} {R : ℕ} (core : B → B)
    (packet : B → Equiv.Perm (PacketBank R)) (b : B) (p q : PacketBank R) (T : ℕ) :
    ((jointTick core packet)^[T] (b,p)).1 = ((jointTick core packet)^[T] (b,q)).1 := by
  rw [joint_core_iterate, joint_core_iterate]

/-- An identified NET loss in a background-only reserve cannot depend on the
packet input for the one-way successor. No gross consumption is inferred. -/
theorem net_debit_independent {B : Type*} {R : ℕ} (core : B → B)
    (packet : B → Equiv.Perm (PacketBank R)) (reserve : B → ℝ)
    (b : B) (T : ℕ) (debit : PacketBank R → ℝ)
    (hnet : ∀ p, reserve (((jointTick core packet)^[T] (b,p)).1) = reserve b - debit p) :
    ∀ p q, debit p = debit q := by
  intro p q
  have h := congrArg reserve (packet_independent_background core packet b p q T)
  rw [hnet p, hnet q] at h
  linarith

theorem zero_baseline_forces_zero_net_debit {B : Type*} {R : ℕ} (core : B → B)
    (packet : B → Equiv.Perm (PacketBank R)) (reserve : B → ℝ)
    (b : B) (T : ℕ) (debit : PacketBank R → ℝ)
    (hnet : ∀ p, reserve (((jointTick core packet)^[T] (b,p)).1) = reserve b - debit p)
    (hzero : debit 0 = 0) : ∀ p, debit p = 0 := by
  intro p
  exact (net_debit_independent core packet reserve b T debit hnet p 0).trans hzero

/-- Positive consumed and restored amounts can leave every reserve unchanged.
The intake source and its relation to a physical joint state are not supplied. -/
theorem positive_matched_flows :
    ∃ (reserve intake : ℕ → ℝ) (consumed : ℝ),
      0 < consumed ∧ reserve 0 = 1 ∧
      (∀ t, reserve (t+1) = reserve t - consumed + intake t) ∧
      (∀ t, consumed ≤ intake t) ∧ (∀ t, 0 ≤ reserve t) ∧
      reserve 43 = reserve 0 := by
  refine ⟨fun _ => 1, fun _ => 1, 1, by norm_num, rfl, ?_, ?_, ?_, rfl⟩
  · intro t; norm_num
  · intro t; exact le_rfl
  · exact PMSubstrate.Pillars.capacity_sustains (r := fun _ => 1)
      (i := fun _ => 1) (d := 1) (by norm_num)
      (fun _ => le_rfl) (fun _ => by norm_num)

/-- An arbitrary reversible core already has reversible one-way lifts. -/
theorem one_way_reversible {B : Type*} {R : ℕ} (core : Equiv.Perm B)
    (packet : B → Equiv.Perm (PacketBank R)) : Function.Bijective (jointTick core packet) :=
  (joint_bijective_iff _ _).2 core.bijective

/-- A finite cell/channel index does not make coherent packet states finite. -/
theorem packetBank_infinite (R : ℕ) : Infinite (PacketBank R) := by
  apply Infinite.of_injective (fun z : ℂ => (fun _ => z : PacketBank R))
  intro z w h
  exact congrFun h (0, Sum.inr (Sum.inr (Sum.inl 0)))

/-- The existing FIFO preserves the bank's total squared amplitude. -/
theorem fifo_population_conserved (R : ℕ) (p : PacketBank R) :
    CommonResponse.nsq (fifoEquiv R p) = CommonResponse.nsq p := by
  rw [fifoEquiv_eq_tick]
  exact RecordTransport.tick_norm R p

private theorem fifo_iterate_apply (R T : ℕ) (p : PacketBank R)
    (slot : Fin (R+1) × PMConstants.PacketGaugeActions.Channels) :
    ((fifoEquiv R)^[T] p) slot = p ((RecordTransport.shift R)^[T] slot) := by
  induction T generalizing slot with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply']
    change ((fifoEquiv R)^[T] p) (RecordTransport.shift R slot) = _
    rw [ih, Function.iterate_succ_apply]

set_option maxRecDepth 100000 in
private theorem slot43_return :
    ∀ slot : Fin 43 × PMConstants.PacketGaugeActions.Channels,
      (RecordTransport.shift 42)^[43] slot = slot := by decide +kernel

/-- Full bank return on the 43-cell FIFO; this gives no root-event admission. -/
theorem fifo43_return (p : PacketBank 42) : (fifoEquiv 42)^[43] p = p := by
  funext slot
  rw [fifo_iterate_apply, slot43_return]

/-- An occupied slot changes at the first FIFO tick, despite full-period return. -/
theorem fifo43_nontrivial (label : PMConstants.PacketGaugeActions.Channels) :
    fifoEquiv 42 (Pi.single (0,label) 1) ≠ (Pi.single (0,label) 1 : PacketBank 42) := by
  intro h
  have hs := congrFun h (0,label)
  norm_num [fifoEquiv, RecordTransport.shift, Equiv.prodCongr_apply,
    finRotate_apply, Pi.single_apply] at hs

/-- A stationary background can coexist with the conservative nontrivial bank
cycle. No consumption or restoration counter is identified with this cycle. -/
theorem one_way43_return {B : Type*} (b : B) (p : PacketBank 42) :
    (jointTick id (fun _ : B => fifoEquiv 42))^[43] (b,p) = (b,p) := by
  have h : ∀ T : ℕ,
      (jointTick id (fun _ : B => fifoEquiv 42))^[T] (b,p) = (b,(fifoEquiv 42)^[T] p) := by
    intro T
    induction T with
    | zero => rfl
    | succ T ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl
  rw [h, fifo43_return]

end PMKAutomaton.JointSuccessorConstraints
