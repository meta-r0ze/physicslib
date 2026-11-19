import PMTransport.Machine.OpenReferenceFlow
import PMTransport.Machine.AxisHop
import PMTransport.Machine.RootReferencePreparation
import PMAction.LatticeSiteAction

/-!
# Reference supply and record export on an open handoff route

Embed the two-stream line in the D₄ address lattice along a primitive
root direction. For the supplied shift and exchange operations, every
receiver visit takes a different upstream reference and exports the
opposite incoming state. The downstream slots retain each displaced
value at an exact address. The finite population requirement follows
from the required receiver outputs. Physical execution of the shift
and preparation of its inputs remain separate premises.
-/

noncomputable section
namespace PMTransport.OpenHandoff

open PMAction Matrix

/-- A representative primitive D₄ direction. -/
def direction : AxisHop.Tri := ![1, 1, 0, 0]

theorem direction_is_root : AxisHop.IsRoot direction := by decide +kernel

def address (j : ℤ) : Fin 4 → ℤ := fun i => j * AxisHop.vec direction i

theorem address_injective : Function.Injective address := by
  intro j k h
  have h0 := congrFun h 0
  simpa [address, AxisHop.vec, AxisHop.val, direction] using h0

theorem address_is_site (j : ℤ) :
    ∃ k, address j = Matrix.mulVec LatticeSiteAction.basisZ k := by
  apply (LatticeSiteAction.d4_sites _).mpr
  refine ⟨j, ?_⟩
  simp [address, AxisHop.vec, AxisHop.val, direction, Fin.sum_univ_four]

/-- Consecutive route addresses differ by one nearest-neighbour root. -/
theorem address_step (j : ℤ) : address (j + 1) - address j = AxisHop.vec direction := by
  funext i
  change (j + 1) * _ - j * _ = _
  ring

abbrev State (V : Type*) := OpenReferenceFlow.State ℤ V

def run {V : Type*} (s : State V) (t : ℕ) : State V :=
  (OpenReferenceFlow.evolution 0 OpenReferenceFlow.line)^[t] s

private theorem run_succ {V : Type*} (s : State V) (t : ℕ) (x : ℤ) :
    run s (t + 1) x = if x = 0 then ((run s t (x + 1)).2, (run s t (x - 1)).1)
      else ((run s t (x - 1)).1, (run s t (x + 1)).2) := by
  unfold run
  rw [Function.iterate_succ_apply', OpenReferenceFlow.evolution_apply]
  rfl

private theorem live_upstream {V : Type*} (s : State V) (t : ℕ) (x : ℤ) (hx : x < 0) :
    (run s t x).1 = (s (x - (t : ℤ))).1 := by
  induction t generalizing x with
  | zero => simp [run]
  | succ t ih =>
    rw [run_succ]
    simp only [ne_of_lt hx, ite_false, ih (x - 1) (by omega)]
    congr 2
    omega

private theorem record_upstream {V : Type*} (s : State V) (t : ℕ) (x : ℤ) (hx : 0 < x) :
    (run s t x).2 = (s (x + (t : ℤ))).2 := by
  have h := OpenReferenceFlow.record_path 0 OpenReferenceFlow.line t s x (by
    intro j _
    rw [OpenReferenceFlow.line_iterate]
    omega)
  simpa only [run, OpenReferenceFlow.line_iterate] using h

/-- Visit `t+1` restores from positive address `t+1` and retains the
live state sent from negative address `-(t+1)`. -/
theorem receiver_trace {V : Type*} (s : State V) (t : ℕ) :
    run s (t + 1) 0 = ((s (t + 1 : ℤ)).2, (s (-(t + 1 : ℤ))).1) := by
  rw [run_succ]
  simp only [ite_true, zero_add, zero_sub]
  rw [record_upstream s t 1 (by norm_num), live_upstream s t (-1) (by norm_num),
    show (1 : ℤ) + t = (t : ℤ) + 1 by omega,
    show (-1 : ℤ) - t = -((t : ℤ) + 1) by omega]

/-- At horizon `N`, the most recent displaced value is at the receiver.
Earlier displaced values occupy successive record slots on the negative line. -/
theorem export_trace {V : Type*} (s : State V) {N d : ℕ} (hd : d < N) :
    (run s N (-(d : ℤ))).2 = (s ((d : ℤ) - (N : ℤ))).1 := by
  induction N generalizing d with
  | zero => omega
  | succ N ih =>
    cases d with
    | zero =>
      simpa [Nat.cast_succ] using congrArg Prod.snd (receiver_trace s N)
    | succ d =>
      have hx : -(↑(d + 1) : ℤ) ≠ 0 := by omega
      rw [run_succ]
      simp only [hx, ite_false]
      change (run s N (-(↑(d + 1) : ℤ) + 1)).2 = _
      rw [show -(↑(d + 1) : ℤ) + 1 = -(d : ℤ) by omega, ih (by omega)]
      congr 2
      omega

/-- Even with exact restoration at every visit, the open route can carry
any supplied incoming live stream. Every displaced value is also visible
at its exported address. This witness uses no source admission premise. -/
theorem any_incoming_trace {V : Type*} (reference : V) (traffic : ℕ → V) :
    ∃ s : State V,
      (∀ t : ℕ, run s (t + 1) 0 = (reference, traffic t)) ∧
      (∀ N d : ℕ, d < N → (run s N (-(d : ℤ))).2 = traffic (N - d - 1)) := by
  let s : State V := fun x => (traffic (-x - 1).toNat, reference)
  refine ⟨s, ?_, ?_⟩
  · intro t
    rw [receiver_trace]
    simp [s]
  · intro N d hd
    rw [export_trace s hd]
    simp [s]

/-- For any reference acceptance rule, all receiver visits pass exactly
when each corresponding upstream record passes. This also covers tolerances
around a chosen reference. -/
theorem acceptance_iff_supply {V : Type*} (s : State V) (accepts : V → Prop) (N : ℕ) :
    (∀ j : Fin N, accepts (run s (j.val + 1) 0).1) ↔
      (∀ j : Fin N, accepts (s (j.val + 1 : ℤ)).2) := by
  simp only [receiver_trace]

/-- Exact receiver restoration through `N` visits requires the full
incoming reference population. A budget on those inputs bounds the horizon. -/
theorem population_required {n : Type*} [Fintype n] [DecidableEq n]
    (s : State (n → ℂ)) (reference : n → ℂ) (N : ℕ)
    (restored : ∀ j : Fin N, (run s (j.val + 1) 0).1 = reference) :
    OpenReferenceFlow.incomingPopulation s N = (N : ℝ) * CommonResponse.nsq reference := by
  have h := (acceptance_iff_supply s (· = reference) N).mp restored
  simp [OpenReferenceFlow.incomingPopulation, h]

/-- The existing carrier reference has unit population. Each required visit
draws one such reference from the initial incoming train. -/
theorem basis_population_required (s : State (Fin 2 → ℂ)) (N : ℕ)
    (restored : ∀ j : Fin N, (run s (j.val + 1) 0).1 = RootReferencePreparation.reference) :
    OpenReferenceFlow.incomingPopulation s N = N := by
  rw [population_required s RootReferencePreparation.reference N restored]
  norm_num [LinkExpansion.nsq_eq, RootReferencePreparation.reference, WalkReferenceCoupling.reference,
    Fin.sum_univ_two]

/-- If each incoming record is loaded by the existing root preparation,
exact restoration is equivalent to supplying its known occupied seed
at each upstream loading site. -/
theorem basis_loading_iff {N : ℕ} (s : State (Fin 2 → ℂ))
    (seed : Fin N → ActualRootRepair.C → ℂ)
    (loaded : ∀ j : Fin N, ActualRootRepair.root.permMatrix ℂ *ᵥ seed j =
      ActualRootRepair.pack 0 (s (j.val + 1 : ℤ)).2) :
    (∀ j : Fin N, (run s (j.val + 1) 0).1 = RootReferencePreparation.reference) ↔
      ∀ j : Fin N, seed j = Pi.single RootReferencePreparation.seedLabel 1 := by
  rw [acceptance_iff_supply s (· = RootReferencePreparation.reference) N]
  constructor
  · intro ready j
    exact (RootReferencePreparation.prepares_iff _).mp (by rw [loaded j, ready j])
  · intro known j
    have h := ((RootReferencePreparation.prepares_iff _).mpr (known j))
    rw [loaded j] at h
    exact (ActualRootRepair.pack_injective _ _ _ _ h).2

/-- The local coherent exchange flag on each visit depends on the original
opposite arrivals at that visit. The flag is a probability when those
arrivals form a normalized comparison input. -/
theorem receiver_flag (s : State (Fin 2 → ℂ)) (t : ℕ) :
    CommonResponse.stateFlag (ActualRootRepair.root.permMatrix ℂ)
      (ActualRootRepair.pack (run s t (-1)).1 (run s t 1).2) =
    CommonResponse.nsq ((s (-(t + 1 : ℤ))).1 - (s (t + 1 : ℤ)).2) / 2 := by
  rw [ActualRootRepair.repair_response, live_upstream s t (-1) (by norm_num),
    record_upstream s t 1 (by norm_num), show (1 : ℤ) + t = (t : ℤ) + 1 by omega,
    show (-1 : ℤ) - t = -((t : ℤ) + 1) by omega]

/-- The exported record train preserves the sum of any observable of the
displaced inputs. In particular, take the observable to be population.
The statement assigns no registration price to the route. -/
theorem sum_exported {V A : Type*} [AddCommMonoid A] (s : State V)
    (N : ℕ) (measure : V → A) :
    (∑ d : Fin N, measure (run s N (-(d.val : ℤ))).2) =
      ∑ j : Fin N, measure (s (-(j.val + 1 : ℤ))).1 := by
  calc
    _ = ∑ j : Fin N, measure (run s N (-(j.rev.val : ℤ))).2 :=
      (Equiv.sum_comp Fin.revPerm _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have hj : (j.rev.val : ℤ) - (N : ℤ) = -(j.val + 1 : ℤ) := by
        have h := j.isLt
        simp only [Fin.val_rev]
        omega
      rw [export_trace s j.rev.isLt, hj]

/-- A conditional reset price in the existing two-port receiver. Two
equally weighted basis inputs, one carrying the bit and one a fresh zero,
have unit joint population. When this comparison registers, exchanging
a written one has flag probability one half and a written zero has zero.
An implementation must still supply and admit the bit encoding and the
fresh reference. -/
theorem balanced_basis_repair_flag (b : Fin 2) (markPhase : ℂ)
    (hphase : Complex.normSq markPhase = 1) :
    let a : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)
    let input := ActualRootRepair.pack
      (Pi.single b (if b = 0 then a else markPhase * a)) (Pi.single 0 a)
    CommonResponse.nsq input = 1 ∧
      CommonResponse.stateFlag (ActualRootRepair.root.permMatrix ℂ) input =
        if b = 0 then 0 else 1 / 2 := by
  have ha : Complex.normSq (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [Complex.normSq_ofReal, ← sq, inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  dsimp only
  rw [ActualRootRepair.population, ActualRootRepair.repair_response]
  simp only [LinkExpansion.nsq_eq, Fin.sum_univ_two]
  fin_cases b <;> norm_num [Pi.single_apply, ha, Complex.normSq_neg, Complex.normSq_mul, hphase]

end PMTransport.OpenHandoff
