import PMConstants.General.Encoding
import PMSubstrate.E8Values
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Reference capacity, without assuming a marker implementation

The closed state space is N registers over an alphabet of size a. The encoder
must preserve every combination of an independent r-valued reference and K
full-width payload registers. Those are operational hypotheses, not consequences
of the E8 lattice or of Closure alone. Counting gives an implementation-independent
bound. Update equivariance can be strictly stronger than static capacity.
-/

namespace PMConstants.General.ReferenceCapacity

abbrev Code (N K a r : ℕ) := Fin r × (Fin K → Fin a) → (Fin N → Fin a)

def Encodable (N K a r : ℕ) : Prop := ∃ code : Code N K a r, Function.Injective code

theorem frame_bound (N K a r : ℕ) (code : Code N K a r)
    (h : Function.Injective code) : r*a^K ≤ a^N := by
  simpa using Fintype.card_le_of_injective code h

/-- Static capacity is also sufficient for some finite encoding. No claim of
locality, efficiency, clock compatibility or cost optimality is made here. -/
theorem encodable_iff (N K a r : ℕ) : Encodable N K a r ↔ r*a^K ≤ a^N := by
  constructor
  · rintro ⟨code, h⟩; exact frame_bound N K a r code h
  · intro h
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (α := Fin r × (Fin K → Fin a)) (β := Fin N → Fin a) (by simpa using h)
    exact ⟨e, e.injective⟩

theorem reference_costs (N a r : ℕ) (ha : 1 ≤ a) (hr : 2 ≤ r) :
    ¬ Encodable N N a r := by
  intro h
  have hb := (encodable_iff N N a r).mp h
  have hp : 0 < a^N := pow_pos (by omega) _
  have hm := Nat.mul_le_mul_right (a^N) hr
  omega

theorem payload_bound (N K a r : ℕ) (ha : 1 ≤ a) (hr : 2 ≤ r)
    (h : Encodable N K a r) : K ≤ N-1 := by
  have hb := (encodable_iff N K a r).mp h
  have hp : 0 < a^N := pow_pos (by omega) _
  by_contra hK
  have hNK : N ≤ K := by omega
  have hpow : a^N ≤ a^K := pow_le_pow_right₀ ha hNK
  have hm := Nat.mul_le_mul_right (a^K) hr
  omega

theorem power_last (N a : ℕ) (hN : 1 ≤ N) : a^N = a^(N-1)*a := by
  calc
    a^N = a^((N-1)+1) := by congr 1; omega
    _ = _ := pow_succ _ _

/-- Exactly N-1 full-width payload registers fit iff one alphabet symbol has
enough states to carry the independent reference. This is a static theorem. -/
theorem one_slot_iff (N a r : ℕ) (hN : 1 ≤ N) (ha : 1 ≤ a) :
    Encodable N (N-1) a r ↔ r ≤ a := by
  rw [encodable_iff, power_last N a hN]
  have hp : 0 < a^(N-1) := pow_pos (by omega) _
  constructor
  · intro h; nlinarith
  · intro h; simpa [Nat.mul_comm] using Nat.mul_le_mul_right (a^(N-1)) h

def OptimalPayload (N K a r : ℕ) : Prop :=
  Encodable N K a r ∧ ∀ j, Encodable N j a r → j ≤ K

theorem optimal_payload_iff (N K a r : ℕ) (hN : 1 ≤ N)
    (hr : 2 ≤ r) (hwidth : r ≤ a) : OptimalPayload N K a r ↔ K = N-1 := by
  have ha : 1 ≤ a := by omega
  have hfull : Encodable N (N-1) a r := (one_slot_iff N a r hN ha).mpr hwidth
  constructor
  · rintro ⟨hcode, hmax⟩
    exact Nat.le_antisymm (payload_bound N K a r ha hr hcode) (hmax _ hfull)
  · rintro rfl
    exact ⟨hfull, fun j hj => payload_bound N j a r ha hr hj⟩

theorem ternary_payload_bound (K : ℕ) (h : Encodable 172 K 3 172) : K ≤ 167 := by
  have hb := (encodable_iff 172 K 3 172).mp h
  by_contra hK
  have hp : (3 : ℕ)^168 ≤ 3^K := pow_le_pow_right₀ (by decide) (by omega)
  norm_num at hb hp
  omega

theorem ternary_167_attained : Encodable 172 167 3 172 := by
  rw [encodable_iff]; norm_num

theorem binary_payload_bound (K : ℕ) (h : Encodable 172 K 2 172) : K ≤ 164 := by
  have hb := (encodable_iff 172 K 2 172).mp h
  by_contra hK
  have hp : (2 : ℕ)^165 ≤ 2^K := pow_le_pow_right₀ (by decide) (by omega)
  norm_num at hb hp
  omega

theorem binary_static_optimum : OptimalPayload 172 164 2 172 := by
  refine ⟨?_, fun j hj => binary_payload_bound j hj⟩
  rw [encodable_iff]; norm_num

theorem ternary_static_optimum : OptimalPayload 172 167 3 172 :=
  ⟨ternary_167_attained, fun j hj => ternary_payload_bound j hj⟩

theorem one_register_per_tick_static_optimum : OptimalPayload 43 42 43 43 := by
  exact (optimal_payload_iff 43 42 43 43 (by decide) (by decide) le_rfl).mpr rfl

theorem wide_static : Encodable 172 171 172 172 :=
  (one_slot_iff 172 172 172 (by decide) (by decide)).mpr le_rfl

theorem canonical_reference_no_payload_loss (N a : ℕ) : Encodable N N a 1 := by
  rw [encodable_iff]; simp

/-- Any fixed point of the stored-state update is unavailable to an injective
equivariant encoding whose input dynamics has no fixed point. -/
theorem equivariant_not_surjective {X Y : Type*} (code : X → Y)
    (input : X → X) (update : Y → Y) (hinj : Function.Injective code)
    (heq : ∀ x, update (code x) = code (input x))
    (hmove : ∀ x, input x ≠ x) (fixed : Y) (hfixed : update fixed = fixed) :
    ¬ Function.Surjective code := by
  intro hs
  obtain ⟨x, hx⟩ := hs fixed
  have h : code (input x) = code x := by
    rw [← heq x, hx]
    exact hfixed
  exact hmove x (hinj h)

theorem equivariant_iterates {X Y : Type*} (code : X → Y)
    (input : X → X) (update : Y → Y)
    (heq : ∀ x, update (code x) = code (input x)) (n : ℕ) (x : X) :
    (update^[n]) (code x) = code ((input^[n]) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, heq]

/-- Injective equivariant codes preserve exact return times, not merely one
tick. Any counting construction must supply enough orbits of the right length. -/
theorem period_reflection {X Y : Type*} (code : X → Y)
    (input : X → X) (update : Y → Y) (hinj : Function.Injective code)
    (heq : ∀ x, update (code x) = code (input x)) (n : ℕ) (x : X) :
    (update^[n]) (code x) = code x ↔ (input^[n]) x = x := by
  rw [equivariant_iterates code input update heq]
  exact ⟨fun h => hinj h, congrArg code⟩

/-- A homogeneous fixed state cannot carry a total equivariant origin readout
when the reference must advance without a fixed point. An admissible addressed
code must exclude such states, or change the readout/update requirement. -/
theorem no_total_origin_readout {States Ref : Type*}
    (update : States → States) (advance : Ref → Ref)
    (hmove : ∀ o, advance o ≠ o) (fixed : States) (hfixed : update fixed = fixed) :
    ¬ ∃ read : States → Ref, ∀ s, read (update s) = advance (read s) := by
  rintro ⟨read, h⟩
  have he := h fixed
  rw [hfixed] at he
  exact hmove (read fixed) he.symm

theorem strict_frame_bound (N K a r : ℕ) (code : Code N K a r)
    (advance : Fin r → Fin r) (update : (Fin N → Fin a) → (Fin N → Fin a))
    (hinj : Function.Injective code)
    (heq : ∀ o p, update (code (o,p)) = code (advance o,p))
    (hmove : ∀ o, advance o ≠ o) (fixed : Fin N → Fin a) (hfixed : update fixed = fixed) :
    r*a^K < a^N := by
  have hns := equivariant_not_surjective code (fun x => (advance x.1,x.2)) update hinj
    (fun x => heq x.1 x.2) (fun x h => hmove x.1 (congrArg Prod.fst h)) fixed hfixed
  simpa using Fintype.card_lt_of_injective_not_surjective code hinj hns

theorem rotate_moves {N : ℕ} (hN : 2 ≤ N) (i : Fin N) : finRotate N i ≠ i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
  intro heq
  have hv := congrArg Fin.val heq
  rw [coe_finRotate] at hv
  split_ifs at hv with hi
  · have hi' := congrArg Fin.val hi
    simp only [Fin.val_last] at hi'
    omega
  · omega

def rotateWord {N a : ℕ} (word : Fin N → Fin a) : Fin N → Fin a :=
  fun i => word ((finRotate N).symm i)

/-- For the literal N-cycle update and a nonempty alphabet, an equivariant
one-slot code needs strictly more than N alphabet symbols. Sufficiency for all
N is not asserted: it needs a proved full-orbit/necklace construction. -/
theorem rotating_one_slot_requires_wider (N a : ℕ) (hN : 2 ≤ N) (ha : 1 ≤ a)
    (code : Code N (N-1) a N) (hinj : Function.Injective code)
    (heq : ∀ o p, rotateWord (code (o,p)) = code (finRotate N o,p)) : N+1 ≤ a := by
  let z : Fin a := ⟨0, by omega⟩
  have hb := strict_frame_bound N (N-1) a N code (finRotate N) rotateWord hinj heq
    (rotate_moves hN) (fun _ => z) rfl
  rw [power_last N a (by omega)] at hb
  have hp : 0 < a^(N-1) := pow_pos (by omega) _
  by_contra h
  have haN : a ≤ N := by omega
  have hm := Nat.mul_le_mul_right (a^(N-1)) haN
  nlinarith

theorem wide_not_clock_equivariant :
    ¬ ∃ code : Code 172 171 172 172, Function.Injective code ∧
      ∀ o p, rotateWord (code (o,p)) = code (finRotate 172 o,p) := by
  rintro ⟨code, hinj, heq⟩
  have h := rotating_one_slot_requires_wider 172 172 (by decide) (by decide) code hinj heq
  omega

theorem rotating_172_payload_bound (K : ℕ) (code : Code 172 K 172 172)
    (hinj : Function.Injective code)
    (heq : ∀ o p, rotateWord (code (o,p)) = code (finRotate 172 o,p)) : K ≤ 170 := by
  have hs := payload_bound 172 K 172 172 (by decide) (by decide) ⟨code, hinj⟩
  by_contra h
  have hK : K = 171 := by omega
  subst K
  exact wide_not_clock_equivariant ⟨code, hinj, heq⟩

/-- A small attained dynamical example: the six ordered pairs of distinct
symbols in a three-symbol, two-register memory. No extra marker symbol. -/
def pairBase (p : Fin 3) : Fin 2 → Fin 3 := ![![0,1], ![0,2], ![1,2]] p

def pairCode (x : Fin 2 × Fin 3) : Fin 2 → Fin 3 :=
  if x.1 = 0 then pairBase x.2 else fun i => pairBase x.2 (finRotate 2 i)

theorem pairCode_injective : Function.Injective pairCode := by decide

theorem pairCode_equivariant :
    ∀ o p, rotateWord (pairCode (o,p)) = pairCode (finRotate 2 o,p) := by decide

/-! The actual direction/phase register interpretation has another possible
tick: advance the 43 phases while retaining the direction component. It is not
the single 172-cycle assumed by a word-necklace construction. -/
abbrev Grid := Fin 4 × Fin PMSubstrate.E8Values.Delta

def gridTick (x : Grid) : Grid := (x.1, finRotate PMSubstrate.E8Values.Delta x.2)

def gridUpdate {a : ℕ} (word : Grid → Fin a) : Grid → Fin a :=
  fun x => word (x.1, (finRotate PMSubstrate.E8Values.Delta).symm x.2)

theorem gridTick_moves (x : Grid) : gridTick x ≠ x := by
  intro h
  exact rotate_moves (by decide) x.2 (congrArg Prod.snd h)

theorem grid_one_slot_requires_wider (a : ℕ) (ha : 1 ≤ a)
    (code : Grid × (Fin 171 → Fin a) → (Grid → Fin a)) (hinj : Function.Injective code)
    (heq : ∀ o p, gridUpdate (code (o,p)) = code (gridTick o,p)) : 173 ≤ a := by
  let z : Fin a := ⟨0, by omega⟩
  have hns := equivariant_not_surjective code (fun x => (gridTick x.1,x.2)) gridUpdate
    hinj (fun x => heq x.1 x.2)
    (fun x h => gridTick_moves x.1 (congrArg Prod.fst h)) (fun _ => z) rfl
  have hc : 172*a^171 < a^172 := by
    simpa [Grid] using Fintype.card_lt_of_injective_not_surjective code hinj hns
  rw [power_last 172 a (by decide)] at hc
  change 172*a^171 < a^171*a at hc
  have hp : 0 < a^171 := pow_pos (by omega) _
  by_contra h
  have hm := Nat.mul_le_mul_right (a^171) (show a ≤ 172 by omega)
  nlinarith

theorem grid_172_payload_bound (K : ℕ)
    (code : Grid × (Fin K → Fin 172) → (Grid → Fin 172)) (hinj : Function.Injective code)
    (heq : ∀ o p, gridUpdate (code (o,p)) = code (gridTick o,p)) : K ≤ 170 := by
  have hc : 172*172^K ≤ 172^172 := by
    simpa [Grid] using Fintype.card_le_of_injective code hinj
  have hs := payload_bound 172 K 172 172 (by decide) (by decide)
    ((encodable_iff 172 K 172 172).mpr hc)
  by_contra h
  have hK : K = 171 := by omega
  subst K
  have hwidth := grid_one_slot_requires_wider 172 (by decide) code hinj heq
  omega

end PMConstants.General.ReferenceCapacity
