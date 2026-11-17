import PMAction.GenerationMapObligations
import PersistenceMechanics.Requirements
import PMAction.Machine.CarrierResponse

/-!
# A reversible governor for the six-state carrier-pair protocol

This is the class-pair quotient, not the full carrier or clock dynamics. A
proposed class translation executes if it stays in `IsGen`; otherwise it idles.
That rejection policy and the admitted query family are specified choices.
All resulting schedules are reversible and satisfy the framework's three PM
requirements for any supplied configuration cost. A schedule is an abstract
macrostep; its identification with the substrate tick is not supplied.

The operational ledger charges changed class states plus a supplied baseline.
It is not a native-root tariff: zero-glue root words may still move carrier
coordinates invisible in this quotient. The physical event prices, clock and
noise/restoration law remain to derive.
-/
noncomputable section
namespace PMAction.GenerationPairProtocol
open GenerationSector GenerationMapObligations Matrix

section Guard
variable {A : Type*} (P : A → Prop) [DecidablePred P] (f : A → A)

def guarded (s : {a // P a}) : {a // P a} :=
  if h : P (f s.val) then ⟨f s.val,h⟩ else s

/-- Rejection is reversible because the ambient move is an involution. -/
theorem guarded_involutive (hf : Function.Involutive f) : Function.Involutive (guarded P f) := by
  intro s
  by_cases h : P (f s.val)
  · have hh := hf s.val
    simp [guarded, h, hh, s.property]
  · simp [guarded, h]

def governor (hf : Function.Involutive f) : Equiv.Perm {a // P a} where
  toFun := guarded P f
  invFun := guarded P f
  left_inv := guarded_involutive P f hf
  right_inv := guarded_involutive P f hf

/-- The specified accept-or-idle contract fixes this governor uniquely. -/
theorem guarded_unique (u : {a // P a} → {a // P a})
    (hyes : ∀ s, P (f s.val) → (u s).val = f s.val)
    (hno : ∀ s, ¬P (f s.val) → u s = s) : u = guarded P f := by
  funext s
  by_cases h : P (f s.val)
  · apply Subtype.ext
    simpa [guarded,h] using hyes s h
  · simpa [guarded,h] using hno s h
end Guard

def pairDomain (p : Glue × Glue) : Prop := IsGen p.1 p.2
instance : DecidablePred pairDomain := fun p => inferInstanceAs (Decidable (IsGen p.1 p.2))

def glueMove (a : Glue) (p : Glue × Glue) : Glue × Glue := (p.1+a,p.2+a)
def wallMove (q : Bool × Glue) (p : Glue × Glue) : Glue × Glue :=
  if q.1 then (p.1+q.2,p.2) else (p.1,p.2+q.2)

lemma glue_twice : ∀ a : Glue, Function.Involutive (glueMove a) := by
  unfold Function.Involutive
  decide +kernel
lemma wall_twice : ∀ q : Bool × Glue, Function.Involutive (wallMove q) := by
  unfold Function.Involutive
  decide +kernel

def glueStep (a : Glue) : Equiv.Perm State := governor pairDomain (glueMove a) (glue_twice a)
def wallStep (q : Bool × Glue) : Equiv.Perm State := governor pairDomain (wallMove q) (wall_twice q)

lemma wall_zero : ∀ (b : Bool) (s : State), wallStep (b,0) s = s := by
  decide +kernel

/-- Matched translations either exchange orientation or leave this pair unchanged. -/
theorem glue_step_shape : ∀ (a : Glue) (s : State),
    glueStep a s = if a = label s then swap s else s := by
  decide +kernel

theorem glue_preserves_label (a : Glue) (s : State) : labelCode (glueStep a s) = labelCode s := by
  rw [glue_step_shape]
  split_ifs
  · exact swap_same_label s
  · rfl

/-- A valid nonzero single-wall shift keeps the pair valid but changes its label. -/
theorem accepted_wall_changes_label : ∀ (q : Bool × Glue) (s : State),
    q.2 ≠ 0 → wallKeeps s q →
      label (wallStep q s) = label s + q.2 ∧ label (wallStep q s) ≠ label s := by
  unfold wallKeeps
  decide +kernel

inductive Move where
  | glue (a : Glue)
  | wall (q : Bool × Glue)
  deriving DecidableEq

def step : Move → Equiv.Perm State
  | .glue a => glueStep a
  | .wall q => wallStep q

lemma step_involutive : ∀ m : Move, Function.Involutive (step m) := by
  intro m
  cases m
  · exact guarded_involutive _ _ (glue_twice _)
  · exact guarded_involutive _ _ (wall_twice _)

/-- Lists execute from left to right. -/
def run : List Move → State → State
  | [], s => s
  | m :: ms, s => run ms (step m s)

theorem run_bijective (ms : List Move) : Function.Bijective (run ms) := by
  induction ms with
  | nil => exact Function.bijective_id
  | cons m ms ih => exact ih.comp (step m).bijective

def schedule (ms : List Move) : Equiv.Perm State := Equiv.ofBijective (run ms) (run_bijective ms)

/-- Finiteness, no merging and a reversible history, for the supplied schedule
and cost. This is not selection of a microscopic update or a noise margin. -/
def requirements (ms : List Move) (cost : State → ℝ) :
    PersistenceMechanics.Requirements.PMRequirements State where
  step := run ms
  cost := cost
  finiteness _ := Set.toFinite _
  conservation := (run_bijective ms).1
  causality := (run_bijective ms).2

/-! ## Transition geometry and the missing identity protection -/

def runWalls (qs : List (Bool × Glue)) : State → State := run (qs.map Move.wall)

/-- Short paths along the six-state wall-move graph, expressed from the initial
classes. The route count is the six-state classification, not a fitted factor. -/
def routes (s : State) : Fin 6 → List (Bool × Glue) := ![
  [], [(true,s.val.2)], [(false,s.val.1)],
  [(true,s.val.2),(false,label s)],
  [(false,s.val.1),(true,label s)],
  [(true,s.val.2),(false,label s),(true,s.val.1)]]

theorem routes_cover : ∀ s t : State, ∃ i : Fin 6, runWalls (routes s i) s = t := by
  decide +kernel

theorem routes_length : ∀ (s : State) (i : Fin 6), (routes s i).length ≤ 3 := by
  decide +kernel

/-- Orientation exchange needs three guarded wall-class moves in this move family. -/
theorem swap_three : ∀ s : State,
    runWalls [(true,s.val.2),(false,label s),(true,s.val.1)] s = swap s := by
  decide +kernel

theorem swap_not_two : ∀ (s : State) (q r : Bool × Glue),
    runWalls [q,r] s ≠ swap s := by
  decide +kernel

/-- The full minimum bound includes empty and one-move schedules. -/
theorem swap_needs_three (s : State) (qs : List (Bool × Glue))
    (h : runWalls qs s = swap s) : 3 ≤ qs.length := by
  by_contra hn
  have hl : qs.length ≤ 2 := by omega
  cases qs with
  | nil => exact swap_ne s h.symm
  | cons q qs =>
    cases qs with
    | nil =>
      apply swap_not_two s q (true,0)
      simpa [runWalls, run, step, wall_zero] using h
    | cons r qs =>
      cases qs with
      | nil => exact swap_not_two s q r h
      | cons u qs => simp at hl

/-- If every guarded wall move must leave a diagonal state label unchanged,
that label is constant. Pair validity alone protects no nontrivial such identity. -/
theorem wall_invariants_constant {R : Type*} (f : State → R)
    (h : ∀ q s, f (wallStep q s) = f s) : ∀ s t, f s = f t := by
  have hr : ∀ qs s, f (runWalls qs s) = f s := by
    intro qs
    induction qs with
    | nil => intro s; rfl
    | cons q qs ih =>
      intro s
      exact (ih (wallStep q s)).trans (h q s)
  intro s t
  obtain ⟨i,hi⟩ := routes_cover s t
  rw [← hi]
  exact (hr (routes s i) s).symm

/-! ## Operational toll, with prices supplied -/

def toll (baseline : ℝ) (w : Move → ℝ) (m : Move) (s : State) : ℝ :=
  baseline + if step m s = s then 0 else w m

def action (baseline : ℝ) (w : Move → ℝ) : List Move → State → ℝ
  | [], _ => 0
  | m :: ms, s => toll baseline w m s + action baseline w ms (step m s)

theorem action_nonneg (baseline : ℝ) (hb : 0 ≤ baseline) (w : Move → ℝ) (hw : ∀ m, 0 ≤ w m)
    (ms : List Move) (s : State) : 0 ≤ action baseline w ms s := by
  induction ms generalizing s with
  | nil => exact le_rfl
  | cons m ms ih =>
    apply add_nonneg _ (ih _)
    unfold toll
    split_ifs <;> linarith [hw m]

/-- Returning to the same state does not erase the expenditure of an active cycle. -/
theorem round_trip (baseline : ℝ) (w : Move → ℝ) (m : Move) (s : State)
    (h : step m s ≠ s) :
    run [m,m] s = s ∧ action baseline w [m,m] s = 2 * (baseline + w m) := by
  have hback : step m (step m s) ≠ step m s := by
    rw [step_involutive m s]
    exact Ne.symm h
  constructor
  · exact step_involutive m s
  · simp [action, toll, h, hback]
    ring

/-- A concrete identity-changing accepted move exists inside the validity governor. -/
theorem validity_not_label_protection :
    ∃ q : Bool × Glue, ∃ s : State, wallKeeps s q ∧ label (wallStep q s) ≠ label s := by
  unfold wallKeeps
  decide +kernel

/-- A governor cannot both execute every pair-valid wall request and preserve
this label. Identity protection needs an additional restriction or restoration. -/
theorem no_label_preserving_executor (u : (Bool × Glue) → State → State)
    (hexec : ∀ q s, wallKeeps s q → u q s = wallStep q s)
    (hkeep : ∀ q s, label (u q s) = label s) : False := by
  obtain ⟨q,s,hvalid,hchange⟩ := validity_not_label_protection
  exact hchange ((hexec q s hvalid) ▸ hkeep q s)

/-- Without a retained fault tag or redundancy, no repair on this full logical
space can undo every unknown wall fault for every logical input. -/
theorem no_record_free_repair (repair : State → State)
    (h : ∀ q s, repair (wallStep q s) = s) : False := by
  have hid : ∀ s, repair s = s := by
    intro s
    simpa only [wall_zero] using h (true,0) s
  obtain ⟨q,s,hvalid,hchange⟩ := validity_not_label_protection
  have he : wallStep q s = s := (hid _).symm.trans (h q s)
  exact hchange (congrArg label he)

/-- A supplied event log is retained without measuring the live class.
The alphabet includes idle requests; its size is not a substrate-capacity claim. -/
abbrev FaultFrame := (Bool × Glue) × State

def taggedFault : Equiv.Perm FaultFrame where
  toFun p := (p.1, wallStep p.1 p.2)
  invFun p := (p.1, wallStep p.1 p.2)
  left_inv p := Prod.ext rfl (guarded_involutive _ _ (wall_twice _) p.2)
  right_inv p := Prod.ext rfl (guarded_involutive _ _ (wall_twice _) p.2)

theorem tagged_twice (p : FaultFrame) : taggedFault (taggedFault p) = p :=
  Prod.ext rfl (guarded_involutive _ _ (wall_twice _) p.2)

theorem fault_tag_kept (p : FaultFrame) : (taggedFault p).1 = p.1 := rfl

theorem tagged_unitary : taggedFault.permMatrix ℂ ∈ unitary (Matrix FaultFrame FaultFrame ℂ) :=
  CarrierResponse.perm_unitary _

/-- A retained event tag permits coherent exact correction of this fault family.
The tag is retained, not reset; its acquisition and physical supply are inputs. -/
theorem coherent_fault_echo (Ψ : FaultFrame → ℂ) :
    taggedFault.permMatrix ℂ *ᵥ (taggedFault.permMatrix ℂ *ᵥ Ψ) = Ψ := by
  have hs : taggedFault * taggedFault = 1 := by
    apply Equiv.ext
    intro p
    exact tagged_twice p
  rw [mulVec_mulVec, ← permMatrix_mul, hs, permMatrix_one, one_mulVec]

end PMAction.GenerationPairProtocol
