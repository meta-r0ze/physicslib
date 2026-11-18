import PMElementaryParticles.ControlledGluedRegister

/-!
# Exact primitive activity of the unconditioned six-root heavy crossing

Use the supplied reflection word on the static wall and the reverse word on
the active wall. Keep the absolute reflection coefficient at every step,
including an antipodal jump of twice the root length. Pairing antipodal
amplitude carriers proves a sign tie even for nonuniform same-pair weights.
-/

namespace PMElementaryParticles.HeavyCrossingCost

open ControlledGluedRegister GluedRegister
open scoped BigOperators

abbrev Point := Wt × Wt
abbrev Instruction := Fin 3 × Fin 8 × Fin 8

/-- Both components of every instruction are in the same glue class. -/
def rootPair (r : Instruction) : Point :=
  (carrier r.1 r.2.1, carrier r.1 r.2.2)

def word (active : Bool) : List Instruction :=
  if active then crossingWord.reverse else crossingWord

def input (active : Bool) (amplitude label : Fin 8) : Point :=
  let x := wallClass 0 active
  place active (frame x amplitude) (frame x label)

def coefficient (r w : Point) : ℤ := (dot w.1 r.1 + dot w.2 r.2) / 4

def stepLedger : List Instruction → Point → List ℕ
  | [], _ => []
  | r :: rs, w =>
    (coefficient (rootPair r) w).natAbs :: stepLedger rs (reflectPair (rootPair r) w)

def ledger (active : Bool) (amplitude label : Fin 8) : List ℕ :=
  stepLedger (word active) (input active amplitude label)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
/-- Both words implement the same-generation endpoint exchange. -/
theorem endpoint : ∀ (b : Bool) (a l : Fin 8),
    (word b).foldl (fun w r => reflectPair (rootPair r) w) (input b a l) =
      input (!b) a l := by decide +kernel

/-- Flip the sign in the transported vector frame. -/
def mate (i : Fin 8) : Fin 8 := if i.val % 2 = 0 then i + 1 else i - 1

theorem mate_twice : ∀ i, mate (mate i) = i := by decide +kernel

def matePerm : Equiv.Perm (Fin 8) :=
  ⟨mate, mate, mate_twice, mate_twice⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
theorem ledger_antipodes : ∀ (b : Bool) (a l : Fin 8),
    ledger b (mate a) (mate l) = ledger b a l := by decide +kernel

/-- Any valuation of successive absolute steps on either wall ties opposite
protocol positions when the amplitude weights pair antipodes. -/
theorem sign_tie (b : Bool) (l : Fin 8) (mass : Fin 8 → ℝ)
    (paired : ∀ a, mass (mate a) = mass a) (price : List ℕ → ℝ) :
    (∑ a : Fin 8, mass a * price (ledger b a (mate l))) =
      ∑ a : Fin 8, mass a * price (ledger b a l) := by
  calc
    _ = ∑ a : Fin 8, mass (mate a) * price (ledger b (mate a) (mate l)) :=
      (Equiv.sum_comp matePerm (fun a => mass a * price (ledger b a (mate l)))).symm
    _ = _ := Finset.sum_congr rfl fun a _ => by rw [paired, ledger_antipodes]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
/-- Of the 48 steps per signed label, 27 are idle, 20 move by one root,
and one moves by twice a root, on either wall. -/
theorem activity_histogram : ∀ (b : Bool) (l : Fin 8),
    (∑ a : Fin 8, (ledger b a l).count 0) = 27 ∧
      (∑ a : Fin 8, (ledger b a l).count 1) = 20 ∧
      (∑ a : Fin 8, (ledger b a l).count 2) = 1 := by
  decide +kernel

/-- Uniform amplitude sampling with a separate tariff for each observed
nonzero jump. Both tariffs yield a common label cost on either wall. -/
theorem uniform_cost (b : Bool) (l : Fin 8) (unitJump doubleJump : ℝ) :
    (∑ a : Fin 8, (((ledger b a l).count 1 : ℝ) * unitJump +
      ((ledger b a l).count 2 : ℝ) * doubleJump)) / 8 =
      (20 * unitJump + doubleJump) / 8 := by
  obtain ⟨-, h1, h2⟩ := activity_histogram b l
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have h1' : (∑ a : Fin 8, ((ledger b a l).count 1 : ℝ)) = 20 := by exact_mod_cast h1
  have h2' : (∑ a : Fin 8, ((ledger b a l).count 2 : ℝ)) = 1 := by exact_mod_cast h2
  rw [h1', h2', one_mul]

end PMElementaryParticles.HeavyCrossingCost
