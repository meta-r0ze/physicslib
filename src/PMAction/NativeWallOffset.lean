import PMAction.NativeDetuning

/-!
# The retained scalar term of a wall-local lazy event

For the supplied lazy generator the scalar term is fixed. On one wall it is
a multiple of that wall's projector. It can be a global energy shift only
when its coefficient vanishes, and it commutes with the coupled wall
Hamiltonian only when that coefficient or the crossing link vanishes.
The microscopic choice of event remains an input.
-/
noncomputable section
namespace PMAction.NativeWallOffset
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

def projector : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks (1 : Matrix n n ℂ) 0 0 0

def lazyEvent (e : Equiv.Perm n) (p : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks (RootTransferPhase.generator e p) 0 0 0

def flipPart (e : Equiv.Perm n) (p : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks (-((RootTransferPhase.gap p / 2 : ℝ) : ℂ) • e.permMatrix ℂ) 0 0 0

omit [Fintype n] in
/-- The existing lazy event determines the wall-local offset exactly. -/
theorem generator_split (e : Equiv.Perm n) (p : ℝ) :
    lazyEvent e p = flipPart e p +
      ((RootTransferPhase.gap p / 2 : ℝ) : ℂ) • (projector : Matrix (n ⊕ n) _ ℂ) := by
  rw [lazyEvent, NativeDetuning.generator_split]
  ext i j
  cases i <;> cases j <;> simp [flipPart, projector, sub_eq_add_neg, add_comm]

omit [Fintype n] in
/-- On two nonempty walls a one-wall offset is a global scalar exactly when
both scalars vanish. This is a statement about the generator. -/
theorem global_shift_iff [Nonempty n] (c z : ℂ) :
    c • (projector : Matrix (n ⊕ n) _ ℂ) = z • 1 ↔ c = 0 ∧ z = 0 := by
  classical
  let i : n := Classical.arbitrary n
  constructor
  · intro h
    have hr := congrFun (congrFun h (.inr i)) (.inr i)
    have hl := congrFun (congrFun h (.inl i)) (.inl i)
    simp [projector] at hr hl
    exact ⟨by simpa [hr.symm] using hl, hr.symm⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- A scalar on one wall is dynamically coupled to every nonzero crossing.
The diagonal wall operators are arbitrary. -/
theorem offset_commutes_iff (A B Y : Matrix n n ℂ) (c : ℂ) :
    Commute (c • (projector : Matrix (n ⊕ n) _ ℂ)) (fromBlocks A Y Yᴴ B) ↔
      c = 0 ∨ Y = 0 := by
  constructor
  · intro h
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      ext i j
      have he := congrFun (congrFun h.eq (.inl i)) (.inr j)
      simp [projector, fromBlocks_multiply] at he
      exact he.resolve_left hc
  · rintro (rfl | rfl)
    · simp [Commute]
    · change _ * _ = _ * _
      simp [projector, fromBlocks_multiply]

omit [Fintype n] in
/-- Relative wall offsets cannot be discarded before inserting the crossing. -/
theorem coupled_generators_differ [Nonempty n] (e : Equiv.Perm n) (p : ℝ)
    (hp : p < 1/2) (hne : p ≠ 0) (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (z : ℂ) :
    H + lazyEvent e p ≠ H + flipPart e p + z • 1 := by
  intro h
  rw [generator_split] at h
  have hoff : ((RootTransferPhase.gap p / 2 : ℝ) : ℂ) •
      (projector : Matrix (n ⊕ n) _ ℂ) = z • 1 := by
    have ha : H + (flipPart e p + z • 1) = H + flipPart e p + z • 1 :=
      (add_assoc _ _ _).symm
    rw [← ha] at h
    exact add_left_cancel (add_left_cancel h)
  have hz := (global_shift_iff _ _).mp hoff
  have hr : RootTransferPhase.gap p / 2 = 0 := by exact_mod_cast hz.1
  have hg : RootTransferPhase.gap p = 0 := by linarith
  exact hne ((NativeDetuning.gap_zero_iff p hp).mp hg)

end PMAction.NativeWallOffset
