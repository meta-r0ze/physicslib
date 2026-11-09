import Mathlib.Data.Fin.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The von Neumann measurement construction

A **joint state space** (system `⊗` apparatus), a **measurement interaction**, and the **pointer
readout**, from which the Born rule follows.

* `Joint N` — the joint state, `Fin (N+1) → Fin (N+1) → ℂ` (system index, apparatus index).
* `normSq` — the joint (squared) Hilbert norm.
* `prepare ψ` — the pre-measurement product state: system amplitude `ψ`, apparatus in the pointer
  origin `0`.
* `interaction` — the von Neumann coupling: a controlled permutation of the joint labels (shift
  the pointer by `swap 0 i`, controlled on the system value `i`), hence **unitary**
  (`normSq_measure`).
* `measure` — the interaction applied to a state.
* `measure_prepare` — the post-measurement state is the **entangled/diagonal** state
  `Σ_i ψ_i |i⟩⟨i|`.
* `pointerProj j` — the pointer projection on outcome `j`.
* `born` — the pointer outcome `j` has probability `‖ψ_j‖²`: the **Born rule**, derived from the
  premeasurement and pointer orthogonality rather than postulated.

This constructs the joint space and the measurement; identifying the substrate's own readout with
this apparatus interaction is the modelling boundary.
-/

noncomputable section
namespace PMAction.Measurement

/-- Joint system `⊗` apparatus state: system index `i` (rows), apparatus index `a` (columns). -/
abbrev Joint (N : ℕ) := Fin (N+1) → Fin (N+1) → ℂ

/-- Squared Hilbert norm of a joint state. -/
def normSq {N : ℕ} (v : Joint N) : ℝ := ∑ i, ∑ a, Complex.normSq (v i a)

/-- A transposition is an involution. -/
theorem swap_swap {N : ℕ} (i a : Fin (N+1)) :
    Equiv.swap 0 i (Equiv.swap 0 i a) = a := by
  simp only [Equiv.swap_apply_def]; split_ifs <;> simp_all

/-- `normSq` of an `if … else 0`. -/
theorem normSq_ite {P : Prop} [Decidable P] (x : ℂ) :
    Complex.normSq (if P then x else 0) = if P then Complex.normSq x else 0 := by
  by_cases h : P <;> simp [h]

/-- **Prepare.** System amplitude `ψ`, apparatus in the pointer origin `0`. -/
def prepare {N : ℕ} (ψ : Fin (N+1) → ℂ) : Joint N := fun i a => if a = 0 then ψ i else 0

/-- **The von Neumann interaction.** A controlled permutation of the joint labels: shift the
pointer by `swap 0 i`, controlled on the system value `i`. -/
def interaction {N : ℕ} (p : Fin (N+1) × Fin (N+1)) : Fin (N+1) × Fin (N+1) :=
  (p.1, Equiv.swap 0 p.1 p.2)

/-- Apply the interaction to a joint state (pullback along the label permutation). -/
def measure {N : ℕ} (v : Joint N) : Joint N := fun i a => v i (Equiv.swap 0 i a)

/-- The interaction is an involution on labels. -/
theorem interaction_involutive {N : ℕ} (p : Fin (N+1) × Fin (N+1)) :
    interaction (interaction p) = p := by
  obtain ⟨i, a⟩ := p
  simp only [interaction, Prod.mk.injEq, true_and]
  exact swap_swap i a

/-- **Unitarity.** The interaction preserves the joint norm. -/
theorem normSq_measure {N : ℕ} (v : Joint N) : normSq (measure v) = normSq v := by
  unfold normSq measure
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp (Equiv.swap 0 i) (fun a => Complex.normSq (v i a))

/-- **Post-measurement state.** The prepared system becomes the entangled diagonal state
`Σ_i ψ_i |i⟩⟨i|`. -/
theorem measure_prepare {N : ℕ} (ψ : Fin (N+1) → ℂ) (i a : Fin (N+1)) :
    measure (prepare ψ) i a = if a = i then ψ i else 0 := by
  unfold measure prepare
  by_cases ha : a = i
  · subst ha; simp [Equiv.swap_apply_right]
  · have h : Equiv.swap 0 i a ≠ 0 := by
      intro h0
      have hc := congrArg (Equiv.swap 0 i) h0
      rw [swap_swap, Equiv.swap_apply_left] at hc
      exact ha hc
    rw [ite_eq_right h, ite_eq_right ha]

/-- Pointer projection on outcome `j`. -/
def pointerProj {N : ℕ} (j : Fin (N+1)) (v : Joint N) : Joint N :=
  fun i a => if a = j then v i a else 0

/-- **Born rule.** After the von Neumann interaction, the pointer outcome `j` has probability
`‖ψ_j‖²`. Derived: the post-measurement state is diagonal, so projecting on `j` leaves exactly the
`j`-th system amplitude. -/
theorem born {N : ℕ} (ψ : Fin (N+1) → ℂ) (j : Fin (N+1)) :
    normSq (pointerProj j (measure (prepare ψ))) = Complex.normSq (ψ j) := by
  have h1 : ∀ i, (∑ a, Complex.normSq (pointerProj j (measure (prepare ψ)) i a)) =
      Complex.normSq (measure (prepare ψ) i j) := by
    intro i
    simp only [pointerProj, normSq_ite]
    rw [Finset.sum_eq_single j]
    · simp
    · intro a _ ha; rw [ite_eq_right ha]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have h2 : ∀ i, Complex.normSq (measure (prepare ψ) i j) =
      if j = i then Complex.normSq (ψ i) else 0 := by
    intro i
    rw [measure_prepare, normSq_ite]
  unfold normSq
  simp_rw [h1, h2]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; rw [ite_eq_right hij.symm]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- **The outcomes partition the state.** The pointer probabilities sum to the state norm
`∑_j ‖ψ_j‖²`; for a normalized system they sum to `1`. So the construction loses no probability. -/
theorem born_total {N : ℕ} (ψ : Fin (N+1) → ℂ) :
    (∑ j, normSq (pointerProj j (measure (prepare ψ)))) = ∑ j, Complex.normSq (ψ j) := by
  simp_rw [born]

/-- **Preferred basis.** The interaction resolves the system basis `{|i⟩}` (the pointer basis): a
system basis state premeasures to the correlated joint state `|i⟩|i⟩`. So the pointer coupling's
eigenbasis — the basis the measurement reports in — is *selected* by the interaction, not put in by
hand. -/
theorem basis_premeasure {N : ℕ} (i : Fin (N+1)) (j a : Fin (N+1)) :
    measure (prepare (Pi.single i 1)) j a = if j = i ∧ a = i then 1 else 0 := by
  rw [measure_prepare]
  by_cases hj : j = i
  · rw [hj, Pi.single_eq_same]
    by_cases ha : a = i <;> simp [ha]
  · simp [hj]

end PMAction.Measurement
