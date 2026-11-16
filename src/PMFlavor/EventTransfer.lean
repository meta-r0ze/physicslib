import PMFlavor.TransferGraph
import PMConstants.GenerationWeak
import PMConstants.CarrierActions

/-!
# The label changes of one charged-current event

A charged-current event changes the protocol (for example up into down). It acts on one wall, the
reference's (`PMAction.WallChiralCurrent`, `PMConstants.CarrierActions.weak_chiral`), so it can also
change the label state: on one wall every label change is one single-wall carrier plus one glue move,
and the changes form a directed 3-cycle (`PMAction.GenerationCurrent`). On the reference's wall
(`false`, the wall of the reference background) the change `g → g − 1` uses a carrier of class
`g + 1` (`GenerationCurrent.shift_false_then_glue`).

`J κ` is the label-change matrix of one event (rows: label after, columns: label before), with
amplitude `1` for no change and `κ c` for the change that uses a carrier of class `c`.

* `entry_of_class`: the change through class `c` takes label `c − 1` to `c + 1`, with amplitude `κ c`;
  these are the three transfers of `TransferGraph` (`ends c = (c + 1, c − 1)`).
* `reverse_zero`: one event does not make the reverse change; that is the conjugate event (`Jᴴ`).
* `weak_carrier_entry`: the change through the reference's class `0` (labels `2 → 1`) uses the weak
  carrier itself (`PMConstants.GenerationWeak.weak_carrier_is_vector`, `weak_edge_false`), and it is
  the in-cycle transfer (`TransferGraph.inCycle_iff`).
* `node_entries`: the changes through classes `1` and `2` (`0 → 2` and `1 → 0`) need a spinor carrier
  (`GenerationWeak.heavy_edges_spinor`), which only the reference node supplies (`TransferGraph`).

**The actual weak refresh.** `PMConstants.CarrierActions.weak` acts on packets `V ⊕ V`, both copies
vector-class carriers (`V = Carrier 0`): it reverses the sign of every carrier in the reference's
sector (`refresh_moves_reference`) and fixes the other sector (`refresh_fixes_other`). It moves no
spinor carrier, so the entries through classes `1` and `2` need the node. It does not supply the
in-cycle entry either: a sign flip is a trivial-class glue move and keeps the label
(`PMFlavor.RefreshLabel.refresh_keeps_label`); it exchanges doublet partners, the protocol change.
Whether an event makes the class-`0` change at all is PMFlavor REVIEW item 0. `J κ` keeps `κ 0` as a
free entry.

**Completion to a unitary transfer.** One event makes only the forward changes; the reverse entries
come from the conjugate event. `A κ = N κ − (N κ)ᴴ`, with `N κ = J κ − 1` the off-diagonal part, is
skew-Hermitian (`A_skew`), carries `κ c` forward and `−κ̄ c` in reverse (`forward_entry`,
`reverse_entry`), and `1 + A κ` is unitary up to second order: `(1 + A)ᴴ(1 + A) = 1 + AᴴA`
(`first_order_unitary`).

**What unitarity fixes at second order.** For any second-order term `B`, unitarity needs
`Bᴴ + B = A²` (`second_order_unitary`): the Hermitian part of `B` is `A²/2`, forced; the
skew-Hermitian part is free. Every completion that is a power series in `A` alone (exponential,
Cayley, polar) has `B = A²/2`; they first differ at third order (coefficient of `A³`: `1/6`, `1/4`,
`1/2`). So "exponential or Cayley" does not matter at second order. What does matter is the free
skew part, which is the order of the changes inside the event: `corner_split` shows that the
two-step product `κ̄₀ κ̄₂` is carried exactly once by the class-`1` entry (`2 ← 0`) and the conjugate
of its reverse (`0 ← 2`) together, with a split `w, 1 − w̄` that unitarity does not fix. The
exponential of `A` (all three changes at once) gives `w = ½`; the ordered product with the class-`0`
change (the refresh's own) before the class-`2` change gives `w = 0`; the reverse order gives
`w = 1`.

**Forward composition (premise FC).** One event makes only forward changes (`reverse_zero`).
Premise FC: the second-order term of one event is two successive forward changes of that event,
`N²`, with only the Hermitian depletion `½(N Nᴴ + Nᴴ N)` added; no route uses two reverse changes.
FC is a unitary completion (`forward_completion`). The two forward steps `2 → 1 → 0` land on
`0 ← 2` with `κ₂ κ₀` (`forward_two_step`), and the class-`1` entry `2 ← 0` gets nothing
(`forward_corner`): FC is `w = 0`. Any power series in `A` (exponential, Cayley) uses
reverse-reverse routes (`Nᴴ²/2` in `A²/2`), so it is not FC. FC is not derived: it reads
`reverse_zero` as a statement about all routes inside one event.

**The cycle phase.** Rephasing the label states leaves only the product of the three changes round
the cycle, `κ₀κ₁κ₂` (`cycle_invariant`); its argument `Φ` is the holonomy of the directed 3-cycle,
the only place a phase of `J` can sit. Under FC the class-`1` entry is `κ₁` and its reverse has size
`|κ₁ − conj(κ₀κ₂)|`, with `|·|² = |κ₁|² + |κ₀κ₂|² − 2|κ₀κ₁κ₂| cos Φ` (`fc_corner`). So under FC a flat
holonomy (`Φ = 0` or `π`) makes the three sizes collinear.

The amplitudes `κ c` depend on where the carriers sit relative to the reference axis (off the axis:
two legs, amplitude; on the axis: one leg, probability; `NodeElimination`): `ConductionRule` gives the
in-cycle one, `TransferAmplitude` the other-wall node one; the reference-wall node one is open. So
there are two matrices, `J` for carriers off the axis and for carriers on it. If the persisting states
are the label states, the observed matrix is `J` (normalized, with the dressing); otherwise it is
`U_uᴴ J U_d`, with `U` the persistence rotation of each protocol (PMAction's wire; protocols from
PMElementaryParticles).
-/

namespace PMFlavor.EventTransfer

/-- **The label-change matrix of one event** on the reference's wall. -/
def J {R : Type*} [One R] [Zero R] (κ : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of ![![1, κ 2, 0], ![0, 1, κ 0], ![κ 1, 0, 1]]

variable {R : Type*} [One R] [Zero R] (κ : Fin 3 → R)

/-- **The change through class `c` takes label `c − 1` to `c + 1`, amplitude `κ c`.** -/
theorem entry_of_class (c : Fin 3) : J κ (c + 1) (c - 1) = κ c := by
  fin_cases c <;> rfl

/-- **The three changes are the three transfers of `TransferGraph`.** -/
theorem entry_is_transfer (c : Fin 3) :
    J κ (TransferGraph.ends c).1 (TransferGraph.ends c).2 = κ c := entry_of_class κ c

/-- **One event makes no reverse change.** -/
theorem reverse_zero (c : Fin 3) : J κ (c - 1) (c + 1) = 0 := by
  fin_cases c <;> rfl

/-- **No change keeps amplitude `1`.** -/
theorem diag_one (g : Fin 3) : J κ g g = 1 := by
  fin_cases g <;> rfl

/-- **The weak carrier's own change:** through class `0`, labels `2 → 1`, in the cycle. -/
theorem weak_carrier_entry :
    J κ 1 2 = κ 0 ∧ (TransferGraph.InCycle 0) ∧ ((2 : Fin 3) - 1 = 1) := by
  exact ⟨rfl, (TransferGraph.inCycle_iff 0).2 rfl, by decide⟩

/-- **The node changes:** through classes `1` (`0 → 2`) and `2` (`1 → 0`), out of the cycle. -/
theorem node_entries :
    J κ 2 0 = κ 1 ∧ J κ 0 1 = κ 2 ∧ ¬ TransferGraph.InCycle 1 ∧ ¬ TransferGraph.InCycle 2 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [TransferGraph.inCycle_iff]; decide
  · rw [TransferGraph.inCycle_iff]; decide

/-! ## The actual weak refresh -/

open PMConstants.CarrierActions PMConstants.CarrierRepresentation in
/-- **The refresh fixes the other sector.** -/
theorem refresh_fixes_other (v : V) : weak (Sum.inr v) = Sum.inr v := rfl

open PMConstants.CarrierActions PMConstants.CarrierRepresentation in
/-- **The refresh moves every carrier of the reference's sector**, by its sign. -/
theorem refresh_moves_reference : ∀ v : V, weak (Sum.inl v) ≠ Sum.inl v := by
  decide +kernel

/-! ## Completion to a unitary transfer -/

open Matrix

/-- Off-diagonal part of `J`. -/
def N (κ : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ := J κ - 1

/-- Forward changes minus their conjugates. -/
def A (κ : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ := N κ - (N κ)ᴴ

/-- **`A` is skew-Hermitian.** -/
theorem A_skew (κ : Fin 3 → ℂ) : (A κ)ᴴ = -A κ := by
  unfold A
  rw [conjTranspose_sub, conjTranspose_conjTranspose]
  abel

/-- **Forward entry: `κ c`.** -/
theorem forward_entry (κ : Fin 3 → ℂ) (c : Fin 3) : A κ (c + 1) (c - 1) = κ c := by
  have h : c + 1 ≠ c - 1 := by fin_cases c <;> decide
  simp only [A, N, Matrix.sub_apply, Matrix.conjTranspose_apply, entry_of_class, reverse_zero,
    Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm, sub_zero, star_zero]

/-- **Reverse entry: `−κ̄ c`.** -/
theorem reverse_entry (κ : Fin 3 → ℂ) (c : Fin 3) : A κ (c - 1) (c + 1) = -star (κ c) := by
  have h : c + 1 ≠ c - 1 := by fin_cases c <;> decide
  simp only [A, N, Matrix.sub_apply, Matrix.conjTranspose_apply, entry_of_class, reverse_zero,
    Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm, sub_zero, zero_sub]

/-- **`1 + A` is unitary up to second order.** -/
theorem first_order_unitary (κ : Fin 3 → ℂ) :
    (1 + A κ)ᴴ * (1 + A κ) = 1 + (A κ)ᴴ * A κ := by
  rw [conjTranspose_add, conjTranspose_one, A_skew]
  noncomm_ring

/-! ## What unitarity fixes at second order -/

/-- **Unitarity order by order.** For any second-order term `B`, `(1 + A + B)ᴴ(1 + A + B)` is `1`,
plus the second-order part `Bᴴ + B − A²`, plus the third-order part `BᴴA − AB`, plus `BᴴB`. So a
unitary completion must have `Bᴴ + B = A²`: the Hermitian part of `B` is forced to `A²/2`; the
skew-Hermitian part is free. -/
theorem second_order_unitary (κ : Fin 3 → ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) :
    (1 + A κ + B)ᴴ * (1 + A κ + B) =
      1 + (Bᴴ + B - A κ * A κ) + (Bᴴ * A κ - A κ * B) + Bᴴ * B := by
  rw [conjTranspose_add, conjTranspose_add, conjTranspose_one, A_skew]
  noncomm_ring

theorem A_diag (κ : Fin 3 → ℂ) (g : Fin 3) : A κ g g = 0 := by
  simp only [A, N, Matrix.sub_apply, Matrix.conjTranspose_apply, diag_one, Matrix.one_apply_eq,
    sub_self, star_zero]

theorem A_21 (κ : Fin 3 → ℂ) : A κ 2 1 = -star (κ 0) := reverse_entry κ 0
theorem A_10 (κ : Fin 3 → ℂ) : A κ 1 0 = -star (κ 2) := reverse_entry κ 2
theorem A_20 (κ : Fin 3 → ℂ) : A κ 2 0 = κ 1 := forward_entry κ 1

/-- **The two-step amplitude is shared between a node crossing and its reverse.** Any unitary
completion `1 + A + B + …` has `B₂₀ + conj B₀₂ = κ̄₀ κ̄₂`: the two-step route `0 → 1 → 2` (both changes
reversed) and its conjugate `2 → 1 → 0` together carry the product of the other two amplitudes
exactly once. How it splits between the class-`1` entry (`2 ← 0`) and its reverse (`0 ← 2`) is the
free skew-Hermitian part: the exponential of `A` splits it `½, ½`; an ordered product of the
single-class changes puts all of it on one side. -/
theorem corner_split (κ : Fin 3 → ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ)
    (hB : Bᴴ + B = A κ * A κ) : B 2 0 + star (B 0 2) = star (κ 0) * star (κ 2) := by
  have h := congrFun (congrFun hB 2) 0
  rw [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_three,
    A_diag, A_diag, A_21, A_10] at h
  linear_combination h

/-! ## Forward composition: the second-order term of one event -/

theorem N_diag (κ : Fin 3 → ℂ) (g : Fin 3) : N κ g g = 0 := by
  simp only [N, Matrix.sub_apply, diag_one, Matrix.one_apply_eq, sub_self]

theorem N_10 (κ : Fin 3 → ℂ) : N κ 1 0 = 0 := by
  simp only [N, Matrix.sub_apply, Matrix.one_apply_ne (show (1 : Fin 3) ≠ 0 by decide), sub_zero]
  exact reverse_zero κ 2

theorem N_21 (κ : Fin 3 → ℂ) : N κ 2 1 = 0 := by
  simp only [N, Matrix.sub_apply, Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide), sub_zero]
  exact reverse_zero κ 0

theorem N_01 (κ : Fin 3 → ℂ) : N κ 0 1 = κ 2 := by
  simp only [N, Matrix.sub_apply, Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide), sub_zero]
  exact entry_of_class κ 2

theorem N_12 (κ : Fin 3 → ℂ) : N κ 1 2 = κ 0 := by
  simp only [N, Matrix.sub_apply, Matrix.one_apply_ne (show (1 : Fin 3) ≠ 2 by decide), sub_zero]
  exact entry_of_class κ 0

/-- **Forward composition is a unitary completion.** Take as second-order term two successive
forward changes of the same event, `N²`, minus a Hermitian depletion `D` with
`D + D = N Nᴴ + Nᴴ N` (so `D = ½(N Nᴴ + Nᴴ N)`). Then `Bᴴ + B = A²`: unitary at second order. -/
theorem forward_completion (κ : Fin 3 → ℂ) (D : Matrix (Fin 3) (Fin 3) ℂ) (hD : Dᴴ = D)
    (hD2 : D + D = N κ * (N κ)ᴴ + (N κ)ᴴ * N κ) :
    (N κ * N κ - D)ᴴ + (N κ * N κ - D) = A κ * A κ := by
  rw [conjTranspose_sub, conjTranspose_mul, hD]
  have e : (N κ)ᴴ * (N κ)ᴴ - D + (N κ * N κ - D) = (N κ)ᴴ * (N κ)ᴴ + N κ * N κ - (D + D) := by
    abel
  rw [e, hD2]
  unfold A
  noncomm_ring

/-- **The two forward steps `2 → 1 → 0` land on the entry `0 ← 2`**, with amplitude `κ₂ κ₀`. -/
theorem forward_two_step (κ : Fin 3 → ℂ) : (N κ * N κ) 0 2 = κ 2 * κ 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three, N_diag, N_01, N_12, zero_mul, mul_zero, zero_add,
    add_zero]

/-- **Under forward composition the class-`1` entry `2 ← 0` has no second-order term** (`w = 0` in
`corner_split`): no two forward changes go from `0` to `2`, and the depletion has no `2 ← 0` entry. -/
theorem forward_corner (κ : Fin 3 → ℂ) (D : Matrix (Fin 3) (Fin 3) ℂ)
    (hD2 : D + D = N κ * (N κ)ᴴ + (N κ)ᴴ * N κ) : (N κ * N κ - D) 2 0 = 0 := by
  have h := congrFun (congrFun hD2 2) 0
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
    N_diag, N_10, N_21, star_zero, mul_zero, zero_mul, add_zero] at h
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three, N_diag, N_10, N_21, mul_zero,
    zero_mul, add_zero]
  linear_combination (-(1 : ℂ) / 2) * h

/-! ## The cycle phase -/

/-- **The cycle product is the one rephasing invariant.** Rephasing the label states by phases `u g`
(`u g · ū g = 1`) changes the change through class `c` (label `c − 1` to `c + 1`) to
`u (c + 1) κ c ū (c − 1)`. The product of the three changes round the cycle is unchanged. -/
theorem cycle_invariant (κ u : Fin 3 → ℂ) (hu : ∀ g, u g * star (u g) = 1) :
    (u 1 * κ 0 * star (u 2)) * (u 2 * κ 1 * star (u 0)) * (u 0 * κ 2 * star (u 1)) =
      κ 0 * κ 1 * κ 2 := by
  linear_combination (κ 0 * κ 1 * κ 2 * (u 1 * star (u 1)) * (u 2 * star (u 2))) * hu 0 +
    (κ 0 * κ 1 * κ 2 * (u 2 * star (u 2))) * hu 1 + (κ 0 * κ 1 * κ 2) * hu 2

/-- **Under FC the two corners and the cycle phase form a triangle.** Under FC the entry `0 ← 2` is
`−κ̄₁ + κ₂κ₀` (`reverse_entry`, `forward_two_step`; the depletion has no `0 ← 2` entry), so its
size is `|κ₁ − conj(κ₀κ₂)|`, and the law of cosines holds with the angle `arg(κ₀κ₁κ₂)`, the cycle
phase. -/
theorem fc_corner (κ : Fin 3 → ℂ) :
    Complex.normSq (κ 1 - star (κ 0 * κ 2)) =
      Complex.normSq (κ 1) + Complex.normSq (κ 0 * κ 2) - 2 * (κ 0 * κ 1 * κ 2).re := by
  rw [Complex.star_def, Complex.normSq_sub, Complex.normSq_conj, Complex.conj_conj,
    show κ 1 * (κ 0 * κ 2) = κ 0 * κ 1 * κ 2 by ring]

end PMFlavor.EventTransfer
