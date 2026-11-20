import PMKAutomaton.Machine.RootTransferPhase
import PMKAutomaton.Machine.CarrierWeyl

/-!
# The on-site detuning as a native event rate

Natively the on-site mass operator `β` is a carrier relabelling: `CarrierVacuumSector.beta c` is the
permutation matrix of `CarrierWeyl.lookup c 0`, an involution. `RootTransferPhase`: a lazy transfer
`(1 − p) + p e` by an involution `e`, with attempt probability `p` per tick, is reconstructed by the
Hermitian generator `gap p · (1 − P_e)/2`, `gap p = −2 log(1 − 2p)` (`heat_matches`).

* `generator_split`: that generator is `(gap p/2) · 1 − (gap p/2) · P_e`. With `e` the native `β`, it is
  a constant plus an on-site term `δ β` with `δ = −gap p/2` (per the generator's time unit, two ticks).
* `gap_zero_iff`: `δ = 0` exactly when `p = 0`.

**Reading for the wire.** The on-site detuning of a wall is the rate of that wall's `β` event (a
chirality flip). The reference's stationarity (`δ_R = 0`, `ReferenceDetuning`) is: no `β` event on
the reference's wall. The other wall's `δ_O` is `−gap(p₁)/2` with `p₁` its `β` attempt probability,
which the library does not fix. If the carriers are lazy transfers too, ratios are ratios of gaps,
`δ_O/k_f = gap(p₁)/gap(p_s) ≈ p₁/p_s` for small attempt probabilities.

**The `β` event and the reference node.** `beta_swaps_axes`: the native `β` (root word
`[1, 0, 2, 1]`, coordinate swaps only) exchanges carrier axes `0` and `2` (and `1` and `3`). On the
wire the axes are the Dirac components (`CarrierVacuumSector`), and protocol identity is a separate
register (`ColourRegister`), so this swap does not change a protocol's type and is not a node
passage: the flip is a wall term, realized by the coherent event (`PersistenceSelections` (2)), and
its size is fixed by the resonance (`OtherWallStationary`), not by a leg count. `beta_crossings`,
`lepton_always_crosses` and `colour_crosses_iff` remain as statements about which vector-class
carriers the coordinate swap moves on or off axis `0`; the earlier readings of them as per-protocol
crossing fractions put protocols on the axes and are withdrawn.
-/

namespace PMAction.NativeDetuning
open Matrix PMAction.RootTransferPhase InvolutionSpectral

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- **The lazy-transfer generator is a constant plus `−(gap p/2) P_e`.** -/
theorem generator_split (e : Equiv.Perm n) (p : ℝ) :
    generator e p = ((gap p / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) -
      ((gap p / 2 : ℝ) : ℂ) • e.permMatrix ℂ := by
  rw [generator, minus, smul_smul, ← smul_sub]
  congr 1
  push_cast
  ring

/-- **No attempt, no detuning.** -/
theorem gap_zero_iff (p : ℝ) (hp : p < 1/2) : gap p = 0 ↔ p = 0 := by
  have hr : 0 < RootTransferPhase.residual p := residual_positive p hp
  unfold gap
  constructor
  · intro h
    have hl : Real.log (RootTransferPhase.residual p) = 0 := by linarith
    have h1 : RootTransferPhase.residual p = 1 := by
      rcases Real.log_eq_zero.mp hl with h | h | h
      · linarith
      · exact h
      · linarith
    unfold RootTransferPhase.residual at h1; linarith
  · rintro rfl
    simp [RootTransferPhase.residual]

/-- **The native `β` exchanges carrier axes `0` and `2`, and `1` and `3`.** -/
theorem beta_swaps_axes : ∀ (c : Fin 3) (v : CarrierEvents.Carrier c),
    CarrierEvents.vector (CarrierWeyl.lookup c 0 v) 0 = CarrierEvents.vector v 2 ∧
    CarrierEvents.vector (CarrierWeyl.lookup c 0 v) 2 = CarrierEvents.vector v 0 ∧
    CarrierEvents.vector (CarrierWeyl.lookup c 0 v) 1 = CarrierEvents.vector v 3 ∧
    CarrierEvents.vector (CarrierWeyl.lookup c 0 v) 3 = CarrierEvents.vector v 1 := by
  decide +kernel

/-- **Which carriers a `β` event moves across the reference axis.** For the vector class, `4` of the
`8` carriers change between on-axis and off-axis (`±2e₀ ↔ ±2e₂`); for the two spinor classes none do
(every spinor carrier has axis-`0` component `±1` before and after). -/
theorem beta_crossings : ∀ c : Fin 3,
    (Finset.univ.filter (fun v : CarrierEvents.Carrier c =>
      decide (CarrierEvents.vector v 0 = 0) ≠
        decide (CarrierEvents.vector (CarrierWeyl.lookup c 0 v) 0 = 0))).card =
      if c = 0 then 4 else 0 := by
  decide +kernel

/-- **Per protocol (vector class).** A lepton-axis carrier (`±2e₀`, `ν`/`e`) always leaves the axis
under `β`. -/
theorem lepton_always_crosses : ∀ v : CarrierEvents.Carrier 0,
    CarrierEvents.vector v 0 ≠ 0 → CarrierEvents.vector (CarrierWeyl.lookup 0 0 v) 0 = 0 := by
  decide +kernel

/-- **A colour carrier (`u`/`d`) reaches the axis under `β` exactly when it is on axis `2`.** -/
theorem colour_crosses_iff : ∀ v : CarrierEvents.Carrier 0, CarrierEvents.vector v 0 = 0 →
    (CarrierEvents.vector (CarrierWeyl.lookup 0 0 v) 0 ≠ 0 ↔ CarrierEvents.vector v 2 ≠ 0) := by
  decide +kernel

/-- For fixed carrier-coordinate chirality, no nonzero chirality flip on
these four coordinates is invariant under relabelling the three colour axes.
In particular, averaging an axis flip cannot preserve both properties. -/
theorem colour_invariant_flip_zero (B : ConcreteFermion.Spin)
    (hflip : B * ConcreteFermion.gamma = -(ConcreteFermion.gamma * B))
    (hcolour : ∀ a b : Fin 3, ∀ i j : Fin 4,
      B (Equiv.swap a.succ b.succ i) (Equiv.swap a.succ b.succ j) = B i j) :
    B = 0 := by
  have zero_of_self_neg {z : ℂ} (h : z = -z) : z = 0 := by linear_combination h / 2
  have same : ∀ i j : Fin 4, (i.val < 2 ↔ j.val < 2) → B i j = 0 := by
    intro i j hij
    have he := congrArg (fun M : ConcreteFermion.Spin => M i j) hflip
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num [ConcreteFermion.gamma, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four] at he
    all_goals first | exact zero_of_self_neg he | exact zero_of_self_neg he.symm
  have cover : ∀ i j : Fin 4, ∃ a b : Fin 3,
      ((Equiv.swap a.succ b.succ i).val < 2 ↔ (Equiv.swap a.succ b.succ j).val < 2) := by
    decide +kernel
  ext i j
  obtain ⟨a, b, hab⟩ := cover i j
  rw [← hcolour a b i j]
  exact same _ _ hab

end PMAction.NativeDetuning
