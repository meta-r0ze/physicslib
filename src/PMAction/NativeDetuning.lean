import PMAction.Machine.RootTransferPhase
import PMAction.Machine.CarrierWeyl

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

**Does the `β` event pass the reference node?** `beta_swaps_axes`: the native `β` (root word
`[1, 0, 2, 1]`, coordinate swaps only) exchanges carrier axes `0` and `2` (and `1` and `3`). It moves
carriers between the reference (lepton) axis and a colour axis: a type-changing event, which no
type-preserving gauge repair undoes (`PMFlavor.LeptonAxisRestriction`). So a wall's chirality flip
does pass the reference node. How many legs it uses is open:
* two legs, like a spinor carrier (`NodeAmplitude`, Kron series `α/2`): `p₁ = p_s`, `δ_O = k_f`;
* one leg (a carrier moved onto or off the axis once, `PMFlavor.NodeElimination.one_leg`, weight `α`):
  `p₁ = 2 p_s`, `δ_O ≈ 2 k_f`.
(The mass ratios once read off these values, golden `φ²` and silver `5.83`, used the retired
`WireLightSplit` assignment. On the wire of `PMAction.WireMass` the data put `δ_O/k_f` at `11`–`65`
per protocol, far from both; PMElementaryParticles REVIEW.)
Per protocol (`lepton_always_crosses`, `colour_crosses_iff`): every lepton-axis carrier crosses
under `β`; a colour carrier crosses only on axis `2`. `β`'s pairing of axis `0` with axis `2` is the
Dirac-basis choice; averaged over the three colour pairings a colour carrier crosses in `1/3` of
them. So, if `δ_O` scales with the crossing fraction, `δ_O(lepton) = 3 δ_O(quark)`, and up and down
get the same value (no source for the up/down split here). Candidate; the mass-product readings fail
directly (PMElementaryParticles REVIEW).
Both are candidates; the leg count of an on-site flip is the premise to derive. `beta_crossings`:
a `β` event moves `4` of the `8` vector-class carriers across the axis (each once: one leg), and no
spinor carrier (they touch the axis before and after). So for vector-class wall states the flip is a
one-leg event on half the carriers, which favours the one-leg reading for those states; for
spinor-class states the flip does not change axis contact at all. Testing either needs
a protocol that reads the wire's masses (PMElementaryParticles).
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

end PMAction.NativeDetuning
