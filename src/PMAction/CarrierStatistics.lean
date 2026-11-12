import PMAction.LocalUnitary

/-!
# Carrier statistics: exchange is a relative full turn, and a full turn is `−1`

**The chain.**

1. On the substrate a state is an occupation of slots (site × label); "which carrier" is not a
   substrate fact. Exchanging two identical carriers maps a two-carrier amplitude `Ψ(a, b)` to
   `Ψ(b, a)` (`swap`). Doing it twice is the identity (`swap_swap`), so on any state it acts as a
   number, that number is `±1` (`exchange_sign`), and a phase is invisible to the readout
   (`ReadoutRule.born`).
2. **Premise (geometry).** Carriers move by the substrate's own hops, so an exchange is a pair of
   transports. With three spatial axes (the D₄ coordinate sector split 3 + 1, `PMConstants.AxisSplit`
   and Paper III's row assignment), such an exchange deforms into one carrier making a full `2π`
   turn relative to the other: the exchange phase is the full-turn phase.
3. **A full turn of a carrier is `−1`.** The carrier's spin `Σ` squares to one
   (`RunningResponse.spin_square`), so a rotation by `θ` acts as `cos(θ/2) − i sin(θ/2) Σ`
   (`spinRotation`). At `θ = 2π` this is `−1` (`two_pi_rotation`); at `4π` it is `1`
   (`four_pi_rotation`). The orbital part contributes `1` at `2π`. The carrier parity gives the
   same sign independently (`CarrierParity.carrier_exchange_parity`).
4. Hence the exchange phase is `−1` (`exchange_is_minus_one`), two-carrier states are
   antisymmetric, and two carriers never share a slot (`exclusion`).

On a site the observed single-carrier modes number `24` (`CarrierClassBundle.observed_card`), so
at most `24` carriers occupy one site's observed modes. This is not the substrate's
`nodeCapacity` (`32`).
-/

noncomputable section
namespace PMAction.CarrierStatistics
open Matrix

section Turn
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spin-½ rotation by `θ`: `cos(θ/2) − i sin(θ/2) Σ`. -/
def spinRotation (S : Matrix n n ℂ) (θ : ℝ) : Matrix n n ℂ := LocalUnitary.rotation S (-(θ / 2))

/-- **A full turn is `−1`.** -/
theorem two_pi_rotation (S : Matrix n n ℂ) : spinRotation S (2 * Real.pi) = -1 := by
  unfold spinRotation LocalUnitary.rotation
  rw [show -(2 * Real.pi / 2) = -Real.pi by ring, Real.cos_neg, Real.sin_neg, Real.cos_pi,
    Real.sin_pi]
  simp

/-- **Two full turns are `1`.** -/
theorem four_pi_rotation (S : Matrix n n ℂ) : spinRotation S (4 * Real.pi) = 1 := by
  unfold spinRotation LocalUnitary.rotation
  rw [show -(4 * Real.pi / 2) = -(2 * Real.pi) by ring, Real.cos_neg, Real.sin_neg,
    Real.cos_two_pi, Real.sin_two_pi]
  simp

/-- The rotation is unitary when `Σ` is a Hermitian involution (`LocalUnitary.rotation_unitary`),
so `spinRotation` is a genuine rotation of the carrier's amplitude. -/
theorem spinRotation_unitary (S : Matrix n n ℂ) (hh : S.IsHermitian) (h2 : S * S = 1)
    (θ : ℝ) : spinRotation S θ ∈ unitary (Matrix n n ℂ) :=
  LocalUnitary.rotation_unitary S _ hh h2

end Turn

section Exchange
variable {X : Type*}

/-- Exchanging two carriers. -/
def swap (Ψ : X → X → ℂ) : X → X → ℂ := fun a b => Ψ b a

theorem swap_swap (Ψ : X → X → ℂ) : swap (swap Ψ) = Ψ := rfl

theorem swap_smul (c : ℂ) (Ψ : X → X → ℂ) : swap (c • Ψ) = c • swap Ψ := rfl

/-- **The exchange sign is `±1`.** -/
theorem exchange_sign (Ψ : X → X → ℂ) (hΨ : Ψ ≠ 0) (c : ℂ) (h : swap Ψ = c • Ψ) :
    c = 1 ∨ c = -1 := by
  have h2 : Ψ = (c * c) • Ψ := by
    calc Ψ = swap (swap Ψ) := rfl
      _ = swap (c • Ψ) := by rw [h]
      _ = c • swap Ψ := swap_smul c Ψ
      _ = c • (c • Ψ) := by rw [h]
      _ = (c * c) • Ψ := smul_smul c c Ψ
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hΨ
  obtain ⟨b, hb⟩ := Function.ne_iff.mp ha
  have hab := congrFun (congrFun h2 a) b
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hab hb
  have hcc : c * c = 1 := by
    have : (c * c - 1) * Ψ a b = 0 := by linear_combination -hab
    rcases mul_eq_zero.mp this with h0 | h0
    · linear_combination h0
    · exact absurd h0 hb
  exact mul_self_eq_one_iff.mp hcc

/-- **The exchange phase is the full-turn phase, `−1`.** With the geometric premise that the
exchange phase `c` acts as the relative full turn `spinRotation Σ (2π)` (on a nonempty index
set), `c = −1`. -/
theorem exchange_is_minus_one {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (S : Matrix n n ℂ) (c : ℂ) (hturn : spinRotation S (2 * Real.pi) = c • 1) : c = -1 := by
  rw [two_pi_rotation] at hturn
  obtain ⟨i⟩ := ‹Nonempty n›
  have := congrFun (congrFun hturn i) i
  simpa using this.symm

/-- **Exclusion.** An antisymmetric two-carrier amplitude vanishes on a shared slot. -/
theorem exclusion (Ψ : X → X → ℂ) (h : swap Ψ = (-1 : ℂ) • Ψ) (a : X) : Ψ a a = 0 := by
  have h1 := congrFun (congrFun h a) a
  simp only [swap, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : (2 : ℂ) * Ψ a a = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h0 | h0
  · norm_num at h0
  · exact h0

end Exchange

end PMAction.CarrierStatistics
