import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The protocol readout: how a weak pair reads its shared wire mode

`DoubletSign`: a weak pair shares one wire mode (an axis in one sector). Its two channels are
`|±⟩ = (o ± e)/√2`, with `o` the odd (wire) mode of the axis and `e` the even mode.

**Premise (readout).** A protocol reads an operator `H` as the expectation of `H` in its
channel's carrier state. (Unnormalized below: `o ± e`; divide by `2` for unit states.)

* `partner_difference`: the two partners' readings differ by `2 (⟨o|H|e⟩ + ⟨e|H|o⟩)`, the odd/even
  cross term, for any `H`. So an operator with no cross term (one that commutes with the antipode,
  or the wire with an inert even sector) gives both partners the same reading.
* `projector_cross`: for a projector onto a state `r`, the cross term is `⟨o|r⟩⟨r|e⟩`.
* `reference_reading`: adding `ε |r⟩⟨r|` to an operator with no cross term makes the partners differ
  by `4ε ⟨o|r⟩⟨r|e⟩`.

**Applied to the reference** (`r` = the reference carrier `+2e₀ = (o₀ + e₀)/√2`, the only
antipode-odd object, `DoubletSign`):
* lepton axis (`o = o₀`, `e = e₀`): `⟨o₀|r⟩ ⟨r|e₀⟩ ≠ 0`, so `ν` and `e` read differently at first order;
* colour axis `i ≠ 0`: `o_i`, `e_i` are orthogonal to `r`, so up and down read the same at first
  order. Their difference needs an operator that carries axis `i` to axis `0` (the native `β`, at
  second order; colour-symmetric only when averaged over the three colour pairings,
  PMAction REVIEW).

**Prediction (qualitative, a test).** The partner asymmetry is first order for the lepton pair and
at least second order for the quark pairs, so it must be much larger for leptons. Data: the
neutral lepton protocol's masses are below the electron protocol's by more than `10⁵`; the up and
down protocols' masses differ by factors from `0.5` to `60`. Consistent. A quark pair with a
larger asymmetry than the lepton pair would falsify this readout.
-/

namespace PMElementaryParticles.ProtocolReadout
open Matrix

variable {n : Type*} [Fintype n]

theorem partner_difference (H : Matrix n n ℝ) (o e : n → ℝ) :
    (o + e) ⬝ᵥ (H *ᵥ (o + e)) - (o - e) ⬝ᵥ (H *ᵥ (o - e)) =
      2 * (o ⬝ᵥ (H *ᵥ e) + e ⬝ᵥ (H *ᵥ o)) := by
  simp only [mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct, dotProduct_add,
    dotProduct_sub]
  ring

theorem projector_cross (r o e : n → ℝ) :
    o ⬝ᵥ (vecMulVec r r *ᵥ e) = (o ⬝ᵥ r) * (r ⬝ᵥ e) := by
  simp only [dotProduct, mulVec, vecMulVec_apply]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem reference_reading (H₀ : Matrix n n ℝ) (ε : ℝ) (r o e : n → ℝ)
    (h₁ : o ⬝ᵥ (H₀ *ᵥ e) = 0) (h₂ : e ⬝ᵥ (H₀ *ᵥ o) = 0) :
    (o + e) ⬝ᵥ ((H₀ + ε • vecMulVec r r) *ᵥ (o + e)) -
        (o - e) ⬝ᵥ ((H₀ + ε • vecMulVec r r) *ᵥ (o - e)) =
      4 * ε * (o ⬝ᵥ r) * (r ⬝ᵥ e) := by
  have hs : ∀ v : n → ℝ, (ε • vecMulVec r r) *ᵥ v = ε • (vecMulVec r r *ᵥ v) := fun v => by
    ext i
    simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [partner_difference]
  simp only [add_mulVec, dotProduct_add, h₁, h₂, hs, dotProduct_smul, projector_cross,
    smul_eq_mul, zero_add]
  rw [dotProduct_comm e r, dotProduct_comm r o]
  ring

end PMElementaryParticles.ProtocolReadout
