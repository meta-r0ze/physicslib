import Mathlib.Tactic
import PMAction.GenerationWalls

/-!
# An equal-class wall crossing never keeps the generation, so it cannot carry the mass hierarchy

The E₈ gluing pairs equal glue classes across the two `D₄` walls (`PMSubstrate.ChannelSymmetry`,
`GenerationLabel`). An operation joining the walls is then a crossing that keeps the class: a
class-`c` carrier on one wall goes to a class-`c` carrier on the other. That is the inter-wall hop
of `PMAction.GenerationWalls` (the native label is kept), and the inter-wall term is the mass
(`PMAction.WallTransfer`, `WallSeesaw`).

* `crossing_changes_generation`: the generation that has class `c` on one wall is never the
  generation that has class `c` on the other wall (`GenerationWalls.omitted`). So an equal-class
  crossing always changes the generation: the inter-wall link `Y_gap` (the `Y` of `WallSeesaw`) has
  **zero generation diagonal**.
* `traceless_close_pair`: three reals summing to zero have their largest absolute value at most
  twice the middle one. This applies to the singular values only when `Y_gap` is **Hermitian**
  (its eigenvalues are then real and sum to zero); `WallExchange.exchange_symmetry_iff` makes it
  Hermitian exactly under the wall-parity exchange symmetry.
* `seesaw_close_pair`: so under `WallSeesaw` (light masses `c/σᵢ`) the two lightest generations
  have masses within a factor `2`. The exact one-flavour mass `(√(σ² + 4δ₀²) − σ)/2` keeps the
  factor `2` (it is `2δ₀²/(√(σ² + 4δ₀²) + σ)`, and doubling `σ` at most halves it).
* `no_measured_lepton_traceless`: the measured charged leptons are pairwise more than a factor
  `4` apart (`measured_gaps`), so no such link gives them. The same holds for every
  quark sector (smallest ratio `m_s/m_d ≈ 20`).

**Scope (audit).** The equal-class crossing is directional: class `c` sits in generation `c − 1` on
wall 1 and in `c + 1` on wall 2, so the wall-2-to-wall-1 block has one entry per row, a weighted
cyclic shift. Its singular values are the three class amplitudes and can be anything (e.g.
`1, 10, 100`); the traceless argument does not apply. Two cases follow. (i) Under the wall-parity
symmetry `Y_gap` is Hermitian, so it holds both directions, and the results below apply. (ii)
Without it, the seesaw gives one Dirac pair per class with mass `δ²/|y_c|`; with the library's
amplitudes (vector class in-cycle, order `1`; spinor classes through the node, order `α`) that is one
light pair and two heavy ones, the reverse of the data. Case (ii) is excluded only through that
amplitude assignment, not by this module's theorems.

**Result (case (i)).** With the gluing premise and a Hermitian `Y_gap`, the mass hierarchy
cannot come from the inter-wall link alone: it needs a generation-diagonal term. An equal-class
crossing cannot supply one. A crossing that changes the class by the generation label (class `b` on
one wall to class `c` on the other, `b ≠ c`) would, but it is not an E₈ vector, so it is a
composite: a crossing and a single-wall carrier shift. This is the open question in
`REVIEW-AND-NEXT.md`, now narrowed: the diagonal mass is a composite process or a flavour-dependent
on-site term, and the off-diagonal (equal-class) part is what the gluing allows directly.
-/

noncomputable section
namespace PMAction.InterWallDiagonal
open PMAction.GenerationWalls

/-- Measured charged-lepton masses in MeV (PDG 2024). -/
def IsMeasuredLepton (m : ℝ) : Prop := m = 0.51099895 ∨ m = 105.6583755 ∨ m = 1776.93

theorem measured_gaps (a b : ℝ) (ha : IsMeasuredLepton a) (hb : IsMeasuredLepton b) (h : a < b) :
    4 * a < b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | (norm_num at h; done) | norm_num

/-- **An equal-class crossing always changes the generation.** -/
theorem crossing_changes_generation : ∀ (b : Bool) (c : Fin 3), omitted b c ≠ omitted (!b) c := by
  decide

/-- **Three reals summing to zero**: the largest absolute value is at most twice the middle one. -/
theorem traceless_close_pair (a b c : ℝ) (h : a + b + c = 0) (hcb : |c| ≤ |b|) :
    |a| ≤ 2 * |b| := by
  have ha : a = -(b + c) := by linarith
  rw [ha, abs_neg]
  calc |b + c| ≤ |b| + |c| := abs_add_le b c
    _ ≤ 2 * |b| := by linarith

/-- **Seesaw masses of a traceless link**: the two lightest are within a factor `2`. With
`|b| ≤ |a| ≤ 2|b|`, the masses `k/|a| ≤ k/|b|` satisfy `k/|b| ≤ 2 · (k/|a|)`. -/
theorem seesaw_close_pair (k a b : ℝ) (hk : 0 < k) (hb : 0 < |b|) (ha : 0 < |a|)
    (hab : |a| ≤ 2 * |b|) : k / |b| ≤ 2 * (k / |a|) := by
  rw [show 2 * (k / |a|) = (2 * k) / |a| by ring, div_le_div_iff₀ hb ha]
  nlinarith [mul_le_mul_of_nonneg_left hab hk.le]

/-- **No traceless link gives two measured charged leptons** as its two lightest masses. -/
theorem no_measured_lepton_traceless (k a b : ℝ) (hk : 0 < k) (hb : 0 < |b|) (hba : |b| ≤ |a|)
    (hab : |a| ≤ 2 * |b|) (hlo : IsMeasuredLepton (k / |a|)) (hhi : IsMeasuredLepton (k / |b|))
    (hne : k / |a| ≠ k / |b|) : False := by
  have ha : 0 < |a| := lt_of_lt_of_le hb hba
  have hle : k / |a| ≤ k / |b| := div_le_div_of_nonneg_left hk.le hb hba
  have hlt : k / |a| < k / |b| := lt_of_le_of_ne hle hne
  have h4 := measured_gaps _ _ hlo hhi hlt
  have h2 := seesaw_close_pair k a b hk hb ha hab
  have hpos : 0 < k / |a| := div_pos hk ha
  linarith

end PMAction.InterWallDiagonal
