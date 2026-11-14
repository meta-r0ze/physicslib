import PMFlavor.LinkHierarchy
import PMConstants.GenerationWalls

/-!
# An equal-class wall crossing never keeps the generation, so it cannot carry the mass hierarchy

The E₈ gluing pairs equal glue classes across the two `D₄` walls (`PMSubstrate.ChannelSymmetry`,
`GenerationLabel`). An operation joining the walls is then a crossing that keeps the class: a
class-`c` carrier on one wall goes to a class-`c` carrier on the other. That is the inter-wall hop
of `PMConstants.GenerationWalls` (the native label is kept), and the inter-wall term is the mass
(`PMAction.WallTransfer`, `WallSeesaw`).

* `crossing_changes_generation`: the generation that has class `c` on one wall is never the
  generation that has class `c` on the other wall (`GenerationWalls.omitted`). So an equal-class
  crossing always changes the generation: the inter-wall link `Y` has **zero generation diagonal**,
  hence trace zero.
* `traceless_close_pair`: three reals summing to zero have their largest absolute value at most
  twice the middle one.
* `seesaw_close_pair`: so under `WallSeesaw` (light masses `c/σᵢ`) the two lightest generations
  have masses within a factor `2`. The exact one-flavour mass `(√(σ² + 4δ₀²) − σ)/2` keeps the
  factor `2` (it is `2δ₀²/(√(σ² + 4δ₀²) + σ)`, and doubling `σ` at most halves it).
* `no_measured_lepton_traceless`: the measured charged leptons are pairwise more than a factor
  `4` apart (`LinkHierarchy.measured_gaps`), so no such link gives them. The same holds for every
  quark sector (smallest ratio `m_s/m_d ≈ 20`).

**Result.** With the gluing premise (the inter-wall term pairs equal classes), the mass hierarchy
cannot come from the inter-wall link alone: it needs a generation-diagonal term. An equal-class
crossing cannot supply one. A crossing that changes the class by the generation label (class `b` on
one wall to class `c` on the other, `b ≠ c`) would, but it is not an E₈ vector, so it is a
composite: a crossing and a single-wall carrier shift. This is the open question in
`REVIEW-AND-NEXT.md`, now narrowed: the diagonal mass is a composite process or a flavour-dependent
on-site term, and the off-diagonal (equal-class) part is what the gluing allows directly.
-/

noncomputable section
namespace PMFlavor.InterWallDiagonal
open PMConstants.GenerationWalls LinkHierarchy

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

end PMFlavor.InterWallDiagonal
