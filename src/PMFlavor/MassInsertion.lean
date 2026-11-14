import PMFlavor.GenerationLabel
import PMFlavor.InterWallDiagonal

/-!
# A generation's diagonal mass needs an insertion of its own label class

`InterWallDiagonal`: the E₈ gluing pairs equal classes, so an equal-class crossing never keeps the
generation and cannot give a diagonal mass. This module asks what a diagonal mass needs, in the
glue algebra of `GenerationLabel` (a generation puts class `b` on one wall and `c` on the other,
label `m = b + c`).

* `bilinear_gap`: a bilinear joining class `b` on one wall to class `c` on the other has class gap
  `b + c`, zero exactly when `b = c`. A generation's own mass bilinear joins its two classes, so its
  gap is its label `m ≠ 0`: **a diagonal mass needs an insertion of the label class.** The
  equal-class crossing is the gap-zero case.
* `label_is_reference_iff`: the generation whose label is the reference's class `v` is exactly the
  one containing neither copy of `v` (both of its classes are spinor). Its insertion is a vector
  displacement, which can stay off the reference axis (`ExchangeAxis.vector_free`, in-cycle); the
  other two generations' insertions are spinor displacements, which always touch it
  (`ExchangeAxis.spinor_touch`, a node crossing).
* `label_v_mixings_cross`, `other_has_in_cycle`: the same generation is the only one whose mixings with both others go
  through spinor classes (`GenerationLabel.transition_class`: generations `m, m'` mix through
  `m + m'`). So the generation with the unsuppressed mass insertion is the one with two
  node-suppressed mixings, and the other two mix with each other in-cycle.

**The data fix which way the insertion acts** (ordering only, no fitted numbers). If the insertion
enters the mass directly (larger amplitude, heavier), the label-`v` generation is the heaviest and
weakly mixed: `|V_ub|, |V_cb|` node-suppressed and `|V_us|` in-cycle, as observed
(`0.0037, 0.041 ≪ 0.225`). If it enters the inter-wall link `Y` and the masses are `δ²/σ(Y)`
(`PMAction.WallSeesaw`, larger entry, lighter), the label-`v` generation is the lightest; then
`|V_us|` and `|V_ub|` are node-suppressed and `|V_cb|` is in-cycle, the reverse of the data
(`|V_us| = 0.225 > |V_cb| = 0.041`). So the diagonal mass is not an entry of `Y` read through the
seesaw: either it is an in-wall (on-site) chirality flip, or `WallSeesaw`'s identification of the
light masses with `δ²/σ(Y)` (stated there as an input) does not hold for it.

**On-site insertions through the seesaw fail too.** Put the insertions in the on-site slot
(`D = diag(δ_m)` in place of `PMAction.WallExchange`'s flavour-blind `δ`) and keep the inter-wall
link the equal-class crossing (zero diagonal, `InterWallDiagonal`). The zero-energy reduction gives
`D Y⁻¹ D`; eliminating the heavy generation leaves `D_l (Y_ll)⁻¹ D_l` (block inverse, the Schur
complement of `Y⁻¹` is the inverse of `Y`'s light block). `Y_ll = [[0, x], [x̄, 0]]`, whose inverse is
off-diagonal (`light_block_inverse`), so both light masses are `δ_s δ_c/|x|`
(`light_pair_degenerate`): a degenerate pair at leading order, whatever the moduli, flux or
insertions. Numerically (outside Lean) the full ratio stays below `1.52` over random parameters;
every sector's light pair is at least `16.8` apart. So the light masses do not come from inverting
a link (`δ²Y⁻¹` or `D Y⁻¹ D`). What is left is a term that joins the two chiral zero modes directly
(wall 1 `Γ = +1` to wall 2 `Γ = −1`, the slot of `WallSeesaw`'s effective `M`), carrying the label
class, so the mass matrix is generation-diagonal with entries set by the insertions. This is the
premise of the transfer reading (`TransferGenerator`). It is what survives, not yet a derivation:
the library's wall Hamiltonian has no such direct zero-mode term (its inter-wall hop joins the
gapped components), and the equal-class crossing the gluing allows would add generation off-diagonal
mass entries unless it is absent or small (`PMAction/REVIEW-AND-NEXT.md`).

What this does not give: the size of the node suppression of the two light generations' masses,
or what splits those two (the `s`/`c` asymmetry, `ExchangeChirality`). For leptons the third
generation is not weakly mixed (PMNS), so the lepton side needs its own reading (`NodeElimination`:
lepton-axis states mix by one leg).
-/

namespace PMFlavor.MassInsertion
open GenerationLabel

/-- **The class gap of a two-wall bilinear is the class sum**, zero exactly for equal classes. -/
theorem bilinear_gap : ∀ b c : Glue, label b c = 0 ↔ b = c := by decide

/-- **The label-`v` generation is the one without `v`.** For distinct nontrivial classes `b, c` and
nontrivial `v`, `b + c = v` exactly when neither class is `v`. -/
theorem label_is_reference_iff : ∀ b c v : Glue, b ≠ 0 → c ≠ 0 → v ≠ 0 → b ≠ c →
    (label b c = v ↔ b ≠ v ∧ c ≠ v) := by decide

/-- **The label-`v` generation mixes with each other generation through a class other than `v`.** -/
theorem label_v_mixings_cross : ∀ v m' : Glue, v ≠ 0 → m' ≠ 0 → m' ≠ v → v + m' ≠ v := by decide

/-- **Every other generation has one in-cycle mixing**: generation `m ≠ v` mixes with `m + v`
through `v` itself. -/
theorem other_has_in_cycle : ∀ m v : Glue, m ≠ 0 → v ≠ 0 → m ≠ v →
    m + v ≠ 0 ∧ m + v ≠ m ∧ m + (m + v) = v := by decide

/-- **The light block of a zero-diagonal link inverts to an off-diagonal block.** -/
theorem light_block_inverse (x : ℂ) (hx : x ≠ 0) :
    !![0, x; (starRingEnd ℂ) x, 0] * !![0, 1 / (starRingEnd ℂ) x; 1 / x, 0] = 1 := by
  have hx' : (starRingEnd ℂ) x ≠ 0 := (map_ne_zero _).mpr hx
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hx']

/-- **The two light masses are equal at leading order**: `D_l (Y_ll)⁻¹ D_l` is off-diagonal with
entries `δ_s δ_c / x̄` and `δ_s δ_c / x`, of equal modulus. -/
theorem light_pair_degenerate (δs δc : ℝ) (x : ℂ) :
    ‖((δs * δc : ℝ) : ℂ) * (1 / (starRingEnd ℂ) x)‖ = ‖((δs * δc : ℝ) : ℂ) * (1 / x)‖ := by
  simp

end PMFlavor.MassInsertion
