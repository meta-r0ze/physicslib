import PMAction.NodeAmplitude
import PMAction.GenerationCurrent

/-!
# The other wall must be detuned

`ReferenceWallMass`: the light mass is `D_R (δ_O + cyc κ_O)`. If the other wall were also at the
Wilson point (`δ_O = 0`, no departure from `r = 1`, `PMAction.ZeroModeCoupling`), it would be
`D_R · cyc κ_O`.

* `diag_cyc`: a diagonal matrix times a cyclic shift is a cyclic shift with entries
  `a_{h+1} c_h`, so (`CyclicSeesaw.gram_cyc`, `undetuned_gram`) the masses are
  `|a_{h+1} c_h|`.
* With the class bookkeeping of `ReferenceWallMass` (row `g` carries `κ_R(e g)`, the shift's entry
  at `(h + 1, h)` is `κ_O(e h)`) and the swap × exchange symmetry (`κ_O(v) = κ_R(v) = K`,
  `κ_O(s) = κ_R(c)`, `κ_O(c) = κ_R(s)`, `|κ_R(s)| = |κ_R(c)| = k`), the entries are
  `κ_R(s) K`, `κ_R(c) κ_R(c)`, `K κ_R(s)`: `undetuned_masses` gives `(kK, k², kK)`.

**Corrected bookkeeping (2026-11).** The shift's entry at `(h + 1, h)` is the carrier that moves
wall-`true` generation `h` to `h + 1`, of class `e (h − 1)` (`GenerationCurrent.edge_carrier`; the
vector carrier joins the light generations `1`, `2`, `GenerationWeak.weak_edge_true`), not `e h`. With
the same symmetry the shift is `(κ_O(c), κ_O(v), κ_O(s)) = (κ_R(s), K, κ_R(c))`:
`undetuned_masses_matching` gives entries `κ_R(s)², κ_R(c) K, K κ_R(c)`, the same set
`(k², kK, kK)` when `|κ_R(s)| = |κ_R(c)|`. The conclusion below is unchanged; the light-pair structure
at `δ_O ≠ 0` is not (`PMAction.LightPairTexture`).

So with `δ_O = 0` there are two equal heavy masses and one light: the reverse of the observed
pattern (one heavy) in every charged sector. The other wall's detuning is therefore required, not
optional. What fixes its size is open (`PMAction/REVIEW-AND-NEXT.md`).
-/

noncomputable section
namespace PMAction.UndetunedWall
open Matrix PMAction.CyclicSeesaw

/-- **A diagonal times a cyclic shift is a cyclic shift.** -/
theorem diag_cyc (a c : Fin 3 → ℂ) :
    diagonal a * cyc c = cyc ![a 1 * c 0, a 2 * c 1, a 0 * c 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc, Matrix.diagonal_mul]

/-- **Its Gram matrix is diagonal**, so its masses are the entries' moduli. -/
theorem undetuned_gram (a c : Fin 3 → ℂ) :
    (diagonal a * cyc c)ᴴ * (diagonal a * cyc c) =
      diagonal fun j => star (![a 1 * c 0, a 2 * c 1, a 0 * c 2] j) *
        ![a 1 * c 0, a 2 * c 1, a 0 * c 2] j := by
  rw [diag_cyc, gram_cyc]

/-- **With the symmetry the undetuned entries are `(κ_R(s) K, κ_R(c)², K κ_R(s))`.** Rows carry
`(K, κ_R(s), κ_R(c))`; the shift carries `(κ_O(v), κ_O(s), κ_O(c)) = (K, κ_R(c), κ_R(s))`. -/
theorem undetuned_masses (K ks kc : ℂ) :
    diagonal ![K, ks, kc] * cyc ![K, kc, ks] = cyc ![ks * K, kc * kc, K * ks] := by
  rw [diag_cyc]; rfl

/-- **With the corrected bookkeeping** (shift `(κ_R(s), K, κ_R(c))`) the undetuned entries are
`(κ_R(s)², κ_R(c) K, K κ_R(c))`. -/
theorem undetuned_masses_matching (K ks kc : ℂ) :
    diagonal ![K, ks, kc] * cyc ![ks, K, kc] = cyc ![ks * ks, kc * K, K * kc] := by
  rw [diag_cyc]; rfl

end PMAction.UndetunedWall
