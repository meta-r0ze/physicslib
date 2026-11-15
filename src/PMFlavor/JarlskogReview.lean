import PMFlavor.CKM

/-!
# The two Jarlskog values are different quantities

Paper IV's `J` is fixed by its four mixing parameters (`CKM.pm_jarlskog_matrix`): `pmJ ∈ (3.02, 3.03)·10⁻⁵`.
Paper III's `J_geo = φ²ηT_geo` is an independent formula: `pm3J ∈ (3.0848, 3.0850)·10⁻⁵`. Once the
angles and phase are fixed, `J` has no remaining freedom, so the two cannot both be `J`.

* `ratio_window`: `pmJ / pm3J ∈ (0.9789, 0.9823)`; no simple invariant factor reconciles them.
* `eta_not_the_fix`: dropping `η` moves `J_geo` further away, to `φ²T_geo ∈ (3.1028, 3.1031)·10⁻⁵`.

Paper IV classifies angles and phases as topological, free of the overhead `η` (its §3, "Topology vs.
Volume"); `J` is built only from angles and the phase, so applying `η` to it, as `J_geo` does,
contradicts that classification.
-/

noncomputable section
namespace PMFlavor.JarlskogReview
open PMFlavor.CKM

theorem ratio_window : 0.9789 < pmJ / pm3J ∧ pmJ / pm3J < 0.9823 := by
  have h1 := pmJ_bounds; have h2 := pm3J_bounds
  have hp : 0 < pm3J := by linarith [h2.1]
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

def geoNoEta : ℝ := ((1 + Real.sqrt 5) / 2) ^ 2 * (2 * (172 - 5) / (32 ^ 3 * 5 * 172))

theorem eta_not_the_fix : 3.1028e-5 < geoNoEta ∧ geoNoEta < 3.1031e-5 := by
  have h1 : (2.236067 : ℝ) < Real.sqrt 5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 5 < (2.236068 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold geoNoEta
  constructor <;> nlinarith [h1, h2]

/-- The Jarlskog quartet is invariant under independent unit phases on rows
and columns; det V=1 is a convention, not an observable mass-phase argument. -/
theorem jarlskog_rephasing (U : Fin 3 → Fin 3 → ℂ) (r c : Fin 3 → ℂ)
    (hr : ∀ i, r i*star (r i)=1) (hc : ∀ i, c i*star (c i)=1) :
    PMFlavor.CKM.jarlskog (fun i j => r i*U i j*star (c j))=PMFlavor.CKM.jarlskog U := by
  have he :
      (r 0*U 0 0*star (c 0))*(r 1*U 1 1*star (c 1))*
        star (r 0*U 0 1*star (c 1))*star (r 1*U 1 0*star (c 0)) =
      (r 0*star (r 0))*(r 1*star (r 1))*(c 0*star (c 0))*(c 1*star (c 1))*
        (U 0 0*U 1 1*star (U 0 1)*star (U 1 0)) := by
    simp only [star_mul,star_star]
    ring
  have hf :
      (r 0*U 0 0*star (c 0))*(r 1*U 1 1*star (c 1))*
        star (r 0*U 0 1*star (c 1))*star (r 1*U 1 0*star (c 0)) =
      U 0 0*U 1 1*star (U 0 1)*star (U 1 0) := by
    rw [he,hr 0,hr 1,hc 0,hc 1]
    simp
  exact congrArg Complex.im hf

end PMFlavor.JarlskogReview
