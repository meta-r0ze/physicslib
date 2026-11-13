import PMConstants.VacuumModulus

/-!
# The selected vacuum has `θ̄ = 0` for any quark mass phase

`HermitianMass` and `SectorExchange` reach `θ̄ = 0` in two steps: the vacuum selects `θ = 0`
(`VacuumModulus.strict_modulus`), and Hermitian positive masses make `arg det M = 0`. The second
step needs a unique least-cost update (`exchange_fixed_of_unique`), which fails for continuous
tie families (`PMFlavor.ReferenceSelection`).

With quarks the second step is not needed. The vacuum phase `θ` is what persistence selects (the
premise `VacuumModulus` already uses), and the winding weights it selects from carry the quark
mass phase:

**Premise (chiral anomaly).** Write `α = arg det(M_u M_d)`. A history of winding `n` carries the
mass phase `e^{−inα}` times a nonnegative weight `w n` computed with the masses made real and
positive. On the substrate this is derived with the winding read as the transfer count
(`PMAction.WallTransfer`): chirality changes only by carriers moving between the two walls
(Conservation, `chirality_change`); a flavour-blind background moves the same number `n` in every
flavour (`flavour_blind_transfer`); and fermion statistics make the amplitude of those moves through
`M` carry `(det M)ⁿ`, phase `n·arg det M` (`history_factor`, `FermionFlip.winding_phase`). With real
positive masses the factor is positive, so `w n ≥ 0`. What stays imported is the identification of
the transfer count with the lattice topological charge (Lüscher).

* `Zm`: the vacuum weight with that phase, `Σₙ wₙ e^{−inα} e^{inθ}`.
* `Zm_eq`: `Zm(θ) = Z(θ − α)`; the vacuum only sees `θ̄ = θ − α`.
* `selected_unique`: with the trivial and unit windings weighted, `‖Zm(θ)‖ < ‖Zm(α)‖` for every
  `θ ≠ α` with `θ − α ∈ (−π, π]`. The least-cost vacuum is `θ = α`.
* `thetaBar_least_cost`, `thetaBar_selected_zero`: in terms of `HermitianMass.thetaBar`, every
  vacuum with `θ̄ ≠ 0` costs strictly more, and the selected one has `θ̄ = 0`.

So `θ̄ = 0` holds for any invertible `M_u, M_d`, Hermitian or not; the uniqueness premise of
`SectorExchange` is no longer on the strong-CP path. The weights' positivity is
`WindingWeights.theta_zero_admissible`. In the Standard Model this relaxation is the axion's job;
here it is the persistence selection of the vacuum phase.
-/

noncomputable section
namespace PMConstants.ThetaBarSelection
open Complex HermitianMass

/-- Vacuum weight with the quark mass phase `α` carried once per unit winding. -/
def Zm (S : Finset ℤ) (w : ℤ → ℝ) (α θ : ℝ) : ℂ :=
  ∑ n ∈ S, (w n : ℂ) * Complex.exp ((-((n : ℝ) * α) : ℝ) * I) *
    Complex.exp (((n : ℝ) * θ : ℝ) * I)

/-- **The vacuum sees only `θ − α`.** -/
theorem Zm_eq (S : Finset ℤ) (w : ℤ → ℝ) (α θ : ℝ) : Zm S w α θ = Z S w (θ - α) := by
  unfold Zm Z
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The least-cost vacuum is `θ = α`, uniquely.** -/
theorem selected_unique (S : Finset ℤ) (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (h0 : (0 : ℤ) ∈ S) (h1 : (1 : ℤ) ∈ S) (hw0 : 0 < w 0) (hw1 : 0 < w 1) (α θ : ℝ)
    (hθ : θ - α ∈ Set.Ioc (-Real.pi) Real.pi) (hne : θ ≠ α) :
    ‖Zm S w α θ‖ < ‖Zm S w α α‖ := by
  rw [Zm_eq, Zm_eq, sub_self, Z_zero, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun n _ => hw n)]
  exact VacuumModulus.strict_modulus S w hw h0 h1 hw0 hw1 (θ - α) hθ (sub_ne_zero.mpr hne)

/-- **Every vacuum with `θ̄ ≠ 0` costs strictly more than the one with `θ̄ = 0`.** -/
theorem thetaBar_least_cost (S : Finset ℤ) (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (h0 : (0 : ℤ) ∈ S) (h1 : (1 : ℤ) ∈ S) (hw0 : 0 < w 0) (hw1 : 0 < w 1)
    (Mu Md : Matrix (Fin 3) (Fin 3) ℂ) (θ : ℝ)
    (hθ : thetaBar θ Mu Md ∈ Set.Ioc (-Real.pi) Real.pi) (hne : thetaBar θ Mu Md ≠ 0) :
    ‖Zm S w (Mu.det * Md.det).arg θ‖ <
      ‖Zm S w (Mu.det * Md.det).arg (Mu.det * Md.det).arg‖ :=
  selected_unique S w hw h0 h1 hw0 hw1 _ θ hθ fun h => hne (by unfold thetaBar; rw [h, sub_self])

/-- **The selected vacuum has `θ̄ = 0`.** -/
theorem thetaBar_selected_zero (Mu Md : Matrix (Fin 3) (Fin 3) ℂ) :
    thetaBar (Mu.det * Md.det).arg Mu Md = 0 := sub_self _

end PMConstants.ThetaBarSelection
