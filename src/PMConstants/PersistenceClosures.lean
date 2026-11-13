import PMConstants.ReferenceEconomy
import PMConstants.HermitianMass

/-!
# Closures by persistence

Five premises left open by the reference chain, each settled by asking what persists.

**Exact restoration, from Finiteness (partial).** `finite_restorer_exact`: on a finite state space
with the discrete topology, a restorer under which every state converges to the reference state
reaches it exactly, after one uniform number of updates. Such a map is not reversible
(`reversible_cannot_collapse`): it needs records or an environment. The bridge to the
real-linear restorer **is** proved, in Paper II: an operational encoding law
`encode (f s) = (id − K)(encode s)` on a spanning encoding forces `K` nilpotent and
`PMAction.FiniteRestorationBridge.finite_restoration_gain_trace`/`convergent_gain_trace` give
`trace K = finrank V`. So `ReferenceRestoration.finite_restore_trace` (the `V = ℝ × ℂ` case,
trace `3`) is its instance; the encoding law is the remaining premise, not the bridge.

**The link's charge, from covariance.** The restoring term pairs the regulator (charge `a`) with the
displacement it cancels (charge `b`). Under a phase action it changes by `exp(iθ(a+b))`.
`invariant_iff`: it is invariant for every `θ` exactly when `a = -b`. A non-invariant term would be
moved by the gauge action, and the regulation would not persist under it. With the reference's
hypercharge `Y_L = -1`, `link_from_covariance` gives the link charge `h = 1` and, with flux
conservation and the unit link, the standard charges and `Y_ν = 0`.

**θ̄ = 0, from minimum cost.** `HermitianMass.theta_zero_maximal` gives `‖Z(θ)‖ ≤ Z(0)` from the
positive transfer weights, and `theta_pi_costlier` separates `0` from `π`.
`strict_vafa_witten`: with the unit winding sector weighted, `Re Z(θ) < Z(0)` for every `θ ≠ 0` in
`(-π, π]`, so `θ = 0` is the unique least-cost vacuum on the whole circle **when the cost is read
from `Re Z`**. `abs_not_unique` gives positive weights (on `{−1, 1}` only) for which
`‖Z(π)‖ = Z(0)`; once the trivial sector is weighted the modulus decides too
(`VacuumModulus.strict_modulus`), and `WindingWeights` derives that weight.
`strict_selects_zero` records the selection step: a least-cost `θ` under a strict inequality is `0`.
Premise: `θ̄` is a vacuum variable the selection acts on. `θ̄ = θ` via Hermitian masses
(`HermitianMass`, `WallParityExchange`) is no longer needed: with the chiral-anomaly premise the
selection lands on `θ̄ = 0` for any mass phase (`ThetaBarSelection`).

**One repair, from persistence and Economy.** `one_repair`: an unmaintained state does not persist,
so the repair count is positive, and Economy takes the least such count, `1`. This fixes the count
only, not the physical content of the repair.

**Distinct labels, from maximin.** `repeat_lowers_margin`: counting a label twice adds an entry and
lowers every label's maximin gain `(B - s)/N`, so the maximin allocation counts each label once.
With `ReferenceRestoration.unique_decomposition` the labels are `ν + σ + χ`, given that they are
architecture inputs.
-/

noncomputable section
namespace PMConstants.PersistenceClosures
open Filter Topology

/-- **On a finite substrate, a convergent restorer is exact.** -/
theorem finite_restorer_exact {S : Type*} [Finite S] [TopologicalSpace S] [DiscreteTopology S]
    (f : S → S) (p : S) (hconv : ∀ x, Tendsto (fun n => f^[n] x) atTop (𝓝 p)) :
    ∃ N, ∀ n ≥ N, ∀ x, f^[n] x = p := by
  have h : ∀ x, ∀ᶠ n in atTop, f^[n] x = p := fun x => by
    have := hconv x
    rw [nhds_discrete, tendsto_pure] at this
    exact this
  have hall : ∀ᶠ n in atTop, ∀ x, f^[n] x = p := eventually_all.mpr h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  exact ⟨N, hN⟩

/-- **A phase-invariant pairing has opposite charges.** -/
theorem invariant_iff (a b : ℝ) :
    (∀ θ : ℝ, Complex.exp (Complex.I * (θ * (a + b))) = 1) ↔ a = -b := by
  constructor
  · intro h
    by_contra hne
    have hc : a + b ≠ 0 := fun h0 => hne (by linarith)
    have := h (Real.pi / (a + b))
    have hpi : ((Real.pi / (a + b) : ℝ) : ℂ) * ((a + b : ℝ) : ℂ) = Real.pi := by
      rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hc]
    push_cast at hpi this
    rw [hpi, mul_comm, Complex.exp_pi_mul_I] at this
    norm_num at this
  · rintro rfl θ
    simp

/-- **Covariance gives the link charge and the neutral sterile channel.** -/
theorem link_from_covariance (Y : Hypercharge.Charges) (hf : Hypercharge.Flux Y) (h : ℚ)
    (hl : SectorLinks.OneLink Y h) (hcov : h = -Y.l) (hunit : h = 1) :
    Y = Hypercharge.standard ∧ Y.n = 0 := by
  subst hunit
  exact ReferenceLink.neutral_from_reference Y hf hl (by linarith)

/-- **Strict inequality selects θ̄ = 0.** -/
theorem strict_selects_zero (E : ℝ → ℝ) (hVW : ∀ θ ∈ Set.Ioc (-Real.pi) Real.pi, θ ≠ 0 → E 0 < E θ)
    (θ : ℝ) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hmin : ∀ φ ∈ Set.Ioc (-Real.pi) Real.pi, E θ ≤ E φ) : θ = 0 := by
  by_contra hne
  have h0 : (0 : ℝ) ∈ Set.Ioc (-Real.pi) Real.pi := ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
  linarith [hVW θ hθ hne, hmin 0 h0]

lemma Z_re (S : Finset ℤ) (w : ℤ → ℝ) (θ : ℝ) :
    (HermitianMass.Z S w θ).re = ∑ n ∈ S, w n * Real.cos (n * θ) := by
  unfold HermitianMass.Z
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **The positive transfer weights give the strict inequality on the whole circle.** With the unit
winding sector weighted, every `θ ≠ 0` in `(-π, π]` has `Re Z(θ) < Z(0)`. -/
theorem strict_vafa_witten (S : Finset ℤ) (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n) (h1 : (1 : ℤ) ∈ S)
    (hpos : 0 < w 1) (θ : ℝ) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (hne : θ ≠ 0) :
    (HermitianMass.Z S w θ).re < ∑ n ∈ S, w n := by
  rw [Z_re]
  apply Finset.sum_lt_sum
  · intro n _; nlinarith [hw n, Real.cos_le_one (n * θ)]
  · refine ⟨1, h1, ?_⟩
    have hc : Real.cos θ < 1 := by
      refine lt_of_le_of_ne (Real.cos_le_one θ) (fun h => ?_)
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff θ).mp h
      have hpi := Real.pi_pos
      obtain ⟨h1, h2⟩ := hθ
      have hk1 : (k : ℝ) < 1 := by
        by_contra hc; push Not at hc; nlinarith
      have hk2 : (-1 : ℝ) < k := by
        by_contra hc; push Not at hc; nlinarith
      have : k = 0 := by
        have a : k < 1 := by exact_mod_cast hk1
        have b : -1 < k := by exact_mod_cast hk2
        omega
      subst this; simp at hk; exact hne hk.symm
    simpa using (mul_lt_mul_of_pos_left hc hpos)

/-- **`Re Z` is not `|Z|`.** Unit weights on the windings `{-1, 1}` satisfy the premises of
`strict_vafa_witten`, yet `‖Z(π)‖ = Z(0)`: the modulus does not single out `θ = 0`. Uniqueness of
the physical vacuum needs the cost to be read from `Re Z`, or stronger support assumptions. -/
theorem abs_not_unique :
    ‖HermitianMass.Z {-1, 1} (fun _ => 1) Real.pi‖ =
      ∑ n ∈ ({-1, 1} : Finset ℤ), (fun _ : ℤ => (1 : ℝ)) n := by
  rw [HermitianMass.Z_pi]
  norm_num [Finset.sum_pair (show (-1 : ℤ) ≠ 1 by norm_num)]

/-- **A reversible closed update cannot restore every state to one.** If `f` is injective and
some iterate sends every state to `p`, the state space has one element. Exact restoration of a
displaced reference therefore needs records or an environment outside the restored subsystem;
`finite_restorer_exact` applies to that open map; its link to the linear restorer is
`PMAction.FiniteRestorationBridge.finite_restoration_gain_trace` (given the encoding law). -/
theorem reversible_cannot_collapse {S : Type*} (f : S → S) (hf : Function.Injective f) (p : S)
    (N : ℕ) (hN : ∀ x, f^[N] x = p) (x y : S) : x = y :=
  (hf.iterate N) ((hN x).trans (hN y).symm)

/-- **One repair.** -/
theorem one_repair : IsLeast {k : ℕ | 0 < k} 1 :=
  ⟨Nat.one_pos, fun _ hk => hk⟩

/-- **A repeated label lowers every label's maximin gain.** -/
theorem repeat_lowers_margin {B s : ℝ} (hs : s < B) (N : ℕ) (hN : 0 < N) :
    (B - s) / (N + 1) < (B - s) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  exact div_lt_div_of_pos_left (by linarith) hN' (by linarith)

end PMConstants.PersistenceClosures
