import PMFlavor.LinkKronComparison
import PMKAutomaton.Interface

/-!
# Where a CP phase can sit on the incidence network: one flux per sector

`MassMixing.positive_masses_allow_any_mixing`: the structural constraints fix moduli, not phases.
`LinkKronComparison`: the quark link is the Kron reduction of the generation–class incidence
network (a hexagon: three generation and three class vertices, two legs per class). This module
puts phases on the legs and finds what survives the reduction.

**Reduction with complex legs.** A class vertex with legs `t₁, t₂` (conductances `g₁ = |t₁|`,
`g₂ = |t₂|`) is eliminated exactly as in `KronSeries`; the reduced coupling is
`kronC t₁ t₂ = −t₁ t̄₂ / (g₁ + g₂)` (`kronC_real`: for real legs it is `PMAction.KronReduction.kron_two`).
A phase on a class vertex cancels; a phase on a generation vertex is a basis rephasing. On the
hexagon this leaves one invariant per sector, the **flux** `(−Y₀₁)(−Y₁₂)(−Y₂₀)` (the reduced
triangle's product of couplings). The CKM phase can only come from fluxes.

**A wall-side leg phase.** `PMAction.GenerationWalls.side` puts each leg of a generation on one
of the two walls: around the hexagon the legs alternate walls. If a leg's phase depends only on
its wall (`legA`: `u` on one wall, `ū` on the other, moduli free):
* `flux_cyclic`: the flux is a positive real times `ū⁶`. Each reduced coupling joins a leg on one
  wall to a leg on the other, so every one of the six legs contributes the same `ū`.
* `wall_swap_conj`, `flux_swapped`: exchanging the wall names (the other balanced convention of
  `GenerationWalls`) conjugates every leg, so the flux becomes `u⁶` and `J → −J`.
* `swap_reverses_orientation`: the `μ`–`τ` swap (`1 ↔ 2` on generations and classes) maps every
  leg to the other wall (the `v = 0` case of `ExchangeChirality.swap_reverses_side`). So a phase pattern invariant under the residual `Z₂` of
  `GenerationBreaking` has flux equal to its conjugate, a real flux, and conserves CP.

So: CP violation needs the incidence orientation, i.e. the `Z₂` broken by which wall is which;
its **sign** is the wall-naming convention (the `sin δ` branch the library calls a
substrate-orientation input, `ReferenceFlavour.column2_difference_conj`), and its **size** is
`6θ` for a wall-side leg phase `θ` (flux real iff `θ ∈ (π/6)ℤ`). No substrate input fixing `θ`
is in the library.

**The real network shares its zero mode.** `kronLink_zero_mode`: every real-leg reduced link
annihilates `(1, 1, 1)`, whatever the legs. Two sectors on real legs therefore share that state;
it is the heaviest state: `σ = 0` is outside `WallSeesaw`'s `Y⁻¹`, but the exact one-flavour light branch
`(√(y² + 4δ²) − y)/2` (`PMAction.WallSeesaw.light_heavy`, `PMAction.WallDispersion`) decreases in `y`
and is largest, `δ`, at `y = 0`; naming it the third generation assumes the zero mode is
nondegenerate and the generation labels follow the mass order, and it does not mix with the others.
So the third-generation CKM entries (`|V_ub|`, `|V_cb|`, `|V_td|`, `|V_ts|`) need something that
lifts the zero mode differently in the two sectors: a flux or a non-conserving leak. Numerically
(outside Lean) a common wall-side `θ` with different leg moduli does this and gives `J ≠ 0`; with
uniform moduli in each sector `J = 0`.
-/

noncomputable section
namespace PMFlavor.LinkFlux
open Matrix ComplexConjugate LinkKronComparison
open PMAction.GenerationWalls (side)

/-- The reduced coupling of two generations through a class vertex with legs `t₁, t₂` of
conductances `g₁, g₂` (the vertex's own conductance is `g₁ + g₂`). -/
def kronC (t₁ t₂ : ℂ) (g₁ g₂ : ℝ) : ℂ := -(t₁ * conj t₂) / ((g₁ : ℂ) + g₂)

/-- For real positive legs this is minus the series admittance `g₁g₂/(g₁ + g₂)`, the value of
`PMAction.KronReduction.kron_two`. -/
theorem kronC_real (g₁ g₂ : ℝ) :
    kronC g₁ g₂ g₁ g₂ = ((-(g₁ * g₂ / (g₁ + g₂)) : ℝ) : ℂ) := by
  simp only [kronC, Complex.conj_ofReal]
  push_cast
  ring

/-- A phase on the class vertex cancels from the reduced coupling. -/
theorem class_phase_cancels (t₁ t₂ w : ℂ) (hw : w * conj w = 1) (g₁ g₂ : ℝ) :
    kronC (t₁ * w) (t₂ * w) g₁ g₂ = kronC t₁ t₂ g₁ g₂ := by
  simp only [kronC, map_mul]
  rw [show t₁ * w * (conj t₂ * conj w) = t₁ * conj t₂ * (w * conj w) by ring, hw, mul_one]

/-! ## Legs with a wall-side phase -/

/-- Leg from generation `i` to class `j`: modulus `m i j`, phase `u` on the wall `side i j`
names, `ū` on the other. -/
def legA (m : Fin 3 → Fin 3 → ℝ) (u : ℂ) (i j : Fin 3) : ℂ :=
  if side i j then (m i j : ℂ) * u else (m i j : ℂ) * conj u

/-- Reduced coupling between generations `i, k` through their shared class `j`. -/
def redY (m : Fin 3 → Fin 3 → ℝ) (u : ℂ) (i k j : Fin 3) : ℂ :=
  kronC (legA m u i j) (legA m u k j) (m i j) (m k j)

section legs
variable (m : Fin 3 → Fin 3 → ℝ) (u : ℂ)
theorem l01 : legA m u 0 1 = (m 0 1 : ℂ) * u := by
  have h : side 0 1 = true := by decide
  simp [legA, h]
theorem l02 : legA m u 0 2 = (m 0 2 : ℂ) * conj u := by
  have h : side 0 2 = false := by decide
  simp [legA, h]
theorem l10 : legA m u 1 0 = (m 1 0 : ℂ) * conj u := by
  have h : side 1 0 = false := by decide
  simp [legA, h]
theorem l12 : legA m u 1 2 = (m 1 2 : ℂ) * u := by
  have h : side 1 2 = true := by decide
  simp [legA, h]
theorem l20 : legA m u 2 0 = (m 2 0 : ℂ) * u := by
  have h : side 2 0 = true := by decide
  simp [legA, h]
theorem l21 : legA m u 2 1 = (m 2 1 : ℂ) * conj u := by
  have h : side 2 1 = false := by decide
  simp [legA, h]
end legs

/-- **The flux of a wall-side phase is `ū⁶`** times a positive real: each reduced coupling joins
a leg on one wall to a leg on the other, so all six legs contribute `ū`. -/
theorem flux_cyclic (m : Fin 3 → Fin 3 → ℝ) (u : ℂ) :
    (-redY m u 0 1 2) * (-redY m u 1 2 0) * (-redY m u 2 0 1) =
      ((m 0 2 : ℂ) * m 1 2 / ((m 0 2 : ℂ) + m 1 2)) * ((m 1 0 : ℂ) * m 2 0 / ((m 1 0 : ℂ) + m 2 0)) *
        ((m 2 1 : ℂ) * m 0 1 / ((m 2 1 : ℂ) + m 0 1)) *
        (conj u) ^ 6 := by
  simp only [redY, kronC, l01, l02, l10, l12, l20, l21, map_mul, Complex.conj_ofReal]
  ring

/-- **Exchanging the wall names conjugates every leg.** -/
theorem wall_swap_conj (m : Fin 3 → Fin 3 → ℝ) (u : ℂ) (i j : Fin 3) :
    legA m (conj u) i j = conj (legA m u i j) := by
  unfold legA
  split_ifs <;> simp [map_mul, Complex.conj_ofReal]

/-- With the wall names exchanged the flux is `u⁶`: the conjugate orientation. -/
theorem flux_swapped (m : Fin 3 → Fin 3 → ℝ) (u : ℂ) :
    (-redY m (conj u) 0 1 2) * (-redY m (conj u) 1 2 0) * (-redY m (conj u) 2 0 1) =
      ((m 0 2 : ℂ) * m 1 2 / ((m 0 2 : ℂ) + m 1 2)) * ((m 1 0 : ℂ) * m 2 0 / ((m 1 0 : ℂ) + m 2 0)) *
        ((m 2 1 : ℂ) * m 0 1 / ((m 2 1 : ℂ) + m 0 1)) * u ^ 6 := by
  rw [flux_cyclic, Complex.conj_conj]

/-- **The `μ`–`τ` swap reverses the incidence orientation**: it puts every leg on the other wall.
A phase pattern invariant under it therefore has a real flux. -/
theorem swap_reverses_orientation :
    ∀ g c : Fin 3, g ≠ c →
      side (Equiv.swap 1 2 g) (Equiv.swap 1 2 c) = !side g c := by
  decide

/-! ## The real network's shared zero mode -/

/-- **Every real-leg reduced link annihilates `(1, 1, 1)`**, whatever the legs. -/
theorem kronLink_zero_mode (a b c : ℝ) : kronLink a b c *ᵥ ![1, 1, 1] = 0 := by
  ext i
  fin_cases i <;> simp [kronLink, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- Two real-leg sectors share that state, so it does not mix. -/
theorem shared_zero_mode (a b c a' b' c' : ℝ) :
    kronLink a b c *ᵥ ![1, 1, 1] = 0 ∧ kronLink a' b' c' *ᵥ ![1, 1, 1] = 0 :=
  ⟨kronLink_zero_mode a b c, kronLink_zero_mode a' b' c'⟩

end PMFlavor.LinkFlux
