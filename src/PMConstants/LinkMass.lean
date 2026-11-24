import PMConstants.GaugeStiffness
import PMConstants.GaugeSpectrum
import PMConstants.SectorLinks
import PMConstants.CarrierRepresentation

/-!
# W and Z masses from the inter-sector link

The scalar doublet is the link between the two D₄ sectors (`SectorLinks`). Weak links act only
on the left-handed sector, so moving the link field along a direction transports it by
`U = exp(iθ)` with `θ = (g/2)(W₁σ₁ + W₂σ₂ + W₃σ₃) + (g'/2) Y B`. For a link of
fixed length the cost `|(1 − U)φ|²` is, to second order, `|θ φ|²`.

* The link's hypercharge is `Y = 1`, and that is derived, not inserted (`link_charge_one`,
  `thetaY_one`). The right wall differs from the left by the link's own charge
  (`CarrierRepresentation.carrierCharges_yukawa`), and the carrier table with axis tracelessness
  and the forced lepton charge is `Hypercharge.standard`
  (`CarrierRepresentation.carrierCharges_eq_standard`), every one of whose four hops carries
  `|ΔY| = 1` (`SectorLinks.standard_links`).

* `link_quadratic`: for the vacuum direction `φ̂ = (0, 1)`,
  `|θ φ̂|² = (g²/4)(W₁² + W₂²) + (1/4)(gW₃ − g'B)²`. The charged part and the neutral form
  `(gW₃ − g'B)²` assumed in `GaugeSpectrum` are both outputs of the link cost
  (`neutral_from_link`).
* `w_mass_term`, `z_mass_term`: with `⟨φ⟩ = v/√2`, writing `W₁² + W₂² = 2W⁺W⁻` and
  `(gW₃ − g'B)² = (g² + g'²)Z²`, the cost `(v²/2)|θφ̂|²` equals `m_W² W⁺W⁻ + ½ m_Z² Z²` with
  `m_W² = g²v²/4` and `m_Z² = (g² + g'²)v²/4`.
* `photon_free`: the combination `g'W₃ + gB` costs nothing.
-/

noncomputable section
namespace PMConstants.LinkMass
open Matrix

/-! ## The link's own charge

`theta` below is `thetaY` at `Y = 1`. The unit is the carriers' value, not a convention.
-/

/-- **The inter-sector link carries one unit of hypercharge.** -/
theorem link_charge_one : SectorLinks.OneLink Hypercharge.standard 1 := by
  have h : CarrierRepresentation.carrierCharges (1/3) (-1) 1 = Hypercharge.standard :=
    CarrierRepresentation.carrierCharges_eq_standard (1/3) (-1) (by norm_num) (by norm_num)
  rw [SectorLinks.links_iff_yukawa, ← h]
  exact CarrierRepresentation.carrierCharges_yukawa (1/3) (-1) 1

/-- The transport generator with the link's hypercharge `Y` left free. -/
def thetaY (g gp Y W₁ W₂ W₃ B : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((g/2 * W₃ + gp/2 * Y * B : ℝ) : ℂ), ((g/2 : ℝ) : ℂ) * ((W₁ : ℂ) - (W₂ : ℂ) * Complex.I);
     ((g/2 : ℝ) : ℂ) * ((W₁ : ℂ) + (W₂ : ℂ) * Complex.I),
       ((-(g/2) * W₃ + gp/2 * Y * B : ℝ) : ℂ)]

/-- `θ φ̂` for `φ̂ = (0,1)`: upper `(g/2)(W₁ − iW₂)`, lower `−(g/2)W₃ + (g'/2)B`. -/
def thetaPhi (g gp W₁ W₂ W₃ B : ℝ) : Fin 2 → ℂ :=
  ![((g/2 : ℝ) : ℂ) * ((W₁ : ℂ) - (W₂ : ℂ) * Complex.I), ((-(g/2) * W₃ + (gp/2) * B : ℝ) : ℂ)]

/-- The generator `θ = (g/2)(W₁σ₁ + W₂σ₂ + W₃σ₃) + (g'/2) B` on the doublet. -/
def theta (g gp W₁ W₂ W₃ B : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((g/2 * W₃ + gp/2 * B : ℝ) : ℂ), ((g/2 : ℝ) : ℂ) * ((W₁ : ℂ) - (W₂ : ℂ) * Complex.I);
     ((g/2 : ℝ) : ℂ) * ((W₁ : ℂ) + (W₂ : ℂ) * Complex.I), ((-(g/2) * W₃ + gp/2 * B : ℝ) : ℂ)]

/-- **The generator used here is the free one at the carriers' link charge.** -/
theorem thetaY_one (g gp W₁ W₂ W₃ B : ℝ) :
    thetaY g gp 1 W₁ W₂ W₃ B = theta g gp W₁ W₂ W₃ B := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [thetaY, theta] <;> ring

theorem theta_pauli (g gp W₁ W₂ W₃ B : ℝ) :
    theta g gp W₁ W₂ W₃ B =
      ((g/2 * W₁ : ℝ) : ℂ) • !![0, 1; 1, 0] + ((g/2 * W₂ : ℝ) : ℂ) • !![0, -Complex.I; Complex.I, 0] +
      ((g/2 * W₃ : ℝ) : ℂ) • !![1, 0; 0, -1] + ((gp/2 * B : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [theta] <;> ring

theorem theta_on_vacuum (g gp W₁ W₂ W₃ B : ℝ) :
    theta g gp W₁ W₂ W₃ B *ᵥ ![0, 1] = thetaPhi g gp W₁ W₂ W₃ B := by
  ext i; fin_cases i <;> simp [theta, thetaPhi, mulVec, dotProduct, Fin.sum_univ_two]

theorem link_quadratic (g gp W₁ W₂ W₃ B : ℝ) :
    Complex.normSq (thetaPhi g gp W₁ W₂ W₃ B 0) + Complex.normSq (thetaPhi g gp W₁ W₂ W₃ B 1) =
      (g^2/4) * (W₁^2 + W₂^2) + (1/4) * (g*W₃ - gp*B)^2 := by
  simp [thetaPhi, Complex.normSq_apply]
  ring

theorem neutral_from_link (g gp W₃ B : ℝ) :
    (1/4) * (g*W₃ - gp*B)^2 = (1/4) * (![W₃, B] ⬝ᵥ (GaugeSpectrum.neutral g gp *ᵥ ![W₃, B])) := by
  rw [GaugeSpectrum.neutral_quadratic]; simp

theorem w_mass_term (g v Wp Wm W₁ W₂ : ℝ) (h : W₁^2 + W₂^2 = 2 * Wp * Wm) :
    (v^2/2) * ((g^2/4) * (W₁^2 + W₂^2)) = (g^2 * v^2 / 4) * (Wp * Wm) := by
  rw [h]; ring

theorem z_mass_term (g gp v W₃ B Z : ℝ) (h : (g*W₃ - gp*B)^2 = (g^2 + gp^2) * Z^2) :
    (v^2/2) * ((1/4) * (g*W₃ - gp*B)^2) = (1/2) * ((g^2 + gp^2) * v^2 / 4) * Z^2 := by
  rw [h]; ring

theorem photon_free (g gp t : ℝ) :
    g * (gp * t) - gp * (g * t) = 0 := by ring

end PMConstants.LinkMass
