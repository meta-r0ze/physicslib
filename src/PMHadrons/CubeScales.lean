import PMHadrons.NeutronPrediction

/-!
# Two `3×3×3` cubes: the carrier cube and the lepton cube

Two readings use `MinimalCube`'s `3×3×3` cube:

* the **lepton (final-state) cube** of the neutron's spectral channel (`NeutronPrediction`):
  Dirichlet Laplacian eigenvalues read in units of `m_e`, with at least one mode below the endpoint
  `m_n − m_p` (`neutron_openModes`);
* the **carrier cube** of the confined light carrier (`PMAction.ConfinedCarrier`): a Dirac walk,
  whose energy unit is `ħc/a`, and whose lowest mode's rms radius (`ρ = 1.354` sites, numerical,
  `tools/confined_walk.py`) is the proton's charge radius, E8 `r_p = Dħ/(m_p c)`
  (`CompositeMasses.protonRadius_value`).

**They cannot share one spacing.** In units `ħ = c = m_e = 1`:

* `single_unit_rms_bound`: if one unit `u` served both, the decay channel being open forces
  `u ≤ (m_n − m_p)/λ_min < 1.45`, and then `r_p = ρ/u` forces `ρ < 0.0032` sites: the carrier would
  have to sit almost entirely on the centre site. The confined carrier's `ρ` is `1.354`.
* `two_units`: for any carrier mode with `ρ ≥ 1`, the carrier unit exceeds the lepton unit by more
  than a factor `300` (numerically `≈ 430`: `318 MeV` against `≤ 0.74 MeV`).

Both inputs are E8 values (the masses `m_n`, `m_p` and the radius `D/m_p`), so this is forced by
the substrate's own numbers, not by a modelling choice.

**Reading (Persistence Mechanics).** `MinimalCube` is a statement about any persistent volume:
the smallest cube with an interior vertex. Each persistent system has its own minimal cube,
measured in its own scale, as each level of the system tower carries its own budget
(`PMAtoms.SystemTower`). The nucleon's carriers live on the nucleon's cube (`a ≈ 0.62 fm`). The
emitted electron is not one of the nucleon's resources: it leaves through the Toll boundary
(`TollGovernor`), and its modes are those of its own minimal cube at its own scale `m_e`.

**Consequence: the lepton cube's spacing, and the Coulomb `κ`.** The channel reads Laplacian
eigenvalues (the non-relativistic kinetic operator of a mass-`m_e` particle) in units of `m_e`, so
the hop `ħ²/(2 m_e a²)` equals `m_e`: `a_e = ħ/(√2 m_e c)` (`lepton_hop`). This is the
non-relativistic link `κ = 4π√2` of `PMHadrons/REVIEW-AND-NEXT.md` §0.2, now forced by the channel's
own definition rather than chosen.
-/

noncomputable section
namespace PMHadrons.CubeScales
open PMElementaryParticles

/-- The lowest Dirichlet eigenvalue of the `3×3×3` cube exceeds `1.75`. -/
theorem lambda_min_gt : (1.75 : ℝ) < dirichletEigenvalue 3 1 1 1 := by
  rw [neutron_low_eigenvalue_eq]
  have h : Real.sqrt 2 < 1.415 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

/-- The neutron endpoint `m_n − m_p` is below `2.531 m_e`. -/
theorem cutoff_lt : neutronCutoffExact < 2.531 := by
  unfold neutronCutoffExact
  have hn := CompositeMasses.neutron_value
  have hp := CompositeMasses.proton_value
  linarith [hn.2, hp.1]

/-- An open lepton channel bounds its unit: `u < 2.531/1.75 < 1.45`. -/
theorem lepton_unit_lt (u : ℝ) (hu : 0 < u)
    (hopen : dirichletEigenvalue 3 1 1 1 * u ≤ neutronCutoffExact) : u < 2.531 / 1.75 := by
  have h1 : 1.75 * u < dirichletEigenvalue 3 1 1 1 * u := mul_lt_mul_of_pos_right lambda_min_gt hu
  rw [lt_div_iff₀ (by norm_num)]
  linarith [cutoff_lt]

/-- **One shared unit is impossible.** If the same unit `u` (in `m_e`) served the open lepton
channel and the carrier cube (`r_p = ρ/u` with E8 `r_p = 4/m_p`), the carrier's rms radius would be
below `0.0032` sites. -/
theorem single_unit_rms_bound (u ρ : ℝ) (hu : 0 < u)
    (hopen : dirichletEigenvalue 3 1 1 1 * u ≤ neutronCutoffExact)
    (hrad : ρ = u * (4 / CompositeMasses.proton)) : ρ < 0.0032 := by
  have hp := CompositeMasses.proton_value
  have hpos : 0 < CompositeMasses.proton := by linarith [hp.1]
  have h4 : 4 / CompositeMasses.proton < 4 / 1836.15 := by
    rw [div_lt_div_iff₀ hpos (by norm_num)]
    linarith [hp.1]
  have hu' := lepton_unit_lt u hu hopen
  rw [hrad]
  calc u * (4 / CompositeMasses.proton) < (2.531 / 1.75) * (4 / 1836.15) :=
        mul_lt_mul'' hu' h4 hu.le (div_pos (by norm_num) hpos).le
    _ < 0.0032 := by norm_num

/-- **The two units differ by more than 300.** For a carrier mode with rms radius at least one
site, the carrier unit `u_c` (from `r_p = ρ/u_c`) exceeds `300 ×` any open lepton unit `u_l`. -/
theorem two_units (uc ul ρ : ℝ) (hul : 0 < ul) (hρ : 1 ≤ ρ)
    (hrad : ρ = uc * (4 / CompositeMasses.proton))
    (hopen : dirichletEigenvalue 3 1 1 1 * ul ≤ neutronCutoffExact) : 300 * ul < uc := by
  have hp := CompositeMasses.proton_value
  have hpos : 0 < CompositeMasses.proton := by linarith [hp.1]
  have huc : ρ * CompositeMasses.proton = 4 * uc := by
    rw [hrad, mul_assoc, div_mul_cancel₀ (4 : ℝ) hpos.ne', mul_comm]
  have hge : CompositeMasses.proton ≤ ρ * CompositeMasses.proton := by nlinarith [hp.1]
  have hul' := lepton_unit_lt ul hul hopen
  have : (300 : ℝ) * (2.531 / 1.75) < 1836.15 / 4 := by norm_num
  linarith [hp.1]

/-- The lepton cube's spacing `a_e = 1/√2` (in `ħ/(m_e c)`). -/
def leptonSpacing : ℝ := 1 / Real.sqrt 2

theorem leptonSpacing_sq : leptonSpacing ^ 2 = 1 / 2 := by
  unfold leptonSpacing
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **The lepton hop is one `m_e`.** The Laplacian hop `ħ²/(2 m_e a²)` at `a = a_e` equals `m_e`:
the channel's unit fixes its spacing. -/
theorem lepton_hop : 1 / (2 * 1 * leptonSpacing ^ 2) = 1 := by
  rw [leptonSpacing_sq]; norm_num

end PMHadrons.CubeScales
