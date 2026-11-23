# PMAtoms — open work

Repo-wide named premises are listed once in [SCOPE](../../SCOPE.md#named-premises).

**Open.** The bulk: with both isospin terms present the stable-line masses are `≈ 110 m_e`
heavy on average, because `certifiedMass`'s bulk terms (and the alpha-cluster binding) already
carry the average symmetry cost along the line. A full-chart ledger needs the bulk re-derived
with the isospin terms present; the occupancy ledger's symmetric filling energy has no E8 link
potential to pair with (`IsospinLedger` docstring). Until then the valley (which `(Z, N)` are
stable, `NuclearRegime`/`PersistenceSelection`) is a comparison, not a result.

- Derive the universal alpha width. The current E8 width is frontier-local: the `(43/8)Z/√Q−84`
  cost leaves U-235 as the outlier, and the `cKf` absolute scale is about `10¹⁵` too long. The
  missing input is a Q-dependent preformation or a regime-dependent barrier coefficient. Compare
  in `OVERVIEW.md` §Comparison.
- Derive the odd-A alpha hindrance scale. The two-level mixing `σχ/(χ·gap+1)` fixes U-235 and
  Pu-239, but the Nilsson level scheme and the scale are candidates.
- Derive the fragment overlap for α/fission hindrance, using the composite configuration required
  by `PMHadrons.Emission`. Compare the odd-A α cases in `OVERVIEW.md` §Comparison.
- Derive the fragment-resolved fission barrier and collective inertia. The one-shot yield scale
  `Δ²/(D+σ)` is a candidate, not a universal law; the superheavy No/Rf entries need a nonlinear
  barrier.
- Derive `β·c0` for the finite spectral beta fraction. The fraction is not a lifetime.
- Derive a channel rule for the `41/43` phase margin, and test the E8 tick on a second
  clock-sensitive decay.
- Replace the amplitude ledger with species-specific spinors.
- Derive the charge coefficient from the uncalibrated lattice Green function. The mirror data
  give `k ≈ 1.30 m_e`; the present `c·3/5 = 0.754` is too small, and `c = πD/(2σ) = 1.257` is
  within 3.5%.
- Re-derive or remove the typed `σ/ν` asymmetry. The `A ≥ 11` mirror data do not support it; a
  two-parameter fit gives it a negative coefficient.
- Derive the residual offset left after whole alpha closures: `≈ −5 m_e` for `A < 70` and
  `≈ −12 m_e` for Sn–Pb. Candidates: the linear isospin suppression of alphas, and the
  identified weights. Derive, do not fit.
- Derive screening and the electron fill order used by the atomic configurations.
- Keep continuum comparisons until each E8 replacement has a numerical counterpart. Mark
  candidate modules experimental and keep the measured residuals in `OVERVIEW.md` §Comparison.
- Choose the alpha-attempt clock convention (capacity vs nested).
