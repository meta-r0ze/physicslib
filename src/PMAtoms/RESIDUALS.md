# Certified-ledger residuals

Comparison data only. These values are not theorem inputs. Residual is
`certifiedMass(Z,N) − m_iso` in atomic mass units.

The certified ledger is valid through the deformed frontier `Z=96, N=152`.
Post-frontier entries are marked separately.

| nucleus | Z | N | residual (u) | regime |
| --- | --- | --- | --- | --- |
| He-4 | 2 | 2 | −0.00014 | light |
| C-12 | 6 | 6 | +0.00076 | light |
| O-16 | 8 | 8 | −0.00018 | light |
| Ne-20 | 10 | 10 | −0.00414 | light |
| Mg-24 | 12 | 12 | −0.00335 | light |
| Si-28 | 14 | 14 | −0.00185 | light |
| S-32 | 16 | 16 | −0.00355 | light |
| Ar-36 | 18 | 18 | −0.00544 | light |
| Ar-40 | 18 | 22 | −0.00406 | light |
| Ca-40 | 20 | 20 | −0.00674 | light |
| Ca-44 | 20 | 24 | −0.00332 | light |
| Ca-48 | 20 | 28 | −0.00425 | light |
| Ni-56 | 28 | 28 | −0.00899 | mid |
| Ni-58 | 28 | 30 | −0.00369 | mid |
| Ni-62 | 28 | 34 | +0.00029 | mid |
| Sn-120 | 50 | 70 | −0.00606 | mid |
| Xe-132 | 54 | 78 | −0.00622 | mid |
| Ba-138 | 56 | 82 | −0.00532 | mid |
| Nd-142 | 60 | 82 | −0.00675 | mid |
| W-184 | 74 | 110 | −0.01099 | mid |
| Pb-208 | 82 | 126 | −0.00363 | mid |
| U-238 | 92 | 146 | +0.00246 | deformed |
| Pu-244 | 94 | 150 | +0.00571 | deformed |
| Cm-244 | 96 | 148 | +0.02406 | frontier |
| Cf-252 | 98 | 154 | +0.02234 | **beyond frontier** |

The Cm/Cf entries are boundary data, not certified-ledger fits.

## Structure of the residual (comparison)

**SEMF regression.** Regressing the E8 binding on the Bethe–Weizsäcker basis
`{A, A^(2/3), Z(Z−1)/A^(1/3), (N−Z)²/A, 1}` along the stable line gives volume / surface /
Coulomb / asymmetry `16.2 / 20.0 / 0.73 / 23.7` MeV against the empirical
`15.75 / 17.8 / 0.71 / 23.7`. The residual floor of a scan is `~3.3 m_e ≈ 1.7 MeV`. The
curvature term `A^{1/3}` is collinear with `A, A^{2/3}` and does not lower it
(`3.34 → 3.13 m_e`, cancelling coefficients). A residual regression gives
`R ≈ −12 + 1.2·A^{2/3} − 0.22·A` `m_e` (Q1, below).

**Holographic capacity.** Nuclei are ~38 orders below the hoop bound `Rc²/2G`, and the Bekenstein
entropy bound is `10²–10⁴` nats against `~A` cells, so entropy-holography does not bind nuclei.

**Shell term.** On the 26 frozen nuclides with `12 ≤ A ≤ 208`, `certifiedMass` has residual rms
`4.8 m_e` (mean `−7.9`). The E8 shell term `ℏω(A)·(δE_Z + δE_N)` (`ShellGaps`, Strutinsky with
`γ = 1.2 ℏω`) has rms `14–20 m_e` and correlation `0.03` (`κ = 1/ν`) or `0.37` (`κ = χ/Δ`) with
it; adding it gives `15–22 m_e`. `closureBinding` and `alphaClosureBinding` are bulk terms
(hundreds of `m_e`), not shell terms. The E8 ledger is not a liquid drop plus a shell
correction.

**Stability valley (`IsospinLedger`).** The isobar of lowest `certifiedMass` against the stable
isobar:

| A | E8 (local min within ±15 of stable) | stable Z |
| --- | --- | --- |
| 12, 16, 27, 40 | 6, 8, 13, 20 | same |
| 56 | 28 | 26 |
| 90 | 45 | 40 |
| 107 | 53 | 47 |
| 120 and up | none (mass falls towards neutron-rich isobars) | 50, … |

At Sn-120 the mass is locally maximal in `Z`. The link binding is linear in `N − Z`
(`packingBindingTyped_closed`), Coulomb pushes towards neutrons, and the alpha-cluster term is
the only `N ≈ Z` preference; it is concave in `Z` on the neutron-rich side and switches off at
`|N − Z| ≥ Δ`. The global minimum of each heavy isobar lies at very small `Z` (hundreds of `m_e`
below the stable nucleus). So `certifiedMass` is a ledger along the stable line, not a mass
surface over `(Z, N)`.

**Occupancy symmetry term.** Adding `8.3 MeV·(N−Z)²/A` (separate `p`/`n` filling with `ℏω(A)`,
`IsospinLedger`) gives a minimum for every `A`, at `Z ≈ A/2`: A = 56, 90, 120, 208, 238 → `Z = 28,
45, 60, 104, 119`. Stable-line residual rms `4.8 → 42 m_e`, mean `−7.9 → +19`.

**`valleyMass` (occupancy term replacing the alpha isospin suppression).** Lowest isobar `Z = 18,
24, 37, 47, 82, 92` at `A = 40, 56, 90, 120, 208, 238` (stable `20, 26, 40, 50, 82, 92`).
Stable-line residual mean `+102.5 m_e`, rms `53`. Keeping the alpha term as a plain count
(`min(Z,N)/2`, no suppression) instead gives `Z = 19, 26, 40, 51, 82, 99` but rms `86`.

**Volume/surface split (Q1, closed as a floor).** `packingLinks(A) = (σ−χ)(A − A^{2/3})` is the
cube count, exact at `A = n³` (`packingLinks_cube`), and the closure rank is its cycle rank
`E − A + 1`. Persistence selects the packing with the fewest missing links, i.e. the
edge-isoperimetric optimum on the cubic lattice (quasi-cubes plus an optimal partial layer). That
exact count is `1–2` links below the continuous form between cubes (`A = 208`: `517` vs `518.7`).
Used in place of the continuous form (links and closure rank, no other change) on the 26 stable
nuclides with `12 ≤ A ≤ 208`: mean `|R|` `8.05 → 6.76 m_e`, mean `−7.9 → +5.5`, rms about the
mean `4.84 → 5.76`. So the count's discreteness is not the lever, confirming the earlier crude
test. Volume and surface share one link weight `w = πD(σ−χ)/σ` because both come from the same
link count; the regression's ~5% surface offset would need surface links weighted differently,
and the substrate gives no reason for that. The ledger's floor stays `~3.3 m_e ≈ 1.7 MeV`.

**Spin-persistence potential term (`persistBinding`).** Like links persist in `1` of `4` spin
states, unlike in `4`; normalized to mean `w` at `N = Z` (`8w/5`, `2w/5`). With it and the
occupancy term in place of the alpha-cluster suppression: lowest isobar `Z = 8, 13, 19, 26, 40,
52, 59, 69, 84, 101` at `A = 16, 27, 40, 56, 90, 120, 140, 165, 208, 238` (stable `8, 13, 20, 26,
40, 50, 58, 67, 82, 92`). Stable-line residual mean `+111 m_e`, rms `77`. The potential term
alone (with the alpha binding removed, no occupancy) gives `Z = 17, 22, 34, 43, 76, 85` at
`A = 40, 56, 90, 120, 208, 238`.
