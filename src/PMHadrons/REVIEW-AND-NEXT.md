# PMHadrons — open work (todo)

Checked results are in [`OVERVIEW.md`](OVERVIEW.md). This file is only open work, in priority
order. Each item says where it stands, what would close it, and its size.

## 1. Meson masses: why these cell counts, and why the nucleons differ

**Status.** Steps 1–2 of the original item are done, and step 2 changed the question.

- The `π⁺` ledger moved from `PMElementaryParticles.LeptonMasses` to `MesonMasses`.
- "Constituents minus a six-pillar budget" does not describe any hadron here. With the
  current-quark ledger every hadron is far heavier than its quarks (`pionPlus_gt_constituents`,
  `kaonPlus_gt_constituents`, `proton_gt_constituents`), so the binding would be negative. The
  nucleon formula never used constituents either; its base is `Δ²`.
- The mesons are already six-pillar ledgers. `α⁻¹` is, by definition, one substrate cell's
  six-pillar budget (`cellBudget_pillars`), and its Toll and Margin terms are the nucleons'
  `Z_TOL` and `Z_MAR` (`tollTerm_eq_zTol`, `marginTerm_eq_zMar`). Each meson is
  `n · cellBudget + residual`, with `n = χ` for pions and `n = σ+χ` for kaons
  (`pion0_cells` … `kaonPlus_cells`). The `OVERVIEW.md` pillar audit is corrected.
- The cell counts and residuals are recorded as model inputs (`MesonMasses` docstring). The
  charge load `α(σ−χ)/χ` is shared by both charged mesons.

**Open.**

1. Why `n = χ` for the pions (plausibly one cell per constituent) and `n = σ+χ = 7` for the
   kaons (not a constituent count). A rule that gives both would turn `n` from an input into a
   result.
2. The nucleons and mesons use two bases: `Δ²` for the nucleons, whole cell budgets for the
   mesons (`m_p/α⁻¹ ≈ 13.4` is not a whole number). One form covering both, or a reason they
   differ, would unify the level.

**Size.** Research. If neither question yields a rule, stop here: the inputs are already listed.

## 2. The kaon decay constant `fK`

**Status.** The rest of the old item is done.

- `|V_us|` was `s₁₂c₂₃`, which is not an entry of the repo's own CKM matrix. It is now
  `s₁₂c₁₃`, the `(u,s)` entry of `PMFlavor.CKM.ckm` (`vusE8_eq_ckm`). The two differ by 0.08%;
  the enclosure `0.2242 < |V_us| < 0.2245` and everything downstream are unchanged.
- The `π⁰ → γγ` anomaly coefficient is computed, not taken from the textbook:
  `A = N_c(Q_u² − Q_d²) = 3·(4/9 − 1/9) = 1`, with the colour count from the three colour axes
  and the charges from Paper V's protocols (`anomalyCoefficient_eq_one`). The `1/(32π³)`
  triangle-loop normalization stays a model input.

What is left is `fK = v/(Δ²−ν²) = v/1593`. It is an assigned formula, and it is the weakest
number at this level: `fK ≈ 154.56 MeV` against the FLAG 2024 lattice average `155.7(3) MeV`
(about `3.8σ` low), and `fK/fπ = 1890/1593 ≈ 1.1864` against `1.1932(19)` (about `3.6σ`).
`fπ = v/(Δ²+Δ−χ)` itself agrees (`130.27` vs `130.2(8)` MeV). The low `fK` makes the width about 1.5% small, which is
over half of the E8 kaon lifetime's 2.6% excess. The tree-level formula has no radiative
correction, so the remainder is not yet accounted for either way.

**To close.** Give `fK` and `fπ` one shared rule (they have different denominator shapes,
`Δ²−ν²` and `Δ²+Δ−χ`) that also lands inside the lattice band, or keep `fK` as a model input
and add its pull to `e8p` so the tension is visible. Do not search integer combinations for
a better fit: that is how these formulas acquire their look-elsewhere problem.

**Size.** Small to record; open-ended to derive.

## 3. Hadronic matrix elements (blocked kaon channels)

**Status.** `ParticleChannels` marks four kaon modes as blocked. They split into two kinds:

- **Nonleptonic** `K⁺ → π⁺π⁰`, `π⁺π⁺π⁻`. The amplitude `⟨ππ|T|K⁺⟩` is genuinely
  nonperturbative (in standard physics too: the `ΔI = 1/2` rule). The structure is built
  (`CompositeTransition`, `CompositePhaseSpace`, `HadronicMatrixElement`, `BoundStateOverlap`);
  the bound-state amplitude is supplied (`BoundStateMatrixElement.value`).
- **Semileptonic** `K⁺ → π⁰e⁺ν`, `π⁰μ⁺ν` (`K_ℓ3`). These are not blocked by a wavefunction
  at leading order. The only hadronic input is the vector form factor `f₊(t)`. Its value at
  `t = 0` is `1` in the flavour-symmetric limit, by vector-current conservation; the corrections
  start at second order in the `s`–`u` mass difference (Ademollo–Gatto).
  - With `f₊ = 1` and `m_e → 0`, the width is `G_F²|V_us|² m_K⁵ · ½ · f(m_π²/m_K²)/(4·192π³)`.
    Here `f` is the muon-decay phase-space function: the `λ^{3/2}` Dalitz integral equals
    `f/4` exactly. Every factor is already E8 in this repo.
  - A side check (not in Lean) puts that leading-order number about 10% under the measured
    `K_e3` rate. The gap is the known corrections: `f₊(0) ≈ 0.97`, the `t`-slope (`+7%`),
    short-distance electroweak and isospin corrections (`+5%`). The first two are the same
    nonperturbative physics as the nonleptonic modes. A `K_ℓ3` channel would therefore be
    marked "E8 leading order, ~10%", far weaker than the 0.1σ masses.

**To close.**

- Nonleptonic: a substrate bound-state wavefunction for the constituent cohorts, so the
  overlap in `BoundStateOverlap` is computed rather than supplied.
- Semileptonic: optionally add `K_ℓ3` at leading order with that label, reusing the muon-decay
  `f`. It is only worth adding if a 10%-level entry does not dilute the channel table.

**Size.** Nonleptonic: large and nonperturbative. Leave blocked; item 1 does not yet give
wavefunctions, only mass ledgers. Semileptonic leading order: small.

## 4. Continuum neutron width (comparison only)

**Status.** The headline neutron lifetime is the finite E8 channel, `877.2 s` vs `878 s`
(`NeutronPrediction`). The continuum comparison `NeutronRate` (massive-electron phase space,
`g_A = σ/D = 5/4`) gives `≈ 9.8×10² s`, about 11% high; with the recoil endpoint and a
supplied 4% radiative factor it gives `≈ 9.4×10² s`.

**To close.** The full angular Dalitz density and a derived radiative correction. Not needed for
the E8 result.

**Size.** Optional. Keep as a cross-check, or retire it once the E8 route is the only one cited.
