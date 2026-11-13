# OPEN-PROBLEMS

What a reader checking this library should know is **not** derived. The Lean tree is the
ground truth for what is checked; [`SCOPE.md`](SCOPE.md) says what is claimed. The working
lists, with module-level detail, are each folder's `src/*/REVIEW-AND-NEXT.md`.

## 1. Premises (stated, not derived)

| Premise | Where | Note |
| --- | --- | --- |
| **Postulate L — the address lattice**: additive discrete addresses with an integral quadratic cost, finitely generated | `PMSubstrate/Address.lean` | Finite generation is a real extra premise: `Address.DInf_not_finite` gives an infinite-rank lattice that meets every other condition. |
| **The vacuum uses E8's clock, sectors and costs** | `PMSubstrate` (`Clock`, `Sectors`, `NetCost`) | Given the postulates, `Δ = 43, ν = 16, σ = 5, χ = 2` are forced (`persistence_selects`); `VacuumIndependence` shows each postulate is needed. |
| **The physical readout is the coordinate observation** | `PMAction.Machine.CarrierClassBundle`, `CarrierParity` | The readout itself is constructed and its squared form is derived (`PMAction.ReadoutRule.born`); identifying it with what an apparatus records is the admission. |
| **Strong CP: the vacuum phase is selected by least cost; the chiral anomaly is imported** | `PMConstants/ThetaBarSelection.lean`, `WindingWeights.lean` | With these, `θ̄ = 0` for any quark masses. The anomaly relation (index theorem), Lüscher's lattice charge on PM's region and a charge-1 history are cited, not formalised. In the Standard Model this is the axion's job. |
| **Lorentzian signature, origin of ℂ** | `SCOPE.md` | Signature is stated as "volume element squares to −1" (`Derived.SignaturePostulate`). |

## 2. Inputs (not selectable by any cost)

A continuous magnitude or unit cannot be the unique minimizer of a scale-invariant cost
(`SelectionSymmetry.scale_no_unique_min`), so these are anchors by proof, not by omission.

* **Dimensionful anchors:** `m_e`, the SI tick (`E8TickUnit`), the absolute wall-mass scale, the
  `α_G` normalization, the Planck scale, the toll unit `c₀`.
* **Continuous choices:** the CP-sign branch (`conjugate_cost_tie`), the flavour wall magnitude `δ`.
* **Discrete readings with no cost functional yet:** which invariant pays which lepton/quark tier
  cost (`LeptonMasses`, `QuarkMasses`); the dark-matter ratio reading `31/6` vs `25/6`
  (`PMCosmology.Scaling`); the Aufbau fill order (`PMAtoms`); nuclear shell, α and pairing labels.
  Supplying a cost for any of these would turn it into a derivation.

## 3. Open physics (where the numbers do not yet follow)

| Problem | Status | Detail |
| --- | --- | --- |
| **Neutron lifetime** | E8 gives 923.4 s on the continuum route (the emitted electron is not confined; see `src/PMElementaryParticles/CONTINUOUS.md`), +5.1% vs 878.4 s. The phase space, Coulomb factor and short-distance running are derived; the electron's low-energy QED (computed, not yet in Lean) gives 909.2 s, +3.5%. E8's `g_A = 5/4` matches lattice QCD (1.246(28)); the 2% to the measured 1.2754 is the size of the known electromagnetic correction to `g_A` (1.4–2.6%), which gives 871–889 s on this route. Open: that correction from the substrate. | `PMHadrons/REVIEW-AND-NEXT.md` §0, §2 |
| ↳ `g_A` | E8's `5/4` matches lattice QCD. On the substrate: carrier resolved inside the 3-cell hadron volume, centre-of-mass projected (`≈ 1.34`), with a source-confined pion cloud (`−5` to `−8%`) gives `≈ 1.24–1.28`, no fitted parameter; the cloud is still computed with the coarse carrier, and the Toll rule for a returning pion pair is open. Resonances (Δ) are out of scope: documented as hosted transients. | `PMHadrons/PILLARS.md`, `PMAction/REVIEW-AND-NEXT.md` A.3 |
| **`f_K` and the K/π ratio** | `f_K` −3.8σ, K/π −5.6σ (one gap). The pion's emission count `1890` is a defined set; no premise yet says how the kaon's strange carrier restricts it. | `PMHadrons/REVIEW-AND-NEXT.md` §3 |
| **Heavy nuclei** | Actinide deformation scatters ±0.019 u; heavy charge-radius scaling and the deformed proton closure `2(Δ+σ) = 96` are candidates. | `PMAtoms/REVIEW-AND-NEXT.md` |
| **Cosmology** | Background evolution, primordial source, baryon-changing event, metric/causal structure and entropy normalization are not constructed. | `PMCosmology/REVIEW-AND-NEXT.md` |

## 4. Out of scope

| Item | Note |
| --- | --- |
| General quantum Yang–Mills (infinite volume, continuum limit, mass gap) | Finite-volume OS core is built; see `PMAction/OVERVIEW.md` and `PMAction/MassGap/README.md`. |
| Full gravity (metric, Einstein equations, diffeomorphisms) | Weak field only. |
| Inflation / primordial spectrum | Source left free (`Modes.amplitude_free`, `power_free`). |
| Grand unification, hierarchy/naturalness, CPT | Not addressed beyond a value. |
