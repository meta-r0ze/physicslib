# Open problems

This index collects the assumptions and unresolved constructions that affect how the library's results can be interpreted. Each linked folder review tracks the corresponding work. [Project scope](SCOPE.md)

## Foundations and calibration

| Question | What remains open |
| --- | --- |
| Why an E8 substrate? | Derive the finitely generated address lattice and integral quadratic cost, justify the theta symmetries and rank selection, and identify the clock, sectors and costs with the physical vacuum. Finite generation matters: `Address.DInf_not_finite` supplies a counterexample when it is dropped. [Substrate review](src/PMSubstrate/REVIEW-AND-NEXT.md) |
| What does an apparatus record? | Identify the constructed coordinate observation with a physical readout and allocate the reference and record banks. The squared readout rule is already proved for the model. [Action review](src/PMAction/REVIEW-AND-NEXT.md) · [Machine review](src/PMAction/Machine/REVIEW-AND-NEXT.md) |
| Which scales and orientations must be supplied? | Dimensionful readouts require unit anchors, including the electron mass and SI tick. A scale-invariant cost cannot single out a scale along a nontrivial rescaling orbit. For flavour, a cost depending only on squared mixing moduli ties the conjugate CP branches. The wall magnitude and the functional forms of the mixing relations have separate selection problems. [Selection symmetries](src/PersistenceMechanics/SelectionSymmetry.lean) · [Flavour review](src/PMFlavor/REVIEW-AND-NEXT.md) |
| What selects the physical constants? | The VEV correction factors, gravitational handoff interpretation and integrated polarization remainder remain open. Strong-CP selection uses the anomaly relation and least-cost selection among candidate vacua. The unit-transfer history has an external numerical certificate; its Lean verification remains open. [Constants review](src/PMConstants/REVIEW-AND-NEXT.md) |
| What selects the spacetime and amplitude structures? | Lorentzian signature and complex amplitudes enter as modelling premises. The finite gauge measure has site-reflection positivity; a continuum relativistic gauge theory and its mass gap are outside the present construction. [Scope](SCOPE.md) · [Gauge-layer scope](src/PMAction/MassGap/README.md) |

## Observable consequences

| Observable | What would advance it |
| --- | --- |
| Elementary masses and widths | Derive the assignment of invariant costs to lepton and quark tiers, the allowed transition histories and their rates. Connect the charged-current operator to the physical contact vertex and final-state readout. [Elementary-particle review](src/PMElementaryParticles/REVIEW-AND-NEXT.md) |
| Nucleon axial charge and magnetic moments | Compute pion dressing, recoil and intrinsic currents on the same finely resolved, centre-of-mass-projected carrier state. The quoted axial range 1.24–1.28 combines a refined core with a coarse-source correction. The local axial variation, the Toll for a returning pair and the cube-scale colour coupling remain open. [Hadron review](src/PMHadrons/REVIEW-AND-NEXT.md) · [Calculation and premises](src/PMHadrons/PILLARS.md) |
| Neutron lifetime | Lean bounds the continuum lifetime with the leading Fermi correction at 923.37–923.39 s. The external interval calculation includes further corrections; its 871–889 s range uses a supplied electromagnetic axial shift. Derive that shift from the substrate. Lean verification of the full Fermi and outer-radiative integrals is a separate task. [Continuum theorem](src/PMHadrons/NeutronContinuum.lean) · [Interval calculation](tools/neutron_rc_certificate.py) |
| Pion and kaon emission | Derive the meson channel factor 32/33 and explain why kaon routing uses all ν channels and occupies the surviving exits. The proposed routing reproduces the assigned kaon count of 1593; the resulting decay-constant ratio is about 0.6% below the comparison in the hadron ledger. [Hadron pillars](src/PMHadrons/PILLARS.md) |
| Nuclear masses and atomic structure | Re-derive nuclear bulk binding with both isospin terms present, avoiding double counting along the stable line. Fragment overlaps, finite-size charge scaling, electron screening and fill order also need physical inputs. [Atoms review](src/PMAtoms/REVIEW-AND-NEXT.md) |
| Cosmic composition and expansion | Determine which substrate sectors carry dark and baryonic density and how their occupations and energies weight the count. The baryon fractions inherit this identification. The retained-history bound assumes recoverability; explaining expansion requires a source of such records and a reason added capacity takes the form of spatial cells. Background evolution, the primordial source, baryon-changing dynamics, metric and entropy normalization remain open. [Cosmology review](src/PMCosmology/REVIEW-AND-NEXT.md) · [Prediction ledger](src/PMCosmology/PREDICTIONS.md) |

Full gravity, inflationary dynamics, grand unification, hierarchy and naturalness, and CPT are covered in the [project scope map](SCOPE.md).
