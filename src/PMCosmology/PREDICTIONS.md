# PMCosmology — answers to the general cosmology questions

A comparison-facing ledger: which standard cosmology observables Persistence
Mechanics has an answer for, the provenance of each, and the measured reference
(from `tools/e8p/E8PConstants/Experimental.lean`). This is comparison material, not
a theorem input and not error bars of the checked tree.

## E8-substrate / geometric answers

| Question | PM answer | Lean source | Measured reference |
| --- | --- | --- | --- |
| `Ω_DM/Ω_b` | `31/6 = 5.1667` | `Scaling.exact_ratios` (`darkRatio`) | Planck `5.36 ± 0.05` |
| matter–radiation equality `1+z_eq` | `1075π ≈ 3377.212` (geometric proposal) | `Background.z_eq_bounds` | `z_eq ≈ 3400` (Planck) |
| baryon asymmetry `η_B` | `J/(16168π)` → `5.951×10⁻¹⁰` (matrix `pmJ`), `6.073×10⁻¹⁰` (geometric `pm3J`) | `Primordial.baryon_windows` | Planck `(6.12 ± 0.04)×10⁻¹⁰` |
| channel-overhead complement | `31/32 = 0.96875` | `Scaling.scalarIndex` | **not** a spectral tilt — a complement, no direct comparison |

These are testable as-is (a measured `Ω_DM/Ω_b ≠ 31/6`, or `z_eq` far from `1075π`,
would refute the proposal). `z_eq` is a geometric *proposal*, not a derivation.

## Conditional rescalings (frozen inputs × constitutive response)

| Question | PM answer | Inputs | Measured reference |
| --- | --- | --- | --- |
| H₀ (late) | `67.4·L = 502467/6880 ≈ 73.033` | frozen `67.4`; load `L = 1491/1376` | SH0ES `73.0 ± 1.0`; Planck `67.4 ± 0.5`; DES `67.4 ± 0.5` |
| S₈ (late) | `0.832/L = 143104/186375 ≈ 0.767828` | frozen `0.832`; `L` | DES `0.776 ± 0.017`; KiDS `0.759 ± 0.024`; Planck `0.832 ± 0.013` |

`H_late`/`S8_late` are rescalings of frozen draft inputs by the constitutive load,
**not** first-principles derivations; `Scaling.joint_rescaling_invariant` makes them
one constraint, not two. They land on the SH0ES/DES side of the H₀/S₈ tensions.

## Not defined — would need new postulates, not a catalog row

`Ω_b h²`, `Ω_c h²`, `Ω_Λ`, `A_s`, `N_eff`, `Y_p`, `D/H`, recombination `z_*`, the
age, the growth factor, the full `P(k)`, the metric/horizon, and absolute Hubble
units. Papers I–VI define no Lean densities, amplitudes or expansion history for
these; adding them means new model postulates (see `REVIEW-AND-NEXT.md` Part B).

## How to use

`e8p --audit` reports the σ of each catalogued value against these references. The
first block is E8/geometric output, the second is conditional, the third is the
honest open frontier.
