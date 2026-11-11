import PMAtoms.TwoLedger
import PMAtoms.NuclearLedger
import PMAtoms.ShellSystem

/-! **Comparison module.** Not part of `certifiedMass`.

# The isospin dependence of the E8 nuclear ledger

The typed link ledger has a closed form. For `A = Z + N > 4` the mean-field channel counts
`(pp, pn, nn)` weighted by `(w − s, w, w + s)` sum to

  `packingBindingTyped Z N = L(A) · (w + s·(N − Z)/A)`   (`packingBindingTyped_closed`),

with `L(A) = packingLinks A`, `w = πD·(σ−χ)/σ` and `s = σ/ν = 5/16`. So the link binding is
**linear** in the neutron excess `N − Z` at fixed `A`, and favours neutrons: there is no
`(N − Z)²/A` symmetry term in the link ledger. In `certifiedMass` the only terms that prefer
`N ≈ Z` are the Coulomb charge (which pushes the other way, towards neutrons) and the alpha-cluster
term `(Δ/D)·min(Z,N)/2·(1 − |N−Z|/Δ)`, which is piecewise linear in `Z` and switches off at
`|N − Z| ≥ Δ`.

**Symmetry energy, term by term.** The standard model's symmetry energy
`a_sym·(N−Z)²/A`, `a_sym ≈ 23.7` MeV, has a kinetic part (separate proton and neutron Fermi seas)
and a potential part (`pn` binds more than `pp`, `nn`). In the E8 ledger the potential part is
zero (`typed_pn_mean`), and there is no occupancy term: the ledger counts links, not filled
levels. The substrate-native occupancy cost (the shell Capacity filled separately for protons and
neutrons, with the E8 spacing `ℏω(A)`, oscillator smooth energy `(ℏω/4)(3N)^{4/3}`) would give
`ℏω(A)·(3A/2)^{-2/3}·(N−Z)²/4 = 8.3 MeV·(N−Z)²/A` (outside Lean). Added to `certifiedMass` it
restores a minimum for every `A` but at `Z ≈ A/2` (Pb at `Z = 104`), and the stable-line residual
goes from `4.8` to `42 m_e` rms. So it is not an additive term: the ledger's linear link asymmetry
and alpha-cluster kink are what fit the stable line, and a restoring term would mean re-deriving
both.

**The occupancy restoring term (`occupancySymmetry`).** The E8 reason: protons and neutrons are
different species, each fills its own shell ladder (Capacity `2j+1`, spin `2` from `PL.trace`),
and the levels are spaced by `ℏω(A)` (Governor). Filling `Z` and `N` separately, with the
oscillator smooth energy `(ℏω/4)(3N)^{4/3}`, costs `ℏω(A)·(3A/2)^{-2/3}·(N−Z)²/4` more than
filling them equally: `≈ 16.3 m_e ≈ 8.3 MeV · (N−Z)²/A` (`occupancySymmetry`). The alpha-cluster
suppression `(1 − |N−Z|/Δ)` is a second `N ≈ Z` preference for the same nucleons, so the two are
not both kept: `valleyMass` is `certifiedMass` with the alpha-cluster binding replaced by the
occupancy term. Comparison (outside Lean): the lowest-`valleyMass` isobar is `Z = 18, 24, 37, 47,
82, 92` at `A = 40, 56, 90, 120, 208, 238`, against stable `20, 26, 40, 50, 82, 92`. On the
stable line it is `≈ 100 m_e` too heavy on average (rms `53`): the bulk terms of `certifiedMass`
already absorb the average symmetry cost along the line, and most of the offset is the alpha-cluster binding
itself, which the swap removes. A consistent occupancy ledger would also carry the symmetric
filling energy (`≈ 37.5` MeV per nucleon with `ℏω(A)`), turning the link weights into a potential;
the substrate has no link potential separate from the net link cost, so that rebuild is not
attempted (`REVIEW-AND-NEXT.md` §1 item 1).

**Comparison (outside Lean, `RESIDUALS.md`).** The isobar of lowest `certifiedMass`
matches the stable isobar for `A = 12, 16, 27, 40`. It is `Z = 28` at `A = 56` (stable `26`), `45`
at `A = 90` (`40`), `53` at `A = 107` (`47`). From `A ≈ 120` there is no local minimum near the
stable isobar: around Sn-120 the mass is locally flat or maximal in `Z`, and it falls steadily
towards neutron-rich isobars. Along the stable line itself the ledger matches measured masses to
`4.8 m_e` rms, which is where the SEMF regression (asymmetry `23.7` MeV) was taken.
-/

noncomputable section
namespace PMAtoms

/-- **Closed form of the typed link binding.** For `Z + N > 4`,
`packingBindingTyped Z N = L(A)·(w + s·(N − Z)/A)`. -/
theorem packingBindingTyped_closed (z n : Nat) (h : 4 < z + n) :
    packingBindingTyped z n =
      packingLinks (z + n) *
        (packingWeight + packingChannelAsymmetry * (((n : ℝ) - (z : ℝ)) / ((z : ℝ) + (n : ℝ)))) := by
  have hA : (4 : ℝ) < (z : ℝ) + (n : ℝ) := by exact_mod_cast h
  have h1 : ((z : ℝ) + (n : ℝ)) ≠ 0 := by linarith
  have h2 : ((z : ℝ) + (n : ℝ) - 1) ≠ 0 := by linarith
  unfold packingBindingTyped packingTypedCounts bindingFromRealCounts typedChannelWeight
  have hle : ¬ (z + n ≤ 4) := by omega
  simp only [hle, ↓reduceIte, mixedPP, mixedPN, mixedNN]
  field_simp
  ring

/-- At fixed `A`, moving one proton to a neutron changes the link binding by the constant
`2·s·L(A)/A`: the link ledger has no curvature in `Z`. -/
theorem packingBindingTyped_step (z n : Nat) (h : 4 < z + n + 1) :
    packingBindingTyped z (n + 1) - packingBindingTyped (z + 1) n =
      packingLinks (z + n + 1) * (2 * packingChannelAsymmetry / ((z : ℝ) + (n : ℝ) + 1)) := by
  rw [packingBindingTyped_closed z (n + 1) (by omega),
    packingBindingTyped_closed (z + 1) n (by omega)]
  have e1 : z + (n + 1) = z + n + 1 := by omega
  have e2 : z + 1 + n = z + n + 1 := by omega
  rw [e1, e2]
  push_cast
  have hB : (z : ℝ) + ((n : ℝ) + 1) ≠ 0 := by positivity
  have hC : (z : ℝ) + 1 + (n : ℝ) ≠ 0 := by positivity
  have hD : (z : ℝ) + (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **No potential symmetry energy.** The `pn` weight is exactly the mean of the `pp` and `nn`
weights, so swapping like pairs for unlike pairs costs nothing at second order. In the standard
model the unlike (`T = 0`) channel binds more strongly, which supplies about half of the symmetry
energy. -/
theorem typed_pn_mean :
    typedChannelWeight .pn = (typedChannelWeight .pp + typedChannelWeight .nn) / 2 := by
  simp only [typedChannelWeight]; ring

/-! ## The occupancy restoring term -/

/-- Coefficient of the occupancy symmetry cost: `ℏω`-coefficient `χ·m_p/Δ` times
`(3/2)^{-2/3}/4` (`≈ 16.3 m_e`). -/
noncomputable def occupancySymmetryCoeff : ℝ :=
  shellEnergyUnit / (4 * (3 / 2 : ℝ) ^ ((2 : ℝ) / 3))

/-- **Occupancy symmetry cost** `C·(N−Z)²/A`: separate proton and neutron filling of the shell
ladder with spacing `ℏω(A)`. -/
noncomputable def occupancySymmetry (z n : Nat) : ℝ :=
  occupancySymmetryCoeff * (((n : ℝ) - (z : ℝ)) ^ 2 / ((z : ℝ) + (n : ℝ)))

theorem occupancySymmetryCoeff_pos : 0 < occupancySymmetryCoeff := by
  unfold occupancySymmetryCoeff
  have h : (0 : ℝ) < (3 / 2 : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  exact div_pos shellEnergyUnit_pos (by positivity)

theorem occupancySymmetry_nonneg (z n : Nat) : 0 ≤ occupancySymmetry z n := by
  unfold occupancySymmetry
  exact mul_nonneg occupancySymmetryCoeff_pos.le (by positivity)

/-- Equal filling costs nothing. -/
theorem occupancySymmetry_self (z : Nat) : occupancySymmetry z z = 0 := by
  simp [occupancySymmetry]

/-- **Candidate valley mass.** `certifiedMass` with the alpha-cluster binding (and its isospin
suppression) replaced by the occupancy term. Comparison only. -/
noncomputable def valleyMass (z n : Nat) : ℝ :=
  certifiedMass z n + alphaClosureBinding z n + occupancySymmetry z n

end PMAtoms
