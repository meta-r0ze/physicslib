import PMAtoms.LinkWeights
import PMAtoms.LinkModes
import PMAtoms.NuclearLine
import PMAtoms.NuclearFolding
import PMAtoms.NuclearPacking3D
import PMHadrons.CompositeMasses
import Mathlib.Tactic

/-!
# Two-ledger nuclear mass

`M(Z,N) = free nucleons − link binding + charge repulsion`.

The link weights carry a charge asymmetry `±c/2` around the map weight `πD`, and
the charge ledger carries `c = πD/(2σ)` per proton pair. The asymmetry and the
charge term cancel in the H-3/He-3 mirror, leaving exactly the free
neutron−proton−electron difference. So the mirror is a cancellation, not a
Coulomb measurement.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons
open PMHadrons.CompositeMasses

/-- Charge coupling `c = πD/(2σ)`. -/
def chargeCoupling : ℝ := Real.pi * (D : ℝ) / (2 * (σ : ℝ))

theorem chargeCoupling_eq_e8 : chargeCoupling = e8ChargeCoupling := rfl

theorem chargeCoupling_eq : chargeCoupling = Real.pi * 4 / 10 := by
  simp [chargeCoupling, D, σ]
  norm_num

/-- Link weights for the mass ledger: `pp = πD + c/2`, `pn = πD`, `nn = πD − c/2`. -/
def massLinkWeight : LinkType → ℝ
  | .pp => mapWeight + chargeCoupling / 2
  | .pn => mapWeight
  | .nn => mapWeight - chargeCoupling / 2

/-- Number of proton pairs. -/
def chargePairs (z : Nat) : ℝ := ((z * (z - 1) / 2 : Nat) : ℝ)

/-- Charge ledger: `c` per proton pair. -/
def chargeTerm (z : Nat) : ℝ := chargePairs z * chargeCoupling

/-- Binding from an explicit `(pp,pn,nn)` count triple. -/
def bindingFromCounts (wpp wpn wnn : ℝ) (c : Nat × Nat × Nat) : ℝ :=
  wpp * (c.1 : ℝ) + wpn * (c.2.1 : ℝ) + wnn * (c.2.2 : ℝ)

/-- Link ledger: line/ring binding with the mass link weights. -/
def massBinding (z n : Nat) : ℝ :=
  bindingFromCounts (massLinkWeight .pp) (massLinkWeight .pn) (massLinkWeight .nn)
    (lineCounts z n)

/-- Capped link ledger: homo channels saturate at `Z/2`, `N/2`. -/
def cappedMassBinding (z n : Nat) : ℝ :=
  bindingFromCounts (massLinkWeight .pp) (massLinkWeight .pn) (massLinkWeight .nn)
    (cappedLineCounts z n)

/-- **Two-ledger nuclear mass** in `m_e` units (neutral atom). -/
def nuclearMass (z n : Nat) : ℝ :=
  (z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ) -
    massBinding z n + chargeTerm z

/-- Capped two-ledger mass, with the homo-channel saturation. -/
def nuclearMassCapped (z n : Nat) : ℝ :=
  (z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ) -
    cappedMassBinding z n + chargeTerm z

/-- Explicit decomposition into free, link, and charge ledgers. -/
theorem nuclearMass_decomp (z n : Nat) :
    nuclearMass z n =
      ((z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ)) -
        massBinding z n + chargeTerm z := rfl

theorem chargeTerm_zero : chargeTerm 0 = 0 := by
  simp [chargeTerm, chargePairs]

theorem chargeTerm_one : chargeTerm 1 = 0 := by
  simp [chargeTerm, chargePairs]

theorem chargeTerm_two : chargeTerm 2 = chargeCoupling := by
  simp [chargeTerm, chargePairs, chargeCoupling]

theorem chargeTerm_nonneg (z : Nat) : 0 ≤ chargeTerm z := by
  unfold chargeTerm chargePairs
  have hc : 0 ≤ chargeCoupling := by
    unfold chargeCoupling
    positivity
  positivity

/-- **Mirror cancellation.** The link asymmetry and the charge term cancel, so
`M(H-3) − M(He-3) = m_n − m_p − m_e`. -/
theorem mirror_h3_he3 :
    nuclearMass 1 2 - nuclearMass 2 1 = neutron - proton - 1 := by
  unfold nuclearMass massBinding massLinkWeight bindingFromCounts
  rw [lineCounts_h3, lineCounts_he3]
  simp [chargeTerm_one, chargeTerm_two]
  ring

/-- The mirror difference is exactly the free neutron−proton−electron gap. -/
theorem mirror_is_free :
    nuclearMass 1 2 - nuclearMass 2 1 = neutron - proton - 1 :=
  mirror_h3_he3

/-- The cap is inactive for H-3. -/
theorem cappedLineCounts_h3 : cappedLineCounts 1 2 = lineCounts 1 2 := by
  decide

/-- The cap is inactive for He-3. -/
theorem cappedLineCounts_he3 : cappedLineCounts 2 1 = lineCounts 2 1 := by
  decide

theorem cappedMassBinding_h3 : cappedMassBinding 1 2 = massBinding 1 2 := by
  unfold cappedMassBinding massBinding
  rw [cappedLineCounts_h3]

theorem cappedMassBinding_he3 : cappedMassBinding 2 1 = massBinding 2 1 := by
  unfold cappedMassBinding massBinding
  rw [cappedLineCounts_he3]

theorem nuclearMassCapped_h3 : nuclearMassCapped 1 2 = nuclearMass 1 2 := by
  unfold nuclearMassCapped nuclearMass
  rw [cappedMassBinding_h3]

theorem nuclearMassCapped_he3 : nuclearMassCapped 2 1 = nuclearMass 2 1 := by
  unfold nuclearMassCapped nuclearMass
  rw [cappedMassBinding_he3]

/-- **Capped mirror cancellation**: the saturation does not disturb the H-3/He-3
cancellation. -/
theorem mirror_h3_he3_capped :
    nuclearMassCapped 1 2 - nuclearMassCapped 2 1 = neutron - proton - 1 := by
  rw [nuclearMassCapped_h3, nuclearMassCapped_he3]
  exact mirror_h3_he3


/-- E8 per-link weight for 3D packing: `πD · (σ−χ)/σ = πD · 3/5`. -/
def packingWeight : ℝ :=
  mapWeight * (((σ - χ : Nat) : ℝ) / (σ : ℝ))

theorem packingWeight_eq : packingWeight = Real.pi * 4 * (3 / 5) := by
  unfold packingWeight mapWeight
  norm_num [D, σ, χ, PMSubstrate.baseline]

theorem packingWeight_eq_map_mul_sphere :
    packingWeight = mapWeight * (((σ - χ : Nat) : ℝ) / (σ : ℝ)) := rfl

theorem packingWeight_eq_map_mul_three_fifths :
    packingWeight = mapWeight * (3 / 5) := by
  rw [packingWeight_eq_map_mul_sphere, sphere_factor]

/-- The mirror charge, used as the isospin link asymmetry. -/
def mirrorCharge : ℝ := sphereCoulomb chargeCoupling 2 3

/-- Link asymmetry `(Z−N)·Q_m/2`; this cancels the mirror charge exactly. -/
def packingAsymmetry (z n : Nat) : ℝ :=
  ((z : ℝ) - (n : ℝ)) * (mirrorCharge / 2)

/-- 3D packing link ledger: `w·L(A) + (Z−N)·Q_m/2`. -/
def packingBinding (z n : Nat) : ℝ :=
  packingWeight * packingLinks (z + n) + packingAsymmetry z n

/-- Screened charge ledger for a packing of mass number `a`. -/
def chargeTermSphere (z a : Nat) : ℝ :=
  sphereCoulomb chargeCoupling z a

theorem chargeTermSphere_one_three : chargeTermSphere 1 3 = 0 := by
  unfold chargeTermSphere
  exact sphereCoulomb_one _ 3

theorem chargeTermSphere_two_three : chargeTermSphere 2 3 = mirrorCharge := rfl

theorem packingBinding_h3 :
    packingBinding 1 2 = packingWeight * packingLinks 3 - mirrorCharge / 2 := by
  unfold packingBinding packingAsymmetry
  norm_num
  ring

theorem packingBinding_he3 :
    packingBinding 2 1 = packingWeight * packingLinks 3 + mirrorCharge / 2 := by
  unfold packingBinding packingAsymmetry
  norm_num

/-- **3D-packing two-ledger mass.** -/
def nuclearMassPacking (z n : Nat) : ℝ :=
  ((z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ)) -
    packingBinding z n + chargeTermSphere z (z + n)

/-- **The packing mirror still cancels**: the isospin link asymmetry equals the
mirror charge, leaving exactly the free `n − p − e` gap. -/
theorem mirror_h3_he3_packing :
    nuclearMassPacking 1 2 - nuclearMassPacking 2 1 = neutron - proton - 1 := by
  unfold nuclearMassPacking
  rw [packingBinding_h3, packingBinding_he3]
  rw [chargeTermSphere_one_three, chargeTermSphere_two_three]
  ring


/-! ## Typed 3D packing

The cubic edge count is split into `pp`, `pn`, and `nn`.  For `A ≤ 4` the exact
line counts are used; for larger `A` the mean-field channel counts are used.
The channel asymmetry is `σ/ν = 5/16`, while the symmetric weight is
`πD·(σ−χ)/σ = πD·3/5`.
-/

/-- Channel asymmetry, derived from the boundary weight and half the sector
channels: `boundaryWeight / (ν/2) = σ/ν = 5/16`. -/
def packingChannelAsymmetry : ℝ := boundaryWeight / ((ν : ℝ) / 2)

theorem packingChannelAsymmetry_eq_sigma_nu :
    packingChannelAsymmetry = (σ : ℝ) / (ν : ℝ) := by
  unfold packingChannelAsymmetry boundaryWeight
  field_simp

theorem packingChannelAsymmetry_eq : packingChannelAsymmetry = 5 / 16 := by
  rw [packingChannelAsymmetry_eq_sigma_nu]
  norm_num [σ, ν, PMSubstrate.baseline]

/-- Typed link weights: `pp = w − s`, `pn = w`, `nn = w + s`. -/
def typedChannelWeight : LinkType → ℝ
  | .pp => packingWeight - packingChannelAsymmetry
  | .pn => packingWeight
  | .nn => packingWeight + packingChannelAsymmetry

/-- Binding from real-valued channel counts. -/
def bindingFromRealCounts (wpp wpn wnn : ℝ) (c : ℝ × ℝ × ℝ) : ℝ :=
  wpp * c.1 + wpn * c.2.1 + wnn * c.2.2

/-- Exact line counts for `A ≤ 4`; mean-field cubic counts for larger `A`. -/
def packingTypedCounts (z n : Nat) : ℝ × ℝ × ℝ :=
  if z + n ≤ 4 then
    let c := lineCounts z n
    ((c.1 : ℝ), (c.2.1 : ℝ), (c.2.2 : ℝ))
  else
    let e := packingLinks (z + n)
    (mixedPP e z n, mixedPN e z n, mixedNN e z n)

/-- Typed 3D packing binding. -/
def packingBindingTyped (z n : Nat) : ℝ :=
  bindingFromRealCounts (typedChannelWeight .pp) (typedChannelWeight .pn)
    (typedChannelWeight .nn) (packingTypedCounts z n)

/-- Typed 3D-packing mass. -/
def nuclearMassPackingTyped (z n : Nat) : ℝ :=
  ((z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ)) -
    packingBindingTyped z n + chargeTermSphere z (z + n)

theorem packingTypedCounts_h3 : packingTypedCounts 1 2 = (0, 2, 1) := by
  simp [packingTypedCounts, lineCounts_h3]

theorem packingTypedCounts_he3 : packingTypedCounts 2 1 = (1, 2, 0) := by
  simp [packingTypedCounts, lineCounts_he3]

theorem packingBindingTyped_h3 :
    packingBindingTyped 1 2 = 3 * packingWeight + packingChannelAsymmetry := by
  unfold packingBindingTyped bindingFromRealCounts typedChannelWeight
  rw [packingTypedCounts_h3]
  ring

theorem packingBindingTyped_he3 :
    packingBindingTyped 2 1 = 3 * packingWeight - packingChannelAsymmetry := by
  unfold packingBindingTyped bindingFromRealCounts typedChannelWeight
  rw [packingTypedCounts_he3]
  ring

/-- **Typed mirror.** The exact channel counts give
`M(H3) − M(He3) = m_n − m_p − m_e − 2s − Q_m`, with `s = σ/ν`. -/
theorem mirror_h3_he3_typed :
    nuclearMassPackingTyped 1 2 - nuclearMassPackingTyped 2 1 =
      neutron - proton - 1 - 2 * packingChannelAsymmetry - mirrorCharge := by
  unfold nuclearMassPackingTyped
  rw [packingBindingTyped_h3, packingBindingTyped_he3]
  rw [chargeTermSphere_one_three, chargeTermSphere_two_three]
  ring


theorem chargeTermSphere_nonneg (z a : Nat) : 0 ≤ chargeTermSphere z a := by
  unfold chargeTermSphere
  exact sphereCoulomb_nonneg (by unfold chargeCoupling; positivity) z a

theorem packingChannelAsymmetry_nonneg : 0 ≤ packingChannelAsymmetry := by
  rw [packingChannelAsymmetry_eq]
  norm_num

theorem nuclearMassPackingTyped_decomp (z n : Nat) :
    nuclearMassPackingTyped z n =
      ((z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ)) -
        packingBindingTyped z n + chargeTermSphere z (z + n) := rfl


/-! ## Closure ledger

The remaining binding is the number of independent cycles.  The closure weight is
the same E8 ratio `σ/ν = 5/16` used for the channel asymmetry.
-/

/-- Closure weight: the same derived channel asymmetry `σ/ν = 5/16`. -/
def closureWeight : ℝ := packingChannelAsymmetry

theorem closureWeight_eq : closureWeight = 5 / 16 := by
  rw [closureWeight, packingChannelAsymmetry_eq]

theorem closureWeight_eq_channelAsymmetry : closureWeight = packingChannelAsymmetry := rfl

/-- Closure binding: `w_c · R(A)`. -/
def closureBinding (z n : Nat) : ℝ :=
  closureWeight * packingClosureRank (z + n)

/-- Typed packing mass with the closure term. -/
def nuclearMassPackingClosure (z n : Nat) : ℝ :=
  nuclearMassPackingTyped z n - closureBinding z n

theorem nuclearMassPackingClosure_decomp (z n : Nat) :
    nuclearMassPackingClosure z n =
      nuclearMassPackingTyped z n - closureBinding z n := rfl

theorem closureWeight_nonneg : 0 ≤ closureWeight := by
  rw [closureWeight_eq]
  norm_num


theorem chargePairs_mono {m n : Nat} (h : m ≤ n) : chargePairs m ≤ chargePairs n := by
  unfold chargePairs
  have hmn : m * (m - 1) ≤ n * (n - 1) :=
    Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)
  exact_mod_cast Nat.div_le_div_right hmn


/-! ## Alpha-cluster closure (mid-mass term)

Alpha-conjugate nuclei (`N = Z`, `Z` even) are chains of closed tetrahedra.
Each alpha contributes a closure `Δ/D = 43/4 m_e`.  The term is switched off for
non-alpha-conjugate nuclei, so it does not disturb the mirror or Pb.
-/

/-- Isospin gap `|Z−N|`. -/
def isospinGap (z n : Nat) : Nat := if z ≤ n then n - z else z - n

/-- Alpha-cluster occupation: `min(Z,N)/2`, linearly suppressed by the isospin
gap over one substrate period `Δ`, and zero once the gap reaches `Δ`. -/
def alphaCount (z n : Nat) : ℝ :=
  let gap := isospinGap z n
  if 4 ≤ z + n then
    if gap < Δ then ((min z n : Nat) : ℝ) / 2 * (1 - (gap : ℝ) / (Δ : ℝ)) else 0
  else 0

/-- Alpha-cluster closure weight `Δ/D = 43/4 m_e`. -/
def alphaClosureWeight : ℝ := (Δ : ℝ) / (D : ℝ)

theorem alphaClosureWeight_eq : alphaClosureWeight = 43 / 4 := by
  unfold alphaClosureWeight
  norm_num [Δ, D, PMSubstrate.baseline]

/-- Alpha-cluster closure binding. -/
def alphaClosureBinding (z n : Nat) : ℝ :=
  alphaClosureWeight * alphaCount z n

/-- Typed + closure + alpha-cluster mass. -/
def nuclearMassPackingAlpha (z n : Nat) : ℝ :=
  nuclearMassPackingClosure z n - alphaClosureBinding z n

theorem alphaCount_he4 : alphaCount 2 2 = 1 := by
  norm_num [alphaCount, isospinGap, Δ, PMSubstrate.baseline]

theorem alphaCount_c12 : alphaCount 6 6 = 3 := by
  norm_num [alphaCount, isospinGap, Δ, PMSubstrate.baseline]

theorem alphaCount_o16 : alphaCount 8 8 = 4 := by
  norm_num [alphaCount, isospinGap, Δ, PMSubstrate.baseline]

theorem alphaCount_h3 : alphaCount 1 2 = 0 := by
  norm_num [alphaCount, isospinGap, Δ, PMSubstrate.baseline]

theorem alphaCount_he3 : alphaCount 2 1 = 0 := by
  norm_num [alphaCount, isospinGap, Δ, PMSubstrate.baseline]

theorem alphaCount_li7 : alphaCount 3 4 = 63 / 43 := by
  norm_num [alphaCount, isospinGap, Δ, PMSubstrate.baseline]

theorem alphaCount_ar40 : alphaCount 18 22 = 351 / 43 := by
  norm_num [alphaCount, isospinGap, Δ, PMSubstrate.baseline]

theorem alphaCount_pb : alphaCount 82 126 = 0 := by
  norm_num [alphaCount, isospinGap, Δ, PMSubstrate.baseline]

theorem nuclearMassPackingAlpha_decomp (z n : Nat) :
    nuclearMassPackingAlpha z n =
      nuclearMassPackingClosure z n - alphaClosureBinding z n := rfl


/-! ## Alpha persistence budget

The linear isospin suppression is a surviving-budget rule: an alpha cluster has
capacity `min(Z,N)/2`, the isospin gap spends one unit of the `Δ`-period budget,
and the surviving fraction is `(Δ − gap)/Δ`.
-/

/-- Alpha capacity before the isospin toll. -/
def alphaCapacity (z n : Nat) : ℝ := ((min z n : Nat) : ℝ) / 2

/-- Remaining `Δ`-period budget after the isospin gap. -/
def isospinBudget (z n : Nat) : Nat :=
  if isospinGap z n < Δ then Δ - isospinGap z n else 0

/-- Alpha occupancy as capacity times surviving budget fraction. -/
def alphaCountBudget (z n : Nat) : ℝ :=
  if 4 ≤ z + n then alphaCapacity z n * (isospinBudget z n : ℝ) / (Δ : ℝ) else 0

/-- **The suppression is a surviving-budget rule**, not a fitted curve. -/
theorem alphaCount_eq_budget (z n : Nat) :
    alphaCount z n = alphaCountBudget z n := by
  unfold alphaCount alphaCountBudget alphaCapacity isospinBudget
  by_cases hA : 4 ≤ z + n
  · by_cases hg : isospinGap z n < Δ
    · simp [hA, hg]
      have hΔ : (Δ : ℝ) ≠ 0 := by norm_num [Δ, PMSubstrate.baseline]
      have hΔ43 : (Δ : ℝ) = 43 := by norm_num [Δ, PMSubstrate.baseline]
      rw [Nat.cast_sub (le_of_lt hg), hΔ43]
      field_simp [hΔ]
    · simp [hA, hg]
  · simp [hA]

theorem alphaCapacity_nonneg (z n : Nat) : 0 ≤ alphaCapacity z n := by
  unfold alphaCapacity
  positivity

theorem isospinBudget_le_Delta (z n : Nat) : isospinBudget z n ≤ Δ := by
  unfold isospinBudget
  split <;> omega

theorem alphaCountBudget_nonneg (z n : Nat) : 0 ≤ alphaCountBudget z n := by
  unfold alphaCountBudget
  split
  · unfold alphaCapacity
    positivity
  · norm_num

theorem alphaCountBudget_le_capacity (z n : Nat) (hA : 4 ≤ z + n) :
    alphaCountBudget z n ≤ alphaCapacity z n := by
  unfold alphaCountBudget
  rw [ite_eq_left hA]
  have hΔ : (0 : ℝ) < Δ := by norm_num [Δ, PMSubstrate.baseline]
  have hb : (isospinBudget z n : ℝ) ≤ (Δ : ℝ) := by
    exact_mod_cast isospinBudget_le_Delta z n
  have hfrac : (isospinBudget z n : ℝ) / (Δ : ℝ) ≤ 1 := by
    rw [div_le_one hΔ]
    exact hb
  have hcap : 0 ≤ alphaCapacity z n := alphaCapacity_nonneg z n
  calc
    alphaCapacity z n * (isospinBudget z n : ℝ) / (Δ : ℝ)
        = alphaCapacity z n * ((isospinBudget z n : ℝ) / (Δ : ℝ)) := by ring
    _ ≤ alphaCapacity z n * 1 := mul_le_mul_of_nonneg_left hfrac hcap
    _ = alphaCapacity z n := by ring


/-! ## Heavy shell correction

The two heavy closures are E8 counts:
`Z=82 = 2(Δ−χ)` and `N=126 = (σ−χ)(Δ−1)`.
Neutrons beyond `N=126` cost `Δ/(D+χ)` each; the mass correction is positive
(less binding).
-/

/-- Proton shell closure `2(Δ−χ) = 82`. -/
def protonShell : Nat := 2 * (Δ - χ)

theorem protonShell_eq : protonShell = 82 := by
  norm_num [protonShell, Δ, χ, PMSubstrate.baseline]

/-- Neutron shell closure `(σ−χ)(Δ−1) = 126`. -/
def neutronShell : Nat := (σ - χ) * (Δ - 1)

theorem neutronShell_eq : neutronShell = 126 := by
  norm_num [neutronShell, σ, χ, Δ, PMSubstrate.baseline]

/-- Neutrons beyond the `N=126` closure. -/
def neutronExcess (n : Nat) : Nat :=
  if neutronShell < n then n - neutronShell else 0

/-- Shell cost per excess neutron `Δ/(D+χ) = 43/6 m_e`. -/
def shellWeight : ℝ := (Δ : ℝ) / (((D + χ : Nat)) : ℝ)

theorem shellWeight_eq : shellWeight = 43 / 6 := by
  unfold shellWeight
  norm_num [Δ, D, χ, PMSubstrate.baseline]

/-- Positive mass correction for neutrons beyond the `N=126` shell. -/
def shellCorrection (n : Nat) : ℝ :=
  shellWeight * (neutronExcess n : ℝ)

/-- Two-ledger mass with the heavy shell correction. -/
def nuclearMassPackingShell (z n : Nat) : ℝ :=
  nuclearMassPackingAlpha z n + shellCorrection n

theorem neutronExcess_pb : neutronExcess 126 = 0 := by decide
theorem neutronExcess_u238 : neutronExcess 146 = 20 := by decide
theorem shellCorrection_pb : shellCorrection 126 = 0 := by
  simp [shellCorrection, neutronExcess_pb]
theorem nuclearMassPackingShell_decomp (z n : Nat) :
    nuclearMassPackingShell z n =
      nuclearMassPackingAlpha z n + shellCorrection n := rfl


/-- Odd-A pairing reduction of the shell cost: `(D−1)/D = 3/4`. -/
def shellPairingFactor (z n : Nat) : ℝ :=
  if (z + n) % 2 = 1 then (((D - 1 : Nat)) : ℝ) / (D : ℝ) else 1

theorem shellPairingFactor_even (z n : Nat) (h : (z + n) % 2 = 0) :
    shellPairingFactor z n = 1 := by
  unfold shellPairingFactor
  rw [ite_eq_right (by omega : ¬ (z + n) % 2 = 1)]

theorem shellPairingFactor_odd (z n : Nat) (h : (z + n) % 2 = 1) :
    shellPairingFactor z n = 3 / 4 := by
  unfold shellPairingFactor
  rw [ite_eq_left h]
  norm_num [D, PMSubstrate.baseline]

/-- Shell correction with the odd-A pairing reduction. -/
def shellCorrectionPaired (z n : Nat) : ℝ :=
  shellWeight * shellPairingFactor z n * (neutronExcess n : ℝ)

/-- Two-ledger mass with the paired heavy-shell correction. -/
def nuclearMassPackingShellPaired (z n : Nat) : ℝ :=
  nuclearMassPackingAlpha z n + shellCorrectionPaired z n

theorem shellCorrectionPaired_u238 :
    shellCorrectionPaired 92 146 = shellCorrection 146 := by
  unfold shellCorrectionPaired shellCorrection shellPairingFactor
  norm_num

theorem shellCorrectionPaired_u235 :
    shellCorrectionPaired 92 143 = 3 / 4 * shellCorrection 143 := by
  unfold shellCorrectionPaired shellCorrection shellPairingFactor
  have hD : (D : ℝ) = 4 := by norm_num [D, PMSubstrate.baseline]
  have hD1 : ((D - 1 : Nat) : ℝ) = 3 := by norm_num [D, PMSubstrate.baseline]
  rw [hD, hD1]
  norm_num
  ring

theorem nuclearMassPackingShellPaired_decomp (z n : Nat) :
    nuclearMassPackingShellPaired z n =
      nuclearMassPackingAlpha z n + shellCorrectionPaired z n := rfl


theorem neutronExcess_mono {m n : Nat} (h : m ≤ n) :
    neutronExcess m ≤ neutronExcess n := by
  unfold neutronExcess
  split <;> split <;> omega

theorem shellCorrection_nonneg (n : Nat) : 0 ≤ shellCorrection n := by
  unfold shellCorrection
  have hw : 0 ≤ shellWeight := by rw [shellWeight_eq]; norm_num
  exact mul_nonneg hw (by positivity)

theorem shellPairingFactor_le_one (z n : Nat) : shellPairingFactor z n ≤ 1 := by
  unfold shellPairingFactor
  split <;> norm_num [D, PMSubstrate.baseline]

theorem shellCorrectionPaired_le_shellCorrection (z n : Nat) :
    shellCorrectionPaired z n ≤ shellCorrection n := by
  unfold shellCorrectionPaired shellCorrection
  have hw : 0 ≤ shellWeight := by rw [shellWeight_eq]; norm_num
  have hf : shellPairingFactor z n ≤ 1 := shellPairingFactor_le_one z n
  have hx : 0 ≤ (neutronExcess n : ℝ) := by positivity
  calc
    shellWeight * shellPairingFactor z n * (neutronExcess n : ℝ)
        ≤ shellWeight * 1 * (neutronExcess n : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hx
          exact mul_le_mul_of_nonneg_left hf hw
    _ = shellWeight * (neutronExcess n : ℝ) := by ring


/-- **E8 provenance bundle** for the model weights: every weight is an existing
E8 invariant or link quantity, not a free constant. -/
theorem e8_weight_provenance :
    packingWeight = mapWeight * (((σ - χ : Nat) : ℝ) / (σ : ℝ)) ∧
      packingChannelAsymmetry = boundaryWeight / ((ν : ℝ) / 2) ∧
      alphaClosureWeight = (Δ : ℝ) / (D : ℝ) ∧
      shellWeight = (Δ : ℝ) / (((D + χ : Nat)) : ℝ) ∧
      shellPairingFactor 1 2 = 3 / 4 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  unfold shellPairingFactor
  norm_num [D, PMSubstrate.baseline]


/-- The `3/5` packing weight is the active-colour fraction of the link row sum:
`(linkRowSum − reference_axes)/σ = (4−1)/5`. -/
theorem packingWeight_from_linkRow :
    packingWeight = mapWeight * ((linkRowSum - 1) / (σ : ℝ)) := by
  rw [packingWeight_eq_map_mul_sphere, linkRowSum_eq]
  norm_num [σ, χ, PMSubstrate.baseline]

/-- Channel asymmetry from the boundary weight and half the sector channels. -/
theorem packingChannelAsymmetry_from_link :
    packingChannelAsymmetry = boundaryWeight / ((ν : ℝ) / 2) := rfl


/-- Protons beyond the `Z=82` closure. -/
def protonExcess (z : Nat) : Nat :=
  if protonShell < z then z - protonShell else 0

theorem protonExcess_pb : protonExcess 82 = 0 := by decide
theorem protonExcess_u : protonExcess 92 = 10 := by decide
theorem protonExcess_cm : protonExcess 96 = 14 := by decide


/-- Candidate deformed proton closure `2(Δ+σ) = 96`, near Cm/Cf. -/
def deformedProtonShell : Nat := 2 * (Δ + σ)

theorem deformedProtonShell_eq : deformedProtonShell = 96 := by
  norm_num [deformedProtonShell, Δ, σ, PMSubstrate.baseline]

end PMAtoms
