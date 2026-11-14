import PMConstants.CarrierRepresentation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The in-cycle mixing as a half-turn shared over the type-preserving channels (candidate)

`ExchangeAxis`: one generation pair per sector mixes inside the cycle, through the reference's
(vector) class, with no `α`. Candidate mechanism, tested here against data: the weak refresh is the
sign exchange, a half-turn (`CarrierActions.same_axis_iff`); shared evenly over the `N` carriers
the sector's hop may use, each channel carries `π/N`, and the in-cycle mixing is that share.

**The channel count is the type-preserving set.** A sector holds `ν = 16` carriers, the vector
class and one spinor class (`PMSubstrate.ChannelSymmetry`). A vector carrier lies on exactly one
axis and that axis fixes its channel type (`CarrierRepresentation.one_axis`, `leftType`); a hop
that changes type is not a cycle event (`LeptonAxisRestriction.repair_cannot_restore`). A spinor
carrier lies on no single axis (`spinor_on_no_axis`: all four coordinates nonzero), so it carries no
type. So the type-preserving channels are the sector's own vector carriers plus the spinor class:
* `quark_channels`: `6` colour carriers + `8` spinor = `14`;
* `lepton_channels`: `2` lepton-axis carriers + `8` spinor = `10`.

**Data.**
* Quarks, amplitude: `s₁₂ = π/14` (`quark_share_fits`, `0.15σ` from the dressing-removed
  `0.22453 ± 0.00085`). The finite rotation `sin(π/14)` is more than `2σ` low
  (`rotation_excluded`): the share is the generator element, not a rotation.
* Leptons, probability: `sin²θ₁₂ = π/10 = 0.3142` fits JUNO's `0.3092 ± 0.0087` (`lepton_share_fits`).
  `half_turn_golden`: the supplied solar value `1/(2φ)` is exactly `sin(π/10)`, the same half-turn
  over ten channels as a finite rotation, so the pentagon cosine needs no `H₄`.

The amplitude-versus-probability split matches `NodeElimination` (quarks reach the reference node
by two legs, lepton-axis states by one). Open: why the in-cycle share reads the generator element
`π/N` (which would make the solar prediction `π/10`, `0.005` above `1/(2φ)`, resolvable by JUNO).
-/

namespace PMFlavor.HalfTurnMixing
open PMAction.CarrierEvents PMConstants.CarrierRepresentation

theorem spinor_on_no_axis :
    ∀ d : Carrier 1, (Finset.univ.filter fun i => vector d i ≠ 0).card = 4 := by
  decide +kernel

theorem quark_channels :
    (Finset.univ.filter fun v : V => onLepton v = false).card + Fintype.card (Carrier 1) = 14 := by
  rw [lepton_axis_split.1, carrier_card]

theorem lepton_channels :
    (Finset.univ.filter fun v : V => onLepton v = true).card + Fintype.card (Carrier 1) = 10 := by
  rw [lepton_axis_split.2, carrier_card]

theorem quark_share_fits : |Real.pi / 14 - 0.22453| / 0.00085 < 1 := by
  have h1 := Real.pi_gt_d4; have h2 := Real.pi_lt_d4
  rw [div_lt_one (by norm_num), abs_lt]; constructor <;> linarith

theorem rotation_excluded : Real.sin (Real.pi / 14) < 0.22453 - 2 * 0.00085 := by
  have h1 := Real.pi_gt_d4; have h2 := Real.pi_lt_d4
  set x := Real.pi / 14 with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hlo : (0.22439 : ℝ) ≤ x := by rw [hx]; linarith
  have hhi : x ≤ (0.22440 : ℝ) := by rw [hx]; linarith
  have hb := Real.sin_bound (x := x) (by rw [abs_of_pos hx0]; linarith)
  rw [abs_of_pos hx0] at hb
  have hb' := (abs_le.mp hb).2
  have h3 : (0.22439 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hlo 3
  have h5 : x ^ 5 ≤ (0.22440 : ℝ) ^ 5 := pow_le_pow_left₀ hx0.le hhi 5
  norm_num at h3 h5 ⊢
  linarith

theorem lepton_share_fits : |Real.pi / 10 - 0.3092| / 0.0087 < 1 := by
  have h1 := Real.pi_gt_d4; have h2 := Real.pi_lt_d4
  rw [div_lt_one (by norm_num), abs_lt]; constructor <;> linarith

theorem half_turn_sine : Real.sin (Real.pi / 10) = (Real.sqrt 5 - 1) / 4 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [← Real.cos_pi_div_two_sub, show Real.pi / 2 - Real.pi / 10 = 2 * (Real.pi / 5) by ring,
    Real.cos_two_mul, Real.cos_pi_div_five]
  linear_combination (1 / 8) * h5

theorem half_turn_golden :
    Real.sin (Real.pi / 10) = 1 / (2 * ((1 + Real.sqrt 5) / 2)) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < 2 * ((1 + Real.sqrt 5) / 2) := by positivity
  rw [half_turn_sine, eq_div_iff hpos.ne']
  linear_combination (1 / 4) * h5

end PMFlavor.HalfTurnMixing
