import PMFlavor.HalfTurnMixing
import PMFlavor.KronSeries

/-!
# `π` as a length and as an aperture: one Ohmic law for every mixing element

The node-crossing paths use `π` as an impedance (a unit boundary, `VubSeriesPath`, `KronSeries`;
the envelopes `env w = πw + χ` of `VcbEnvelope`; the node's capacity term `πΔ` in `Z_geo`). The
in-cycle mixing needs `π/N` as an admittance (`HalfTurnMixing`). Both follow from Ohm's geometric
law, conductance = aperture / length (`ohmic`), once it is said which way the transfer crosses the
half-turn.

* **Along a boundary: `π` is a length.** Barbier gives a width-`w` envelope a boundary of length
  `πw` (`PMSubstrate.Capacity.barbier`: the half-turn of directions times the width). A transfer
  that runs along it, through a unit aperture, has conductance `1/(πw)` (`boundary_element`); this is
  the boundary of `|V_ub|` and the envelopes of `Z_geo` and `|V_cb|`.
* **Through the refresh: `π` is an aperture.** The weak refresh is the sign exchange, a half-turn
  (`CarrierActions.same_axis_iff`); the transfer it carries passes through that half-turn of
  directions rather than along a boundary. Shared equally (Closure,
  `HandoffAdmittance.closure_one_price`) over the `N` type-preserving channels in parallel, each gets
  aperture `π/N` at unit length, conductance `π/N` (`channel_element`), and together they carry the
  whole half-turn (`channels_total`).

With the rule derived for the node (`KronSeries`: a quark coupling is the admittance between the
two generations; a lepton-axis mixing probability is a conductance, Landauer), the in-cycle mixings
are `s₁₂ = π/14` (quark amplitude, direct coupling, no node to eliminate) and
`sin²θ₁₂ = π/10` (lepton probability) (`in_cycle_quark`, `in_cycle_lepton`).

This picks the generator reading of `HalfTurnMixing`, so the solar prediction is `π/10 = 0.3142`
rather than the supplied `1/(2φ) = sin(π/10) = 0.3090`; JUNO's `0.3092 ± 0.0087` allows both
(`HalfTurnMixing.lepton_share_fits`), and its full precision separates them.

Premise: the refresh's half-turn is an aperture shared equally by the type-preserving channels in
parallel. Status: candidate.
-/

namespace PMFlavor.HalfTurnAperture

/-- Ohm's geometric law: conductance of an element of given aperture and length. -/
noncomputable def ohmic (aperture length : ℝ) : ℝ := aperture / length

theorem boundary_element (w : ℝ) : ohmic 1 (Real.pi * w) = 1 / (Real.pi * w) := rfl

theorem unit_boundary_in_vub : ohmic 1 (Real.pi * 1) = 1 / Real.pi := by
  simp [ohmic]

theorem channel_element (N : ℕ) : ohmic (Real.pi / N) 1 = Real.pi / N := by
  simp [ohmic]

theorem channels_total (N : ℕ) (hN : 0 < N) :
    ∑ _i : Fin N, ohmic (Real.pi / N) 1 = Real.pi := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [ohmic, div_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem in_cycle_quark :
    ohmic (Real.pi / ((Finset.univ.filter fun v : PMConstants.CarrierRepresentation.V =>
      PMConstants.CarrierRepresentation.onLepton v = false).card +
        Fintype.card (PMAction.CarrierEvents.Carrier 1) : ℕ)) 1 = Real.pi / 14 := by
  rw [HalfTurnMixing.quark_channels, channel_element]; norm_num

theorem in_cycle_lepton :
    ohmic (Real.pi / ((Finset.univ.filter fun v : PMConstants.CarrierRepresentation.V =>
      PMConstants.CarrierRepresentation.onLepton v = true).card +
        Fintype.card (PMAction.CarrierEvents.Carrier 1) : ℕ)) 1 = Real.pi / 10 := by
  rw [HalfTurnMixing.lepton_channels, channel_element]; norm_num

end PMFlavor.HalfTurnAperture
