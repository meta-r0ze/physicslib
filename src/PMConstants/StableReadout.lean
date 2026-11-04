import PMAction.RunningCoefficients
import PMConstants.ScalePairing
import PMConstants.NeutralCurrent

/-!
# Why the colour formula pairs `α(0)` with `α_s(M_Z)`

`ScalePairing` showed the data keep the pairing of `α(0)` with `α_s(M_Z)` and exclude the same-scale
pairing at `9σ`, but did not say why. Persistence gives a reason: a readout that persists must not
depend on an arbitrary choice of where it is read. A running coupling has such a scale-free value
only on an interval where it does not run.

* `stationary_iff`: at one loop, `1/α(μ₁) = 1/α(μ₂)` for two distinct scales iff the coefficient
  vanishes on that interval.
* `abelian_stationary_iff`: an abelian coupling (no self-coupling, `C_A = 0`) stops running exactly
  when no charged matter is active (Paper II `RunningCoefficients.bContent`). Below the lightest
  charged carrier the electric coupling is constant: its scale-free readout is that plateau value,
  conventionally called `α(0)`. The lightest charged carrier is the electron, the reference's own
  charged carrier (`ReferenceAnchor`).
* `colour_never_stationary`: for colour with any whole number of quark flavours and no coloured
  scalars, `b₀ = 11 − 2n_f/3 ≠ 0`. The gluons are massless and always active, so colour runs at
  every scale and has **no** scale-free value of its own. Its readout must be anchored to a scale
  supplied by something else; the only scales available are the reference's, and among them the data
  keep the `Z` (`ReadoutScales.at_Z`, `at_W`, `at_H`, `at_v`).
* `pairing`: hence the photon side is read on its plateau and the colour side at the anchored
  scale; the same-scale alternative misses the data (`ScalePairing.same_scale_excluded`).

**Which reference scale anchors colour** (`anchor_is_Z`). Colour's readout is charge-blind: it
commutes with `Q`. An anchor it can read must therefore be a direction that commutes with `Q`, and
to supply a scale at all it must be broken (move the reference). `ReadoutScales.neutral_broken_iff`
says this is one real direction, the `Z`; its only intrinsic scale is its mass, the neutral form's
nonzero eigenvalue `N²/4` (`NeutralCurrent.z_mass`; the photon direction is null,
`photon_is_null`). The `W` carries charge, `m_H` is not a gauge direction, and `v` is not the mass
of any direction, so they are excluded structurally; `ReadoutScales.at_W`, `at_H`, `at_v` become
independent checks that agree.

Premises: a persistent readout is read where it is scale-independent when such a region exists;
otherwise at the intrinsic scale (mass) of the unique `Q`-neutral broken direction. One-loop running
is used for the stationarity criterion.
-/

noncomputable section
namespace PMConstants.StableReadout
open PMAction.RunningCoefficients Matrix GeneratorNormalization PacketTraceForm ReferenceAnchor
  ReferenceStabilizer ReferenceDirections

/-- One-loop inverse coupling. -/
def invRun (inv0 b μ0 μ : ℝ) : ℝ := inv0 - b / (2 * Real.pi) * Real.log (μ / μ0)

/-- **A coupling has the same value at two distinct scales iff it does not run there.** -/
theorem stationary_iff (inv0 b μ0 : ℝ) (h0 : 0 < μ0) {μ₁ μ₂ : ℝ} (h1 : 0 < μ₁) (h12 : μ₁ < μ₂) :
    invRun inv0 b μ0 μ₁ = invRun inv0 b μ0 μ₂ ↔ b = 0 := by
  have h2 : 0 < μ₂ := h1.trans h12
  have hl : Real.log (μ₁ / μ0) < Real.log (μ₂ / μ0) :=
    Real.log_lt_log (div_pos h1 h0) (div_lt_div_of_pos_right h12 h0)
  have hpi : 0 < 2 * Real.pi := by positivity
  unfold invRun
  constructor
  · intro h
    by_contra hb
    have : b / (2 * Real.pi) * (Real.log (μ₂ / μ0) - Real.log (μ₁ / μ0)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hb (by simpa [hpi.ne'] using h)
    · linarith
  · rintro rfl; simp

/-- **An abelian coupling stops running exactly when no charged matter is active.** -/
theorem abelian_stationary_iff (weyl scalar : ℚ) (hw : 0 ≤ weyl) (hs : 0 ≤ scalar) :
    bContent 0 weyl scalar = 0 ↔ weyl = 0 ∧ scalar = 0 := by
  rw [bContent_formula]
  constructor
  · intro h; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- **Colour runs at every scale.** -/
theorem colour_never_stationary (nf : ℕ) : b0 3 nf 0 ≠ 0 := by
  rw [b0_formula]
  intro h
  have h2 : ((2 * nf : ℕ) : ℚ) = 33 := by push_cast; linarith
  have : 2 * nf = 33 := by exact_mod_cast h2
  omega

/-- **The pairing.** The electric side has a scale-free plateau below the lightest charged carrier;
colour has none at any flavour number; the same-scale reading misses the data. -/
theorem pairing :
    bContent 0 0 0 = 0 ∧ (∀ nf : ℕ, b0 3 nf 0 ≠ 0) ∧
      ∀ {aZ : ℝ}, (1 / 127.96 < aZ ∧ aZ < 1 / 127.94) →
        9 < (aZ * footprint / ColourChannels.colourLedger - 0.1180) / 0.0009 :=
  ⟨(abelian_stationary_iff 0 0 le_rfl le_rfl).mpr ⟨rfl, rfl⟩, colour_never_stationary,
    fun h => (ScalePairing.same_scale_excluded h).2⟩

/-- **Colour's anchor is the `Z`.** Colour has no plateau; the `Q`-commuting broken directions are
exactly the `Z` line; its scale is the neutral form's trace (the photon direction being null). -/
theorem anchor_is_Z (g g' : ℝ) (hg : 0 < g) :
    (∀ nf : ℕ, b0 3 nf 0 ≠ 0) ∧
      (∀ (a : ℝ) (z : ℂ) (b : ℝ),
        (ReferenceDirections.gen a z b * (t3 + hyperGen) = (t3 + hyperGen) * ReferenceDirections.gen a z b ∧
          ¬ ReferenceStabilizer.Fixes (ReferenceDirections.gen a z b) (ReferenceAnchor.lepton 0)) ↔
          z = 0 ∧ a ≠ b / 2) ∧
      (ReferenceMasses.neutralForm g g') *ᵥ ![g' / NeutralCurrent.N g g', g / NeutralCurrent.N g g'] = 0 ∧
      (ReferenceMasses.neutralForm g g').trace = NeutralCurrent.N g g' ^ 2 / 4 :=
  ⟨colour_never_stationary, ReadoutScales.neutral_broken_iff, NeutralCurrent.photon_is_null g g',
    NeutralCurrent.z_mass g g' hg⟩

end PMConstants.StableReadout
