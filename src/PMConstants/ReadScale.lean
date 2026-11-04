import PMConstants.StableReadout

/-!
# One rule for both matching scales

`StableReadout` used two branches: read where scale-independent when possible, otherwise at the
mass of the unique `Q`-neutral broken direction. Both follow from one principle: **a read is
evaluated at the mass of the gauge direction that executes it.**

* The read must not change electric charge, so the executing direction commutes with `Q`. These
  are the neutral directions `z = 0` (`ReadoutScales.commutes_iff`).
* The electric read compares charge without moving the reference. Its direction fixes the
  reference, which is the photon, of mass zero (`NeutralCurrent.photon_is_null`). It is read at
  scale `0`. Below the lightest charged carrier, an abelian coupling stops running
  (`StableReadout.abelian_stationary_iff`), so the value there is `α(0)`.
* The colour comparison runs through the payload and reads the reference. Its direction moves the
  reference, which is the `Z` (`ReadoutScales.neutral_broken_iff`). It is read at `m_Z`, the
  nonzero eigenvalue of the neutral mass form (`NeutralCurrent.z_mass`).

`read_scales` collects these. `matching_log_zero_iff` shows the principle is the same as asking
the read to carry no matching log: `c log(μ/m) = 0` exactly when `μ = m`. `exact_read_on_shell`
shows an exact read, which returns the event amplitude with no residual, has no matching log. So it
is read at the executing mass. `colour_exact_read` removes the one-loop
form. The inverse coupling runs at slope `b₀/2π ≠ 0` (`colour_never_stationary`), so the running is
injective, and an exact read is at `μ = m`. `photon_read_flat`: below charged thresholds the slope is
zero, so the read is `α(0)` at any scale there. That the executing mode's scale is its mass is
derived in `OnShell` from persistence and frame independence.
-/

noncomputable section
namespace PMConstants.ReadScale
open PMAction.RunningCoefficients Matrix GeneratorNormalization PacketTraceForm

theorem read_scales (g g' : ℝ) (hg : 0 < g) :
    (ReferenceMasses.neutralForm g g') *ᵥ ![g' / NeutralCurrent.N g g', g / NeutralCurrent.N g g'] = 0 ∧
      (ReferenceMasses.neutralForm g g').trace = NeutralCurrent.N g g' ^ 2 / 4 ∧
      bContent 0 0 0 = 0 ∧
      (∀ (a : ℝ) (z : ℂ) (b : ℝ),
        (ReferenceDirections.gen a z b * (t3 + hyperGen) = (t3 + hyperGen) * ReferenceDirections.gen a z b ∧
          ¬ ReferenceStabilizer.Fixes (ReferenceDirections.gen a z b) (ReferenceAnchor.lepton 0)) ↔
          z = 0 ∧ a ≠ b / 2) := by
  obtain ⟨-, h2, h3, h4⟩ := StableReadout.anchor_is_Z g g' hg
  exact ⟨h3, h4, (StableReadout.abelian_stationary_iff 0 0 le_rfl le_rfl).mpr ⟨rfl, rfl⟩, h2⟩

/-- **The matching log vanishes only on shell.** At one loop, reading a coupling at scale `μ` when
the event is executed by a mode of mass `m` adds `c · log (μ / m)`. If the coefficient `c` is
nonzero, this vanishes exactly when `μ = m`. So the principle "read at the executing mass" is the
same as "the read carries no large matching log". -/
theorem matching_log_zero_iff (c μ m : ℝ) (hc : c ≠ 0) (hμ : 0 < μ) (hm : 0 < m) :
    c * Real.log (μ / m) = 0 ↔ μ = m := by
  constructor
  · intro h
    have hl : Real.log (μ / m) = 0 := (mul_eq_zero.mp h).resolve_left hc
    have hpos : 0 < μ / m := div_pos hμ hm
    have : μ / m = 1 := Real.eq_one_of_pos_of_log_eq_zero hpos hl
    field_simp at this
    exact this
  · rintro rfl
    simp [div_self hm.ne']

/-- **An exact read has no matching log.** At one loop, the event amplitude executed by a mode of
mass `m` and read through a coupling at scale `μ` is `A = α + c α² log(μ/m)`. The read is exact
(it returns the event with no residual, `SectorObligations.refresh_exact`) when `α = A`. For a
nonzero coupling and coefficient, that holds exactly when `μ = m`. So the read scale is the
executing mass, with no separate principle. -/
theorem exact_read_on_shell (α c μ m : ℝ) (hα : α ≠ 0) (hc : c ≠ 0) (hμ : 0 < μ) (hm : 0 < m) :
    α = α + c * α ^ 2 * Real.log (μ / m) ↔ μ = m := by
  rw [← matching_log_zero_iff c μ m hc hμ hm]
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα
  constructor
  · intro h
    have : c * Real.log (μ / m) * α ^ 2 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hα2
  · intro h
    have : c * α ^ 2 * Real.log (μ / m) = (c * Real.log (μ / m)) * α ^ 2 := by ring
    rw [this, h]; ring

/-! ## The read bridge from the running law

At one loop the inverse coupling runs linearly in `log μ` with slope `b / 2π`. Here this is the
statement `HasDerivAt f k ℓ` for every `ℓ`, where `f ℓ` is the inverse coupling at `μ = e^ℓ`. The
read at scale `μ` returns `f (log μ)`. The record of an event executed by a mode of mass `m` is
the response at that event's own scale, `f (log m)`. -/

/-- A response running at a constant rate in `log μ` is affine. -/
theorem affine_of_rate (f : ℝ → ℝ) (k : ℝ) (hf : ∀ ℓ, HasDerivAt f k ℓ) (ℓ₀ ℓ : ℝ) :
    f ℓ = f ℓ₀ + k * (ℓ - ℓ₀) := by
  have hg : ∀ x, HasDerivAt (fun y => f y - k * y) 0 x := by
    intro x
    have := (hf x).sub ((hasDerivAt_id x).const_mul k)
    simp only [mul_one, sub_self] at this
    exact this
  have hc := is_const_of_deriv_eq_zero (fun x => (hg x).differentiableAt)
    (fun x => (hg x).deriv) ℓ ℓ₀
  linarith

/-- **An exact read is at the executing scale.** If the coupling runs (`k ≠ 0`), the read at `μ`
equals the event's record at `m` exactly when `μ = m`. -/
theorem exact_read_iff_same_scale (f : ℝ → ℝ) (k : ℝ) (hk : k ≠ 0) (hf : ∀ ℓ, HasDerivAt f k ℓ)
    (μ m : ℝ) (hμ : 0 < μ) (hm : 0 < m) : f (Real.log μ) = f (Real.log m) ↔ μ = m := by
  rw [affine_of_rate f k hf (Real.log m) (Real.log μ)]
  constructor
  · intro h
    have : k * (Real.log μ - Real.log m) = 0 := by linarith
    have hl := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hk)
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hμ) (Set.mem_Ioi.mpr hm) hl
  · rintro rfl; ring

/-- **Colour is read at the executing mass.** Colour runs at every scale
(`StableReadout.colour_never_stationary`), so with slope `b₀ / 2π` its exact read is at
`μ = m`. The executing direction is the `Z`, so `m = m_Z`. -/
theorem colour_exact_read (nf : ℕ) (f : ℝ → ℝ)
    (hf : ∀ ℓ, HasDerivAt f ((b0 3 nf 0 : ℝ) / (2 * Real.pi)) ℓ) (μ m : ℝ) (hμ : 0 < μ)
    (hm : 0 < m) : f (Real.log μ) = f (Real.log m) ↔ μ = m := by
  have hb : (b0 3 nf 0 : ℝ) ≠ 0 := by exact_mod_cast StableReadout.colour_never_stationary nf
  exact exact_read_iff_same_scale f _ (div_ne_zero hb (by positivity)) hf μ m hμ hm

/-- **The photon read is scale-free below charged thresholds.** With no charged matter active, the
abelian slope is zero (`StableReadout.abelian_stationary_iff`), so every scale in that window
reads the same value, `α(0)`. -/
theorem photon_read_flat (f : ℝ → ℝ) (hf : ∀ ℓ, HasDerivAt f ((bContent 0 0 0 : ℝ) / (2 * Real.pi)) ℓ)
    (μ m : ℝ) : f (Real.log μ) = f (Real.log m) := by
  have h0 : (bContent 0 0 0 : ℝ) = 0 := by
    exact_mod_cast (StableReadout.abelian_stationary_iff 0 0 le_rfl le_rfl).mpr ⟨rfl, rfl⟩
  rw [affine_of_rate f _ hf (Real.log m) (Real.log μ), h0]; ring

end PMConstants.ReadScale
