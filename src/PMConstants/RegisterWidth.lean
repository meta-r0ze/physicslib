import PMConstants.ReferenceFrames
import PMConstants.General.GridEncoding
import PMSubstrate.ThetaE8

/-!
# Register width: what `η = 171/172` needs from a cell

The η row of the REVIEW lists "physical register width / reference factorization" as open.
`General.ReferenceCapacity` already reduces it to two numbers: a closed state of `N` registers over
an alphabet of size `a` carries an independent `r`-valued reference plus `K` full payload
registers exactly when `r · a^K ≤ a^N` (`encodable_iff`), and the optimum is `K = N − 1` exactly
when `r ≤ a` (`optimal_payload_iff`). With `N = r = 172` that optimum is `η = 171/172`
(`ReferenceFrames.static_capacity_optimal_overhead`).

**Factorization (closed registers).** The node's registers are its resolution,
`D·Δ = 172` (`PMSubstrate.baseline_loads`), forced with the substrate. A separate control track
(`ReferenceFrames.SeparateTrack`) would be a register beyond the resolution, so the reference must
be carried inside the 172. The reference is an origin among them, `r = 172`.

**Width.** What remains is `a ≥ 172`: one cell must be able to hold the origin.

* `e8_width_optimal`, `e8_width_overhead`: if a cell holds one substrate transition, an E8 root,
  then `a = 240` (`ThetaE8.e8_card_roots`), the optimum is `K = 171`, and the payload fraction is
  `η`.
* `channel_width_optimal`: if a cell held only a channel label (`a = ν = 16`), the origin would
  need two cells and the optimum would be `K = 170`, a different overhead `170/172`.
* `width_threshold`: statically, the one-slot optimum holds exactly when `172 ≤ a`.
* `clock_width_threshold`, `e8_width_clock`: the physical update advances the 43 phases of the
  `4 × 43` grid (`GridEncoding.gridTick`). A one-slot code that commutes with it exists exactly
  when `173 ≤ a` (`GridEncoding.grid_one_slot_iff`); a cell of exactly 172 symbols is enough
  statically but not under the clock (`ReferenceCapacity.grid_172_payload_bound`). Root-wide cells
  (`240`) clear the clock threshold, so `η = 171/172` holds with the clock running.

Status: η's register premise is now one statement, "a cell holds one transition"
(`a = |Φ(E₈)| = 240`), with the alternative it excludes stated. The closed-register step uses the
forced resolution; that the node has no registers beyond it is the Capacity reading, not a new
theorem.
-/

namespace PMConstants.RegisterWidth
open General.ReferenceCapacity Matrix

/-- The node's register count is its forced resolution. -/
theorem closed_registers : PMSubstrate.baseline.resolution = 172 :=
  PMSubstrate.baseline_loads.2.1

/-- The E8 root count, the alphabet of a cell holding one transition. -/
theorem root_alphabet :
    Nat.card {z : Fin 8 → ℤ // z ⬝ᵥ (PMSubstrate.Lattices.gram *ᵥ z) = 2} = 240 :=
  PMSubstrate.ThetaE8.e8_card_roots

/-- **The one-slot optimum holds exactly when a cell can hold the origin.** -/
theorem width_threshold (a : ℕ) (ha : 1 ≤ a) :
    Encodable 172 171 a 172 ↔ 172 ≤ a :=
  one_slot_iff 172 a 172 (by decide) ha

/-- **Under the clock the threshold is `173`.** -/
theorem clock_width_threshold (a : ℕ) (ha : 1 ≤ a) :
    (∃ code : Grid × (Fin 171 → Fin a) → (Grid → Fin a), Function.Injective code ∧
      ∀ o p, gridUpdate (code (o, p)) = code (gridTick o, p)) ↔ 173 ≤ a :=
  GridEncoding.grid_one_slot_iff ha

/-- **Root-wide cells carry the reference in one slot with the clock running.** -/
theorem e8_width_clock :
    ∃ code : Grid × (Fin 171 → Fin 240) → (Grid → Fin 240), Function.Injective code ∧
      ∀ o p, gridUpdate (code (o, p)) = code (gridTick o, p) :=
  GridEncoding.grid_one_slot_sufficient (by decide)

/-- **With root-wide cells the optimum payload is `171`.** -/
theorem e8_width_optimal (K : ℕ) : OptimalPayload 172 K 240 172 ↔ K = 171 :=
  optimal_payload_iff 172 K 240 172 (by decide) (by decide) (by decide)

/-- **With root-wide cells the payload fraction is `η = 171/172`.** -/
theorem e8_width_overhead (K : ℕ) (h : OptimalPayload 172 K 240 172) :
    (K : ℝ) / 172 = overhead :=
  ReferenceFrames.static_capacity_optimal_overhead 240 K (by decide) h

theorem channel_payload_bound (K : ℕ) (h : Encodable 172 K 16 172) : K ≤ 170 := by
  have hb := (encodable_iff 172 K 16 172).mp h
  by_contra hK
  have hp : (16 : ℕ) ^ 171 ≤ 16 ^ K := pow_le_pow_right₀ (by decide) (by omega)
  norm_num at hb hp
  omega

/-- **With channel-wide cells the optimum would be `170`.** -/
theorem channel_width_optimal : OptimalPayload 172 170 16 172 :=
  ⟨(encodable_iff 172 170 16 172).mpr (by norm_num), fun j hj => channel_payload_bound j hj⟩

end PMConstants.RegisterWidth
