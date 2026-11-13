import PMConstants.PacketTraceForm
import PMConstants.ChainCouplings

/-!
# The colour generator normalization is not a separate choice

`ChainCouplings.colour_limit` takes the colour generators' trace normalization
`tr(TᵃTᵇ) = δᵃᵇ/2` as a hypothesis, and the α_s row of the REVIEW lists "normalization: charge
units, as for the weak sector" as open. The weak normalization is derived
(`ReferenceCharge`: the shared lepton-doublet reference gives charge units; the W mass excludes
the trace form, `GeneratorNormalization`). This module shows the colour value follows from either
rule the library considers.

* `colour_unit_iff`: on the packet, a colour generator's trace is `4×` its fundamental trace, as for
  a weak generator (`PacketTraceForm.colour_trace_product`, `weak_trace_product`: four triplets
  `Q, Q, u, d` and four doublets `Q×3, L`). So a colour unit with the weak unit's packet trace
  (the trace-form rule) has fundamental trace `1/2` exactly when the weak unit does.
* `colour_root_cartan`: in charge units (the rule the W mass selects), a colour generator along
  one root acts on the pair of colours it connects as a doublet, `T₃ = ±1/2`, and has fundamental
  trace `1/2`, the weak doublet's (`ReferenceStiffness.doublet_weak_trace`).
* `colour_eighth`: the remaining diagonal direction, `√3·T₈ = diag(1/2, 1/2, −1)`, is the sum of two
  root Cartans and has trace `3/2`, i.e. `tr T₈² = 1/2`, orthogonal to `T₃`. So the root
  normalization fixes the whole colour basis.

The two rules disagree only for hypercharge (abelian: `3/5`), which the W mass decides. For colour
both give `1/2`, so `colour_limit`'s normalization hypothesis is not an open choice. Why roots
share one normalization: primitive events are E8 root hops, all of norm 2 (`ThetaE8.e8_card_roots`
counts the norm-2 vectors), priced at one toll (`PMSubstrate.NetCost`).
-/

noncomputable section
namespace PMConstants.ColourNormalization
open Matrix PacketGaugeActions PacketTraceForm

/-- **Colour and weak units agree on the packet.** If a colour generator has the packet trace of a
weak generator, its fundamental trace is `1/2` exactly when the weak one's is. -/
theorem colour_unit_iff (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : (A * A).trace = 1 / 2)
    (hpk : (colourGen B * colourGen B).trace = (weakGen A * weakGen A).trace) :
    (B * B).trace = 1 / 2 := by
  rw [colour_trace_product, weak_trace_product, hA] at hpk
  linear_combination hpk / 4

/-- The colour Cartan along the root joining colours `0` and `1`. -/
def colourT3 : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1 / 2, -1 / 2, 0]

/-- `√3 · T₈`, the sum of the root Cartans joining colours `0, 2` and `1, 2`. -/
def colourT8s : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1 / 2, 1 / 2, -1]

/-- **A root's Cartan has the weak doublet's trace `1/2`.** -/
theorem colour_root_cartan : (colourT3 * colourT3).trace = 1 / 2 := by
  simp [colourT3, diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_three]
  norm_num

/-- **The eighth generator is fixed too:** `tr (√3 T₈)² = 3/2` and it is orthogonal to `T₃`. -/
theorem colour_eighth :
    (colourT8s * colourT8s).trace = 3 / 2 ∧ (colourT3 * colourT8s).trace = 0 := by
  constructor <;>
  · simp [colourT3, colourT8s, diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_three]
    norm_num

end PMConstants.ColourNormalization
