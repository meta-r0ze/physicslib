import PMAction.RunningCoefficients
import PMAction.ContactMatching
import PMConstants.ReferenceMasses
import PMConstants.RunningLinks

/-!
# Paper II's dynamics applied to Paper III's derived content

**Running coefficients of the derived content.** The per-generation Weyl indices are the packet
traces already proved in `PacketTraceForm`: `tr(T₃²) = 2` for `SU(2)`, `tr(T₃^{colour}²) = 2` for
`SU(3)` and `tr((Y/2)²) = 10/3` for hypercharge (`weak_index`, `colour_index`,
`PacketTraceForm.hyper_trace_square`). With three generations (`Generations.three_pairs`) and the
one link doublet of hypercharge `1` (`ReferenceLink`), whose scalar indices are `1/2` for `SU(2)`
and `2·(1/2)² = 1/2` for hypercharge:

* `standard_coefficients`: `b₃ = 7`, `b₂ = 19/6`, `b_Y = -41/6`, from
  `PMAction.RunningCoefficients.bContent`.

**The Fermi constant from W exchange.** `ReferenceMasses.charged_entry` gives `⟨T₁²⟩ = 1/4` on the
reference, so `m_W² = g²v²·⟨T₁²⟩ = g²v²/4`.

* `fermi_from_reference`: with Paper II's contact matching (`ContactMatching.fermi_from_mass`),
  `G_F = √2 g²/(8m_W²) = 1/(√2 v²)`. The `√2` and the `1/v²` come from the reference's mass
  entry and the low-momentum exchange, not from a projection argument.
-/

noncomputable section
namespace PMConstants.MatterRunning
open PMConstants Matrix PacketTraceForm PMAction.RunningCoefficients

theorem weak_index :
    (weakGen !![(1 / 2 : ℂ), 0; 0, -1 / 2] * weakGen !![(1 / 2 : ℂ), 0; 0, -1 / 2]).trace = 2 := by
  rw [weak_trace_product]
  simp [Matrix.trace, Fin.sum_univ_two]; norm_num

theorem colour_index :
    (colourGen (diagonal ![(1 / 2 : ℂ), -1 / 2, 0]) * colourGen (diagonal ![(1 / 2 : ℂ), -1 / 2, 0])).trace
      = 2 := by
  rw [colour_trace_product]
  simp [Matrix.trace, Fin.sum_univ_three, diagonal_mul_diagonal]; norm_num

/-- **The Standard Model one-loop coefficients from the derived content.** -/
theorem standard_coefficients :
    bContent 3 (3 * 2) 0 = 7 ∧ bContent 2 (3 * 2) (1 / 2) = 19 / 6 ∧
      bContent 0 (3 * (10 / 3)) (2 * (1 / 2) ^ 2) = -41 / 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [bContent_formula] <;> norm_num

/-- The W mass squared read on the reference. -/
def mWsq (g v : ℝ) : ℝ := g ^ 2 * v ^ 2 * ((ReferenceMasses.t1 * ReferenceMasses.t1)
  (ReferenceAnchor.lepton 0) (ReferenceAnchor.lepton 0)).re

theorem mWsq_eq (g v : ℝ) : mWsq g v = g ^ 2 * v ^ 2 / 4 := by
  rw [mWsq, ReferenceMasses.charged_entry]; norm_num; ring

/-- **The Fermi constant from the reference and W exchange.** -/
theorem fermi_from_reference (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    Real.sqrt 2 * (g ^ 2 / (8 * mWsq g v)) = 1 / (Real.sqrt 2 * v ^ 2) := by
  have h := PMAction.ContactMatching.fermi_from_mass g v (Real.sqrt (mWsq g v)) hg hv
    (by rw [Real.sq_sqrt (by rw [mWsq_eq]; positivity), mWsq_eq])
  rwa [Real.sq_sqrt (by rw [mWsq_eq]; positivity)] at h

end PMConstants.MatterRunning
