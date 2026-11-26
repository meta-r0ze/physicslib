import PMConstants.TableConsequences
import PMConstants.ReferenceDirections
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Where each readout is matched

The derived couplings are compared with data at different scales: `α` at zero momentum, the weak
mixing on shell (`m_W/m_Z`), `α_s` at `M_Z`. The persistence reading is that a readout is matched
where it is maintained.

**Which broken direction reads the payload.** Colour's ledger is a ratio to the electroweak
footprint through the payload, which hypercharge also refreshes (`RequirementComplement`). Reading
payload must not change its electric charge, since `Q` is the unbroken, conserved readout; and it
must be a direction that reads the reference at all, i.e. a broken one.
* `commutes_iff`: a real electroweak generator `gen a z b` commutes with `Q` exactly when `z = 0`.
* `neutral_broken_iff`: it commutes with `Q` and moves the reference exactly when `z = 0` and
  `a ≠ b/2`: one real direction, the `Z`. The other broken directions (`z ≠ 0`) carry charge (`W±`)
  and the unbroken one is `Q` (the photon).
So the `Z` is the unique structural candidate for the payload comparison. That the matching scale
is its mass is a premise; the test below supports it against the other reference-generated
scales. Likewise the electric readout at zero momentum and the weak mixing on the `W/Z` shell are
the readings this principle suggests, not derived matching rules.

**Test against the alternatives.** If the colour formula `0.11799 < A < 0.11800`
(`ColourReference.strong_from_payload`) is `α_s(μ)`, one-loop running with five flavours
(`b₀ = 23/3`) gives the implied `α_s(M_Z) = 1/(1/A - (b₀/2π) log(μ/M_Z))`, compared with
the e8p strong-coupling reference:
* `at_Z`: `μ = M_Z` gives `A` itself, within `0.012σ`;
* `at_W`: `μ = M_W` implies `α_s(M_Z) < 0.1162`, more than `2σ` low;
* `at_H`: `μ = m_H` implies `> 0.1227`, more than `5σ` high;
* `at_v`: `μ = v` implies `> 0.1296`, more than `12σ` high.
Among the scales the reference generates, only the `Z` fits. One-loop, five-flavour running is a
stated approximation (the top threshold matters only for `v`, where the exclusion is large).

The measured comparison proofs are in `tools/e8p/E8PConstants/PMConstants/ScaleComparisons.lean`.
-/

noncomputable section
namespace PMConstants.ReadoutScales
open PMConstants Matrix GeneratorNormalization PacketTraceForm ReferenceAnchor ReferenceStabilizer
  ReferenceDirections

lemma gen_diag_entries (a : ℝ) (z : ℂ) (b : ℝ) :
    gen a z b (lepton 1) (lepton 0) = z ∧ gen a z b (lepton 0) (lepton 1) = star z := by
  simp [gen, weak_lepton, hyper_lepton]

/-- **Commuting with `Q` means no charged component.** -/
theorem commutes_iff (a : ℝ) (z : ℂ) (b : ℝ) :
    gen a z b * (t3 + hyperGen) = (t3 + hyperGen) * gen a z b ↔ z = 0 := by
  have hQ := (ReferenceRestoration.t3_isDiag.add ReferenceRestoration.hyper_isDiag)
  constructor
  · intro h
    have e := congrFun (congrFun h (lepton 1)) (lepton 0)
    rw [← hQ.diagonal_diag, mul_diagonal, diagonal_mul] at e
    simp only [Matrix.diag] at e
    rw [reference_charges.1, reference_charges.2, (gen_diag_entries a z b).1] at e
    linear_combination e
  · rintro rfl
    have hg : (gen a 0 b).IsDiag := by
      unfold gen
      refine IsDiag.add ?_ (ReferenceRestoration.hyper_isDiag.smul _)
      unfold weakGen PacketGaugeActions.block
      have hA : (!![(a : ℂ), star (0 : ℂ); 0, -(a : ℂ)]).IsDiag := by
        intro i j h; fin_cases i <;> fin_cases j <;> simp_all
      exact (isDiag_one.kronecker hA).fromBlocks (isDiag_zero.fromBlocks (hA.fromBlocks isDiag_zero))
    rw [← hg.diagonal_diag, ← hQ.diagonal_diag, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext c; ring

/-- **The neutral broken direction is unique: the `Z`.** -/
theorem neutral_broken_iff (a : ℝ) (z : ℂ) (b : ℝ) :
    (gen a z b * (t3 + hyperGen) = (t3 + hyperGen) * gen a z b ∧ ¬ Fixes (gen a z b) (lepton 0)) ↔
      z = 0 ∧ a ≠ b / 2 := by
  rw [commutes_iff, fixes_iff]
  simp only [displacement, Prod.mk_eq_zero, not_and_or]
  constructor
  · rintro ⟨rfl, h | h⟩
    · exact ⟨rfl, fun e => h (by rw [e]; ring)⟩
    · exact absurd rfl h
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, Or.inl fun e => h (by linarith)⟩

/-- The `α_s(M_Z)` implied if the colour value `A` is read at `μ` (one loop, five flavours). -/
def implied (zAnchor A μ : ℝ) : ℝ := 1 / (1 / A - 23 / (6 * Real.pi) * Real.log (μ / zAnchor))

lemma b_bounds : 23 / (6 * 3.15) < 23 / (6 * Real.pi) ∧ 23 / (6 * Real.pi) < 23 / (6 * 3.14) := by
  have h1 := Real.pi_gt_d2; have h2 := Real.pi_lt_d2
  constructor <;> apply div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)

end PMConstants.ReadoutScales
