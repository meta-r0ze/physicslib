import PMConstants.Partition

/-!
# One rule for the gauge readouts: link stiffness proportional to refresh workload

Premise (refresh ledger). A gauge sector whose links are refreshed `W` times per cycle, each
refresh paying the local curvature cost at Paper I's common toll `c₀`, accumulates curvature
cost `c₀ W Σ(1 − cos θ)` per cycle (`refresh_ledger`). Its lattice stiffness is therefore
`β = c₀ W`, and with Paper II's D₄ normalization `β = 1/(2g²)` its coupling is
`g² = 1/(2c₀W)`.

* `mixing`, `electric`: two sectors with workloads `W`, `Y` have
  `g'²/(g² + g'²) = W/(W + Y)` and `g² g'²/(g² + g'²) = 1/(2c₀(W + Y))`.
* `paper_electroweak`: with `W = Δ = 43` (clock) and `W + Y = N_sys`, the rule reproduces all
  three electroweak readouts of the paper: `s = Δ/N_sys`, `g² = e²/s`, `g'² = e²/(1 − s)`.
  The matching condition `s = g'²/(g² + g'²)` becomes a consequence of the refresh ledger.
* `strong_workload`: the same rule gives `α_s/α = N_sys/W₃`. The paper's
  `α_s = (16η + 1/4)α` corresponds to `W₃ = N_sys/(16η + 1/4)`, which lies strictly between
  11 and 12 (`strong_workload_not_integer`). The strong formula is not of the electroweak
  form with an integer workload; one of the two needs revision.

Scope: the rule uses one normalization constant for every sector. Non-abelian Wilson
actions carry group factors (`β = 2N/g²` in the usual SU(N) convention) and hypercharge has
its own normalization; deriving those relative factors is part of the premise.
-/

noncomputable section
namespace PMConstants.GaugeStiffness
open PMConstants

theorem refresh_ledger (c₀ S : ℝ) (W : ℕ) :
    (∑ _k : Fin W, c₀ * S) = (c₀ * W) * S := by
  simp [Finset.sum_const]; ring

def gsq (β : ℝ) : ℝ := 1 / (2 * β)

theorem mixing {c W Y : ℝ} (hc : 0 < c) (hW : 0 < W) (hY : 0 < Y) :
    gsq (c*Y) / (gsq (c*W) + gsq (c*Y)) = W / (W + Y) := by
  unfold gsq; field_simp; ring

theorem electric {c W Y : ℝ} (hc : 0 < c) (hW : 0 < W) (hY : 0 < Y) :
    gsq (c*W) * gsq (c*Y) / (gsq (c*W) + gsq (c*Y)) = gsq (c*(W + Y)) := by
  unfold gsq; field_simp; ring

theorem paper_electroweak {c : ℝ} (hc : 0 < c) :
    let W : ℝ := 43
    let Y : ℝ := footprint - 43
    let e2 := gsq (c*(W + Y))
    gsq (c*Y) / (gsq (c*W) + gsq (c*Y)) = clockRatio ∧
      gsq (c*W) = e2 / clockRatio ∧ gsq (c*Y) = e2 / (1 - clockRatio) := by
  intro W Y e2
  have hF : (43 : ℝ) < footprint := by norm_num [footprint, overhead]
  have hY : 0 < Y := by simp only [Y]; linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [mixing hc (by norm_num) hY]
    simp only [W, Y, clockRatio]; ring_nf
  · simp only [e2, W, Y, gsq, clockRatio]
    have : footprint ≠ 0 := by linarith
    field_simp; ring_nf; field_simp
  · simp only [e2, W, Y, gsq, clockRatio]
    have h1 : footprint ≠ 0 := by linarith
    have h2 : footprint - 43 ≠ 0 := by linarith
    have h3 : (1 : ℝ) - 43/footprint = (footprint - 43)/footprint := by field_simp
    rw [h3]; field_simp; ring_nf; field_simp

/-- Under the rule, `α_s/α = N_sys/W₃`; the paper's strong formula needs this workload. -/
def strongWorkload : ℝ := footprint / (16*overhead + 1/4)

theorem strong_workload (α : ℝ) :
    strongCoupling α = α * (footprint / strongWorkload) := by
  have : (16*overhead + 1/4 : ℝ) ≠ 0 := by norm_num [overhead]
  have hf : footprint ≠ 0 := by norm_num [footprint, overhead]
  unfold strongWorkload strongCoupling; field_simp

theorem strong_workload_not_integer : 11 < strongWorkload ∧ strongWorkload < 12 := by
  norm_num [strongWorkload, footprint, overhead]

end PMConstants.GaugeStiffness
