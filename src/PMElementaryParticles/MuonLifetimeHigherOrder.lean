import PMElementaryParticles.MuonQEDLoops

/-!
# The muon lifetime with the full Fermi-theory QED series

`τ_μ = τ_tree / (1 + Δq⁽⁰⁾ + Δq⁽¹⁾ + Δq⁽²⁾)` with the E8 tree lifetime
(`PhysicalUnits.muonLifetimeSeconds`: E8 `G_F` and `m_μ`) and the loop terms of `MuonQEDLoops`.

* `lifetime_bounds`: `2.196974 µs < τ_μ < 2.196984 µs` (the one-loop
  `MuonLifetimeCorrected` row is `2.196987–2.196998`).
-/

noncomputable section
namespace PMElementaryParticles.MuonLifetimeHigherOrder

open PMElementaryParticles MuonQEDLoops

def lifetime : ℝ := PhysicalUnits.muonLifetimeSeconds / (1 + dq0 + dq1 + dq2)

theorem lifetime_bounds : (2.196974e-6 : ℝ) < lifetime ∧ lifetime < (2.196984e-6 : ℝ) := by
  have ht := PhysicalUnits.muonLifetimeSeconds_tight
  obtain ⟨p1, p2⟩ := dq0_bounds
  obtain ⟨q1, q2⟩ := dq1_bounds
  obtain ⟨s1, s2⟩ := dq2_bounds
  have hd1 : (0.995616037 : ℝ) < 1 + dq0 + dq1 + dq2 := by linarith
  have hd2 : 1 + dq0 + dq1 + dq2 < (0.995616067 : ℝ) := by linarith
  have hdpos : 0 < 1 + dq0 + dq1 + dq2 := by linarith
  unfold lifetime
  constructor
  · rw [lt_div_iff₀ hdpos]
    calc (2.196974e-6 : ℝ) * (1 + dq0 + dq1 + dq2) < 2.196974e-6 * 0.995616067 := by nlinarith
      _ < 2.187343e-6 := by norm_num
      _ < _ := ht.1
  · rw [div_lt_iff₀ hdpos]
    calc PhysicalUnits.muonLifetimeSeconds < 2.187352e-6 := ht.2
      _ < 2.196984e-6 * 0.995616037 := by norm_num
      _ < _ := by nlinarith

end PMElementaryParticles.MuonLifetimeHigherOrder
