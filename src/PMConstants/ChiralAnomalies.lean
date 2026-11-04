import PMConstants.SectorLinks

/-!
# Gauge anomalies of the two-sector assignment

With left-handed states on one D₄ sector (`Q`: 6 states, `L`: 2) and right-handed states on
the other (`u`, `d`: 3 each, `e`, `ν`: 1 each), a chiral gauge theory is consistent only if
every gauge anomaly cancels between the sectors (left minus right, `Q = T₃ + Y/2`).

* `flux_is_linear_anomalies`: Paper III's flux premise is exactly the three linear anomaly
  conditions: gravitational–`U(1)`, `SU(3)²U(1)` and `SU(2)²U(1)`.
* `color_vectorlike`, `witten_even`: two left and two right colour triplets cancel `SU(3)³`;
  four doublets per generation avoid the global `SU(2)` anomaly.
* `forced_anomaly_free`: the charges forced by flux, one unit-hypercharge link and a neutral
  sterile channel also cancel the cubic `U(1)³` anomaly, which was not assumed.
-/

namespace PMConstants.ChiralAnomalies
open Hypercharge

def gravU1 (Y : Charges) : ℚ := 6*Y.q + 2*Y.l - 3*Y.u - 3*Y.d - Y.e - Y.n
def colorU1 (Y : Charges) : ℚ := 2*Y.q - Y.u - Y.d
def weakU1 (Y : Charges) : ℚ := 3*Y.q + Y.l

theorem flux_is_linear_anomalies (Y : Charges) :
    Flux Y ↔ weakU1 Y = 0 ∧ colorU1 Y = 0 ∧ gravU1 Y = 0 := by
  unfold Flux weakU1 colorU1 gravU1
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩

/-- Left triplets (the quark doublet's two isospin states) minus right triplets (`u`, `d`). -/
theorem color_vectorlike : (2 : ℤ) - (1 + 1) = 0 := by norm_num

/-- Doublets per generation: three colours of `Q` and one `L`. -/
theorem witten_even : Even (3 + 1 : ℕ) := by decide

theorem forced_anomaly_free (Y : Charges) (hf : Flux Y) (hl : SectorLinks.OneLink Y 1)
    (hn : Y.n = 0) :
    weakU1 Y = 0 ∧ colorU1 Y = 0 ∧ gravU1 Y = 0 ∧ cubic Y = 0 := by
  have hs := SectorLinks.forced_by_links Y hf hl hn
  obtain ⟨a, b, c⟩ := (flux_is_linear_anomalies Y).mp hf
  refine ⟨a, b, c, ?_⟩
  rw [hs]; norm_num [cubic, standard]

end PMConstants.ChiralAnomalies
