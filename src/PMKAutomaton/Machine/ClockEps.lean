import PMKAutomaton.Machine.AxisHop

/-!
# The aligned clock in ε coordinates

`PMSubstrate.ChannelSymmetry` writes a `D₄` in ε coordinates.  Those
coordinates are not the clock.  In the aligned placement (`a,b,c` clock-silent,
`beta = e₂+e₃` reading `−1`) the clock reading of a spacetime `D₄` vector `ε`
is `21·(ε₀+ε₁+ε₂+ε₃) mod 43`, and it is silent exactly when `Σε = 0`.

This module sets up the ε → E8 lift through the aligned placement and proves
that formula on the 24 spacetime roots (`rootE8_clock`, `rootE8_silent`).  It
also proves that each coordinate axis `2eⱼ` reads `−1`, so it is not a spatial
step.  `AxisHop` states the hop on the clock-silent spatial axes; this file is
the clock side.
-/

noncomputable section
namespace PMAction.ClockEps
open PMKAutomaton.ClockRing
open PMKAutomaton.AlignedSectors
open PMSubstrate
open Matrix
open PMAction.AxisHop

/-- Inverse of `Channels.d4Basis` on even-sum vectors. -/
def d4FromEps (y : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![y 0, y 0 + y 1, (∑ i, y i) / 2 - y 3, (∑ i, y i) / 2]

/-- The aligned spacetime lift of a `D₄` ε vector. -/
def spacetimeE8 (y : Fin 4 → ℤ) : V :=
  alignedSectorBasis *ᵥ (fun i => if h : (i : ℕ) < 4 then d4FromEps y ⟨(i : ℕ), h⟩ else 0)

/-- The E8 lift of a `D₄` root. -/
def rootE8 (t : Tri) : V := spacetimeE8 (vec t)

/-- **The clock reading in ε coordinates.**  For a spacetime `D₄` root,
`clockReading = 21·Σε mod 43`. -/
theorem rootE8_clock : ∀ t : Tri, IsRoot t →
    clockReading (rootE8 t) = ((21 * ∑ i, val (t i) : ℤ) : ZMod 43) := by
  decide +kernel

/-- **Clock-silence is `Σε = 0`.** -/
theorem rootE8_silent : ∀ t : Tri, IsRoot t →
    (clockReading (rootE8 t) = 0 ↔ ∑ i, val (t i) = 0) := by
  decide +kernel

/-- **Each coordinate axis `2eⱼ` reads `−1` on the clock**, so it is not a
spatial step. -/
theorem two_epsAxis_reads (j : Fin 4) :
    clockReading (spacetimeE8 (fun i => 2 * epsAxis j i)) = -1 := by
  decide +kernel +revert

end PMAction.ClockEps
