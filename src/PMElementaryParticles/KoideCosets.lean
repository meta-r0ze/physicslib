import PMKAutomaton.ClockAlignment
import PMElementaryParticles.KoideSplit

/-!
# Koide fairness of the coset lazy walks

One tick is one root event, and all root events weigh the same
(`PMKAutomaton.ClockTickWeights`). Restricted to the clock-local roots of one
glue coset, a tick either stays (clock-silent root) or moves one site forward
(`+1`) or back (`−1`). The forward and back counts are equal in every coset, so
the walk's amplitude operator on three sites is a Hermitian circulant
(`KoideSplit.circulantSpectrum`) with stay weight `s/(s+2f)` and move weight
`f/(s+2f)` per direction.

By `KoideSplit.lazyWalk_koide_iff` the walk meets Koide (`Q = 2/3`) iff `s = 2f`.
The certified clock signatures give:

* conjugate spinor `(1,0)`: `s = 8`, `f = 4`: Koide-fair (`cospinor_walk_koide`);
* vector `(0,1)`: `s = 2`, `f = 7`: not fair (`vector_walk_not_koide`);
* spinor `(1,1)`: `s = 0`: no stay at all (`spinor_no_stay`).

The conjugate spinor is also the one coset whose silent roots are internal and
whose `+1` roots equal the spacetime ring step (`ClockPlaneProjection.cospinor_silent`,
`cospinor_plus`), so its local roots split cleanly into pure stays and pure ring
steps.

What this does **not** show: that the three-generation register's stay/move
amplitudes are those of this walk. That identification is open (EP TODO).
-/

noncomputable section

namespace PMElementaryParticles.KoideCosets

open PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment PMElementaryParticles.KoideSplit

/-- Clock-local roots of a coset that stay (clock-silent). -/
def stayCount (k : ZMod 2 × ZMod 2) : ℕ :=
  ((rootsOfKey k).filter fun r => clockReading r = 0).length

/-- Clock-local roots of a coset that move one site forward. -/
def fwdCount (k : ZMod 2 × ZMod 2) : ℕ :=
  ((rootsOfKey k).filter fun r => clockReading r = 1).length

/-- Clock-local roots of a coset that move one site back. -/
def backCount (k : ZMod 2 × ZMod 2) : ℕ :=
  ((rootsOfKey k).filter fun r => clockReading r = -1).length

theorem cospinor_counts : stayCount (1, 0) = 8 ∧ fwdCount (1, 0) = 4 ∧ backCount (1, 0) = 4 :=
  ⟨conjugateSpinorRoots_counts.2.2, conjugateSpinorRoots_counts.1,
    conjugateSpinorRoots_counts.2.1⟩

theorem vector_counts : stayCount (0, 1) = 2 ∧ fwdCount (0, 1) = 7 ∧ backCount (0, 1) = 7 :=
  ⟨vectorRoots_counts.2.2, vectorRoots_counts.1, vectorRoots_counts.2.1⟩

theorem spinor_counts : stayCount (1, 1) = 0 ∧ fwdCount (1, 1) = 4 ∧ backCount (1, 1) = 4 :=
  ⟨spinorRoots_counts.2.2, spinorRoots_counts.1, spinorRoots_counts.2.1⟩

/-- Forward and back weights are equal in every coset: the walk is Hermitian. -/
theorem fwd_eq_back :
    fwdCount (1, 0) = backCount (1, 0) ∧ fwdCount (0, 1) = backCount (0, 1) ∧
      fwdCount (1, 1) = backCount (1, 1) := by
  rw [cospinor_counts.2.1, cospinor_counts.2.2, vector_counts.2.1, vector_counts.2.2,
    spinor_counts.2.1, spinor_counts.2.2]
  exact ⟨rfl, rfl, rfl⟩

/-- **The conjugate-spinor lazy walk is Koide-fair**, for every phase of the
move amplitude. -/
theorem cospinor_walk_koide (u w : ℝ)
    (huw : u ^ 2 + w ^ 2 =
      (fwdCount (1, 0) : ℝ) / ((stayCount (1, 0) : ℝ) + 2 * (fwdCount (1, 0) : ℝ))) :
    koideQ (circulantSpectrum
      (Real.sqrt ((stayCount (1, 0) : ℝ) /
        ((stayCount (1, 0) : ℝ) + 2 * (fwdCount (1, 0) : ℝ)))) u w) = 2 / 3 := by
  obtain ⟨h1, h2, -⟩ := cospinor_counts
  refine (lazyWalk_koide_iff (stayCount (1, 0) : ℝ) (fwdCount (1, 0) : ℝ) u w ?_ ?_ huw).2 ?_
  · rw [h1]; norm_num
  · positivity
  · rw [h1, h2]; norm_num

/-- The vector-coset lazy walk is not Koide-fair (`s = 2`, `f = 7`). -/
theorem vector_walk_not_koide (u w : ℝ)
    (huw : u ^ 2 + w ^ 2 =
      (fwdCount (0, 1) : ℝ) / ((stayCount (0, 1) : ℝ) + 2 * (fwdCount (0, 1) : ℝ))) :
    koideQ (circulantSpectrum
      (Real.sqrt ((stayCount (0, 1) : ℝ) /
        ((stayCount (0, 1) : ℝ) + 2 * (fwdCount (0, 1) : ℝ)))) u w) ≠ 2 / 3 := by
  obtain ⟨h1, h2, -⟩ := vector_counts
  intro hk
  have := (lazyWalk_koide_iff (stayCount (0, 1) : ℝ) (fwdCount (0, 1) : ℝ) u w
    (by rw [h1]; norm_num) (by positivity) huw).1 hk
  rw [h1, h2] at this
  norm_num at this

/-- The spinor coset has no clock-silent root: its walk never stays. -/
theorem spinor_no_stay : stayCount (1, 1) = 0 := spinor_counts.1

end PMElementaryParticles.KoideCosets

end
