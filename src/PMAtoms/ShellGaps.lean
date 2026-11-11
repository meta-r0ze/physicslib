import PMAtoms.ShellSystem
import PMSubstrate.Channels
import PMSubstrate.ChannelSymmetry
import PMElementaryParticles.QuarkMasses

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Shell gaps: which spin–orbit strength makes the magic numbers

`ShellSystem.e8OrbitalOrder` shows the E8 cost `2n+l − κ·l·s − (κ/D)·l(l+1)` with
`κ = χ/Δ = 2/43` puts the recorded orbitals in order. Order is not the same as closure: a magic
number is a **large gap** after it, and the mass, the shell correction and the α/fission
hindrances all depend on gap sizes.

**1. `κ = χ/Δ` makes the oscillator numbers the closures, not 28/50/82.**
(`shellSystem_gaps`, in units of `1/172` of `ℏω`.) The gaps after `20, 40, 70` are
`136, 112, 92`; after `28, 50, 82` they are only `28, 36, 44`. A Strutinsky check (outside
Lean) gives a *positive* shell correction at `N = 28, 50, 82`: with this strength those are
anti-magic. The ordering is right; the closures are the plain-oscillator ones `2, 8, 20, 40, 70`.

**2. The E8 Nilsson strengths already in `AlphaConfiguration` make the real closures.**
With `κ = 1/ν = 1/16`, `μ = χ/σ = 2/5` in the standard spherical Nilsson form

  `e = N + 3/2 − κ·(2 l·s + μ·(l(l+1) − ⟨l(l+1)⟩_N))`,  `⟨l(l+1)⟩_N = N(N+3)/2`

(`nilssonE8CostQ`), the largest gaps through `N = 7` are at `2, 8, 20, 28, 50, 82, 126`
(numerical check), for example `28: 3/8`, `50: 19/40`, `82: 23/40`, `126: 7/20` against
`40: 3/10` (`nilssonE8_gaps`). A Strutinsky check gives `δE ≈ −1.1 ℏω` at both `Z = 82` and
`N = 126`, about `−16` MeV for Pb-208 with `ℏω(208)`; standard microscopic values are
`−12` to `−14` MeV. This form breaks five near-degenerate pairs of the recorded textbook order
(for example `1g₇/₂`/`2d₅/₂`, `2d₃/₂`/`3s₁/₂`), which is where `l2_ratio_forced` got its ties.

**3. With the Nilsson form the smooth reference is the plain oscillator.** Both corrections
average to zero over a shell: `spinOrbit_trace_zero` (each `l` doublet) and
`l2_shell_average` (the subtracted `⟨l(l+1)⟩_N` is the shell mean). The oscillator degeneracy is
`(N+1)(N+2)` (`ho_degeneracy`). So the shell correction needs no smoothing width: it is the
ladder sum minus the oscillator's smooth energy.

**4. The α hindrance in the two forms.**
`AlphaConfiguration` uses `SingleParticle.nilssonEnergy`, which counts the radial `n` instead of
the shell `N`, gives `l(l+1)` a `+` sign and adds `−δ(2l − n)`. That formula puts `3s₁/₂`
(`N = 4`) above `2f₇/₂` (`N = 5`) (`nilssonEnergy_inverts_shells`). With the same E8
strengths in the standard form, the parent–daughter gaps become `15/16` (U-235) and `53/80`
(Pu-239) instead of `9/32` and `351/160` (`alpha_standard_gaps`), so the hindrance
`σ/(gap + 1/χ)` is `3.48` and `4.30` instead of the fitted `6.4` and `1.86`: the order of the two
is reversed. The observed hindrances match the first formula, not the second.

**5. Which substrate quantity sets the spin–orbit strength.** The two candidates read the
substrate differently:

* `χ/Δ` is the Governor pillar term (`ShellSystem.spinOrbitCoupling = −governorTerm`): a
  persistence credit per clock slot. Its role in the shell system is the **spacing**: it sets
  `ℏω(A)`. Nothing in it refers to spin.
* `1/ν` is one over the channel count. `ν = 16` is two of the three `D₄` glue classes, `8` minimal
  vectors each (`PMSubstrate.Channels.nu_eq`, `minimal_class_card`); the three classes are the
  vector `8_v` and the two spinors `8_s`, `8_c`. A spin–orbit term couples an orbital (vector)
  state to a spin (spinor) state, so its strength per channel is `1/ν` when the channel pair is
  vector ⊕ spinor (`nilssonKappa_eq_channel`). The substrate does not need to single that pair
  out: triality permutes the three classes as `S₃` (`ChannelSymmetry.pair_choice`), so every pair
  of distinct classes is equivalent to vector ⊕ spinor, and "orbital ⊕ spin" is a naming of
  whichever two classes carry the flow. Within one sector the symmetries (Weyl reflections and
  the triality map `hada`, no sector swap) reach all `ν = 16` channels from any one
  (`sector_orbit`, `sector_channels_card`), so a symmetric per-channel weight in a sector is
  `1/ν`. What stays a reading, not a theorem: that spin–orbit *is* a uniform coupling across the
  flow channels of the coordinate sector. `1/ν` is not one of the six pillar terms.
* `μ = χ/σ` is the same ratio as the bottom-quark latency leak
  (`QuarkMasses.latencyRatio`; `nilssonMu_eq_latency`): boundary `χ` over embedding `σ`.

So the substrate has a pillar for the spacing (Governor) and a channel count for spin–orbit, and
the comparison picks the second for spin–orbit (§2). Measured comparison (outside Lean): the
`d₅/₂–d₃/₂` splitting in O-17 is `5.08` MeV; `2κ(l+½)·ℏω(17)` gives `5.29` MeV with `κ = 1/ν` and
`1.97` MeV with `χ/Δ` (as `ShellSystem` uses it, `κ(l+½)·ℏω`). The `p₁/₂–p₃/₂` splitting in N-15 is
`6.32` MeV; the two give `3.32` and `1.23` MeV.

What this does **not** settle: the gap sizes are checked here, but which orbitals are adjacent
in the full sorted spectrum is a numerical check, not a Lean theorem.
-/

namespace PMAtoms

/-! ## 1. `κ = χ/Δ`: gaps in `1/172` units -/

/-- Gaps after `20, 28, 40, 50, 70, 82` with the `ShellSystem` cost `orbitalCostZ`
(adjacent orbitals of the recorded order). -/
theorem shellSystem_gaps :
    orbitalCostZ ⟨1, 3, 7, 8⟩ - orbitalCostZ ⟨1, 2, 3, 4⟩ = 136 ∧   -- after 20
    orbitalCostZ ⟨2, 1, 3, 4⟩ - orbitalCostZ ⟨1, 3, 7, 8⟩ = 28 ∧    -- after 28
    orbitalCostZ ⟨1, 4, 9, 10⟩ - orbitalCostZ ⟨2, 1, 1, 2⟩ = 112 ∧  -- after 40
    orbitalCostZ ⟨1, 4, 7, 8⟩ - orbitalCostZ ⟨1, 4, 9, 10⟩ = 36 ∧   -- after 50
    orbitalCostZ ⟨1, 5, 11, 12⟩ - orbitalCostZ ⟨3, 0, 1, 2⟩ = 92 ∧  -- after 70
    orbitalCostZ ⟨1, 5, 9, 10⟩ - orbitalCostZ ⟨1, 5, 11, 12⟩ = 44 := by  -- after 82
  decide

/-- With `κ = χ/Δ` the oscillator closures beat the spin–orbit closures pairwise:
`28 < 20`, `50 < 40`, `82 < 70` in gap size. -/
theorem shellSystem_oscillator_closures_dominate :
    orbitalCostZ ⟨2, 1, 3, 4⟩ - orbitalCostZ ⟨1, 3, 7, 8⟩ <
      orbitalCostZ ⟨1, 3, 7, 8⟩ - orbitalCostZ ⟨1, 2, 3, 4⟩ ∧
    orbitalCostZ ⟨1, 4, 7, 8⟩ - orbitalCostZ ⟨1, 4, 9, 10⟩ <
      orbitalCostZ ⟨1, 4, 9, 10⟩ - orbitalCostZ ⟨2, 1, 1, 2⟩ ∧
    orbitalCostZ ⟨1, 5, 9, 10⟩ - orbitalCostZ ⟨1, 5, 11, 12⟩ <
      orbitalCostZ ⟨1, 5, 11, 12⟩ - orbitalCostZ ⟨3, 0, 1, 2⟩ := by
  decide

/-! ## 2. E8 Nilsson strengths -/

/-- Oscillator shell `N = 2(n−1) + l` (radial `n` counted from `1`). -/
def hoShell (o : NuclearOrbital) : ℕ := 2 * (o.n - 1) + o.l

/-- Spherical Nilsson energy in `ℏω` with the E8 strengths `κ = 1/ν = 1/16`, `μ = χ/σ = 2/5`
(the `AlphaConfiguration` values): `N + 3/2 − κ(2 l·s + μ(l(l+1) − N(N+3)/2))`. -/
def nilssonE8CostQ (o : NuclearOrbital) : ℚ :=
  (hoShell o : ℚ) + 3 / 2 -
    (1 / 16) * (2 * spinOrbitQ o +
      (2 / 5) * ((o.l : ℚ) * ((o.l : ℚ) + 1) -
        (hoShell o : ℚ) * ((hoShell o : ℚ) + 3) / 2))

/-- Gaps after `20, 28, 40, 50, 82, 126` in the E8 Nilsson spectrum (adjacent orbitals of the
sorted spectrum). -/
theorem nilssonE8_gaps :
    nilssonE8CostQ ⟨1, 3, 7, 8⟩ - nilssonE8CostQ ⟨1, 2, 3, 4⟩ = 23 / 40 ∧   -- after 20
    nilssonE8CostQ ⟨2, 1, 3, 4⟩ - nilssonE8CostQ ⟨1, 3, 7, 8⟩ = 3 / 8 ∧     -- after 28
    nilssonE8CostQ ⟨1, 4, 9, 10⟩ - nilssonE8CostQ ⟨2, 1, 1, 2⟩ = 3 / 10 ∧   -- after 40
    nilssonE8CostQ ⟨2, 2, 5, 6⟩ - nilssonE8CostQ ⟨1, 4, 9, 10⟩ = 19 / 40 ∧  -- after 50
    nilssonE8CostQ ⟨2, 3, 7, 8⟩ - nilssonE8CostQ ⟨1, 5, 11, 12⟩ = 23 / 40 ∧ -- after 82
    nilssonE8CostQ ⟨2, 4, 9, 10⟩ - nilssonE8CostQ ⟨3, 1, 1, 2⟩ = 7 / 20 := by  -- after 126
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [nilssonE8CostQ, hoShell, spinOrbitQ]

/-- In the E8 Nilsson spectrum the spin–orbit closures `28` and `50` beat the oscillator
closure `40`. -/
theorem nilssonE8_spinOrbit_closures :
    nilssonE8CostQ ⟨1, 4, 9, 10⟩ - nilssonE8CostQ ⟨2, 1, 1, 2⟩ <
      nilssonE8CostQ ⟨2, 1, 3, 4⟩ - nilssonE8CostQ ⟨1, 3, 7, 8⟩ ∧
    nilssonE8CostQ ⟨1, 4, 9, 10⟩ - nilssonE8CostQ ⟨2, 1, 1, 2⟩ <
      nilssonE8CostQ ⟨2, 2, 5, 6⟩ - nilssonE8CostQ ⟨1, 4, 9, 10⟩ := by
  obtain ⟨_, h28, h40, h50, _, _⟩ := nilssonE8_gaps
  rw [h28, h40, h50]
  norm_num

/-! ## 3. The smooth reference is the plain oscillator -/

/-- Degeneracy of oscillator shell `N` (spin included): `Σ_{l ≡ N mod 2} 2(2l+1)`. -/
def hoDegeneracy (N : ℕ) : ℕ :=
  (((List.range (N + 1)).filter (fun l => l % 2 = N % 2)).map (fun l => 2 * (2 * l + 1))).sum

theorem ho_degeneracy : ∀ N < 8, hoDegeneracy N = (N + 1) * (N + 2) := by decide

/-- Degeneracy-weighted `l(l+1)` over shell `N`. -/
def hoL2Sum (N : ℕ) : ℕ :=
  (((List.range (N + 1)).filter (fun l => l % 2 = N % 2)).map
    (fun l => 2 * (2 * l + 1) * (l * (l + 1)))).sum

/-- The shell mean of `l(l+1)` is `N(N+3)/2`, the value `nilssonE8CostQ` subtracts. -/
theorem l2_shell_average : ∀ N < 8, 2 * hoL2Sum N = (N + 1) * (N + 2) * (N * (N + 3)) := by
  decide

/-- Spin–orbit averages to zero over each `l` doublet: `j = l ± 1/2` weighted by `2j+1`. -/
theorem spinOrbit_trace_zero (n l : ℕ) :
    (2 * (l : ℚ) + 4) * spinOrbitQ ⟨n, l + 1, 2 * l + 3, 0⟩ +
      (2 * (l : ℚ) + 2) * spinOrbitQ ⟨n, l + 1, 2 * l + 1, 0⟩ = 0 := by
  unfold spinOrbitQ
  push_cast
  ring

/-! ## 4. The α configuration fit and the standard form -/

/-- The `SingleParticle.nilssonEnergy` formula used by `AlphaConfiguration` puts `3s₁/₂` above
`2f₇/₂`, against the oscillator order (`hoShell` `4 < 5`). -/
theorem nilssonEnergy_inverts_shells :
    hoShell ⟨3, 0, 1, 2⟩ < hoShell ⟨2, 3, 7, 8⟩ ∧
    nilssonEnergy (1 / 16) (2 / 5) (1 / 5) ⟨2, 3, 7, 8⟩ <
      nilssonEnergy (1 / 16) (2 / 5) (1 / 5) ⟨3, 0, 1, 2⟩ := by
  refine ⟨by decide, ?_⟩
  norm_num [nilssonEnergy, spinOrbit]

/-- Parent–daughter gaps of the two odd-A α transitions in the standard E8 Nilsson form:
U-235 `2f₇/₂ → 2d₅/₂` and Pu-239 `3s₁/₂ → 2f₇/₂`. -/
theorem alpha_standard_gaps :
    nilssonE8CostQ ⟨2, 3, 7, 8⟩ - nilssonE8CostQ ⟨2, 2, 5, 6⟩ = 15 / 16 ∧
    nilssonE8CostQ ⟨2, 3, 7, 8⟩ - nilssonE8CostQ ⟨3, 0, 1, 2⟩ = 53 / 80 := by
  refine ⟨?_, ?_⟩ <;> norm_num [nilssonE8CostQ, hoShell, spinOrbitQ]

/-! ## 5. Substrate readings of the strengths -/

/-- The Nilsson spin–orbit strength `1/16` is one over the substrate channel count `ν`. -/
theorem nilssonKappa_eq_channel : (1 / 16 : ℚ) = 1 / (PMSubstrate.Channels.nu : ℚ) := by
  rw [PMSubstrate.Channels.nu_eq]; norm_num

/-- The Nilsson `l²` ratio `μ = 2/5` is the latency ratio `χ/σ` of the quark ledger. -/
theorem nilssonMu_eq_latency : (2 / 5 : ℝ) = PMElementaryParticles.QuarkMasses.latencyRatio := by
  unfold PMElementaryParticles.QuarkMasses.latencyRatio
  norm_num [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq]

/-- Channel indices reachable from channel `0` with the generators of one sector: the four
reflections of each sector and `hada`, without the sector swap (`gen 9`). -/
def sectorReach : ℕ → Finset (Fin 32)
  | 0 => {0}
  | n + 1 => Finset.univ.filter fun k => k ∈ sectorReach n ∨
      ∃ i : Fin 10, i.val < 9 ∧ ∃ j ∈ sectorReach n, PMSubstrate.ChannelSymmetry.genTable i j = k

/-- **One sector's symmetries act transitively on its `ν = 16` channels.** Without the sector
swap, channel `0` reaches exactly the channels of its own sector. -/
theorem sector_orbit :
    sectorReach 12 =
      Finset.univ.filter fun k => (PMSubstrate.ChannelSymmetry.chanTable k).1 = false := by
  decide +kernel

theorem sector_channels_card :
    (Finset.univ.filter fun k : Fin 32 =>
      (PMSubstrate.ChannelSymmetry.chanTable k).1 = false).card = 16 := by
  decide +kernel

end PMAtoms
