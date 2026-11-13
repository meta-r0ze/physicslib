import PMHadrons.AxialCount
import PMHadrons.MesonMasses
import PMElementaryParticles.LeptonMasses
import Mathlib.Tactic

/-! **Construction.** The three-carrier spin–flavour algebra behind the nucleon's pion dressing,
and the Margin signs of the persistent hadrons.

Three carriers in one spatial orbital, each with a spin bit and a `u/d` label, symmetric in
spin ⊗ label (`AxialCount`), span the nucleon (`S = I = ½`) and the Δ (`S = I = 3/2`). With
`G^{ia} = Σ_q σ^i_q τ^a_q / 4`, exact rational computation on the 64 states gives:

* `sumG2_proton`, `sumG2_delta`: `Σ_{ia} G^{ia}G^{ia}` is `57/16` on the nucleon (`protonLit`,
  equal to `AxialCount.proton` by `protonLit_eq`) and `33/16` on the Δ. A static pion self-energy `−K Σ G²` therefore lowers the nucleon below the Δ by `(3/2)K`.
* The double-commutator identities (`dc_full`, `dc_nucleon_only`: the Δ keeps `9/25` of the
  nucleon-only cubic term) are in `tools/slow/SpinFlavourDC.lean`, kept out of the default build
  because the kernel computation is slow (`lake env lean tools/slow/SpinFlavourDC.lean`).

* `neutron_margin_pos`, `pion_margin_pos`: the neutron lies above `p + e` and the charged pion
  above the muon (E8 masses, `m_e` units), so both persist against strong decay and decay only
  through the Toll boundary (`PMHadrons/PILLARS.md`).
-/

namespace PMHadrons.SpinFlavour
open PMHadrons.AxialCount

/-! ## `Σ G²` from carrier swaps

`Σ_{ia} G^{ia}G^{ia} = (1/16) Σ_{q,r} (σ_q·σ_r)(τ_q·τ_r)`, with `σ_q·σ_q = τ_q·τ_q = 3` and, for
`q ≠ r`, `σ_q·σ_r = 2P^σ_{qr} − 1`, `τ_q·τ_r = 2P^τ_{qr} − 1`. Since `P^σ P^τ` is the full swap `P`,
`(2P^σ − 1)(2P^τ − 1) = 4P − 2P^σ − 2P^τ + 1`, so over the three unordered pairs

`Σ G² = (1/16)(33 + 2 Σ_{q<r} (4P_{qr} − 2P^σ_{qr} − 2P^τ_{qr}))`.

Each swap is applied directly to an explicit vector (the proton as a literal list, checked equal
to `AxialCount.proton`), which keeps the kernel computation shallow. -/

/-- Swap carriers `q` and `r` entirely. -/
def swapFull (q r : ℕ) (v : Vec) : Vec :=
  (List.range 64).map fun x => get v (setc (setc x q (car x r)) r (car x q))

/-- Swap the spin bits of carriers `q` and `r` (labels stay). -/
def swapSpin (q r : ℕ) (v : Vec) : Vec :=
  (List.range 64).map fun x =>
    get v (setc (setc x q (2 * (car x r / 2) + car x q % 2)) r (2 * (car x q / 2) + car x r % 2))

/-- Swap the `u/d` labels of carriers `q` and `r` (spins stay). -/
def swapLabel (q r : ℕ) (v : Vec) : Vec :=
  (List.range 64).map fun x =>
    get v (setc (setc x q (2 * (car x q / 2) + car x r % 2)) r (2 * (car x r / 2) + car x q % 2))

/-- The pair terms `8P − 4P^σ − 4P^τ` for one unordered pair. -/
def pairTerm (q r : ℕ) (v : Vec) : Vec :=
  vadd (vadd (smul 8 (swapFull q r v)) (swapSpin q r v) (-4)) (swapLabel q r v) (-4)

/-- `Σ_{ia} G^{ia}G^{ia}`. -/
def sumG2 (v : Vec) : Vec :=
  smul (1 / 16) (vadd (vadd (vadd (smul 33 v) (pairTerm 0 1 v) 1) (pairTerm 0 2 v) 1)
    (pairTerm 1 2 v) 1)

/-- The proton (spin up) as an explicit list. -/
def protonLit : Vec :=
  [0, 0, 0, 4, 0, 0, -2, 0, 0, -2, 0, 0, 4, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
    0, -2, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem protonLit_eq : protonLit = proton := by decide +kernel

/-- **`Σ G² = 57/16` on the nucleon.** -/
theorem sumG2_proton : sumG2 protonLit = smul (57 / 16) protonLit := by decide +kernel

/-- **`Σ G² = 33/16` on the Δ** (`u↑u↑u↑`). -/
theorem sumG2_delta : sumG2 (ket3 0 0 0) = smul (33 / 16) (ket3 0 0 0) := by decide +kernel

/-! ## Margin signs -/

/-- **The neutron lies above `p + e`** (`m_n − m_p − m_e > 0`, `m_e` units). -/
theorem neutron_margin_pos : 1 < CompositeMasses.neutron - CompositeMasses.proton := by
  have hn := CompositeMasses.neutron_value
  have hp := CompositeMasses.proton_value
  linarith [hn.1, hp.2]

/-- **The charged pion lies above the muon** (`m_π − m_μ > 0`, `m_e` units). -/
theorem pion_margin_pos :
    PMElementaryParticles.LeptonMasses.muon < MesonMasses.pionPlus := by
  have hπ := MesonMasses.pionPlus_value
  have hμ := PMElementaryParticles.LeptonMasses.muon_value
  linarith [hπ.1, hμ.2]

end PMHadrons.SpinFlavour
