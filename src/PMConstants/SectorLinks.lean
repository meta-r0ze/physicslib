import PMConstants.Hypercharge

/-!
# The inter-sector link is the scalar doublet

In the two-sector domain wall (Paper II, `DomainWall`) the left-handed states live on one
D₄ sector and the right-handed states on the other, and the fermion hops between them.
Gauge covariance makes each hop carry a link field whose hypercharge is the difference of
the two endpoints (with `Q = T₃ + Y/2`).

* `links_iff_yukawa`: the four hops (`Q → u`, `Q → d`, `L → e`, `L → ν`) can all be carried by
  one field of hypercharge `h` and its conjugate, in the up/down pattern, exactly when Paper III's
  `Yukawa Y h` premise holds. The Yukawa premise is the gauge-covariance condition of the
  domain-wall hop.
* `standard_links`: for the forced charges every hop carries `|ΔY| = 1`: one scalar of unit
  hypercharge, which is also a weak doublet because the left-handed sector is.
-/

namespace PMConstants.SectorLinks
open Hypercharge

/-- Hop charges: right-handed endpoint minus left-handed endpoint. -/
def hops (Y : Charges) : ℚ × ℚ × ℚ × ℚ := (Y.u - Y.q, Y.d - Y.q, Y.e - Y.l, Y.n - Y.l)

/-- One link field `φ` (charge `h`) and its conjugate (charge `−h`), in the up/down pattern. -/
def OneLink (Y : Charges) (h : ℚ) : Prop := hops Y = (h, -h, -h, h)

theorem links_iff_yukawa (Y : Charges) (h : ℚ) : OneLink Y h ↔ Yukawa Y h := by
  unfold OneLink hops Yukawa
  constructor
  · intro H
    simp only [Prod.mk.injEq] at H
    obtain ⟨h1, h2, h3, h4⟩ := H
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    simp only [Prod.mk.injEq]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem standard_links : hops standard = (1, -1, -1, 1) := by
  norm_num [hops, standard]

/-- With flux conservation, one unit-charge link and a neutral sterile channel, the charges are
forced (Paper III's `charges_forced`), now read as a domain-wall statement. -/
theorem forced_by_links (Y : Charges) (hf : Flux Y) (hl : OneLink Y 1) (hn : Y.n = 0) :
    Y = standard :=
  charges_forced Y hf ((links_iff_yukawa Y 1).mp hl) hn

end PMConstants.SectorLinks
