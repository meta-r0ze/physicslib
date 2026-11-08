import PMConstants.ReferenceDirections
import PMConstants.ColourReference
import PMAction.Machine.ReadoutAdditivity
import PMAction.Machine.RecordSupply
import PMAction.HomogeneousRouting
import PMAction.PersistenceSelection
import PMAction.Machine.ReferenceMaintenance

/-!
# Sector obligations from the record bound and the reference repair

The reference-maintenance task model (`ReferenceMaintenanceLedger`) left open the sector-local
events (weak's confinement to the reference row, and colour's separate per-channel obligation) and
an exact refresh. Each now
follows from a proved fact plus the definition of an independently drifting resource.

* `no_spare_no_ownership`: if a sector's setting is fixed uniquely by the reference repair, it
  cannot also maintain a resource whose drift varies independently of the reference. That
  resource's drift set would have at most one element. This turns `SpareFreedom`'s rule ("owning
  needs spare freedom") into a theorem.
* `weak_fixed`, `weak_cannot_own`: weak's three parameters are fixed by the three reference
  directions, so weak maintains no independently drifting resource beyond the reference row.
* `colour_needs_twelve_reads`: an exact refresh of the twelve independently drifting coloured
  payload channels keeps at least twelve records, one read per channel
  (`ReadoutAdditivity.exact_refresh_needs_records`).
* `colour_cost`: with additive event pricing at the payload price `η` per read, the cost is
  `12η = ColourChannels.colourLedger`.
* `weak_is_owner`: weak can repair every reference drift by itself and hypercharge cannot
  (colour fixes the reference). With one owner per job, the owner of the reference is weak. This
  is `FrameOwnership`'s Contract C.
* `full_column`, `coversFull_iff`: colour's generator moves no part of the reference column
  (`colour_unbroken`), so coverage with colour's actual generator is exactly `Covers`.
  `economy_single_owner_full` and `persistent_owner` use the derived form.
* `refresh_exact_homogeneous`: the translation routing is no longer assumed. Any site-homogeneous
  routing that moves records gives the same exactness.
* `economy_single_owner`: single ownership is not a separate principle. With a positive price
  per engaged sector, the unique cheapest set covering every reference correction is `{weak}`.
* `refresh_exact`: with lattice translation routing and a stationary background, the coupling
  site's refresh is exact at every tick (`RecordSupply.lattice_forever`). This is the exactness
  premise of `ReadoutAdditivity`.
-/

noncomputable section
namespace PMConstants.SectorObligations
open PMConstants ReferenceDirections

/-- **No spare freedom, no ownership.** -/
theorem no_spare_no_ownership {P T D : Type*} [Nonempty T] (ρ : P → T) (σ : P → D)
    (huniq : ∀ t, ∃! p, ρ p = t) (hmaint : ∀ t d, ∃ p, ρ p = t ∧ σ p = d) : Subsingleton D :=
  PMAction.ReferenceMaintenance.no_spare_no_ownership ρ σ huniq hmaint

/-- Weak's correction is fixed by the reference repair, for every hypercharge setting. -/
theorem weak_fixed (b : ℝ) (t : ℝ × ℂ) : ∃! p : ℝ × ℂ, displacement p.1 p.2 b = t := by
  refine ⟨(t.1 + b / 2, t.2), by simp [displacement], ?_⟩
  rintro ⟨a, z⟩ h
  obtain ⟨t1, t2⟩ := t
  simp only [displacement, Prod.mk.injEq] at h
  ext
  · simp; linarith [h.1]
  · simp [h.2]

/-- **Weak cannot own an independently drifting resource.** For any response `σ` of a further
resource to weak's setting, maintaining both the reference and that resource for every pair of
targets forces the resource's drift set to be trivial. -/
theorem weak_cannot_own {D : Type*} (b : ℝ) (σ : ℝ × ℂ → D)
    (hmaint : ∀ (t : ℝ × ℂ) (d : D), ∃ p : ℝ × ℂ, displacement p.1 p.2 b = t ∧ σ p = d) :
    Subsingleton D :=
  no_spare_no_ownership (fun p : ℝ × ℂ => displacement p.1 p.2 b) σ (weak_fixed b) hmaint

/-- **Weak alone repairs every reference drift.** -/
theorem weak_repairs_all (t : ℝ × ℂ) : ∃ p : ℝ × ℂ, displacement p.1 p.2 0 = t :=
  ⟨(t.1, t.2), by simp [displacement]⟩

/-- **Hypercharge alone cannot.** It moves the reference only along the real direction. -/
theorem hyper_alone_limited (b : ℝ) : (displacement 0 0 b).2 = 0 := by simp [displacement]

theorem hyper_alone_fails : ¬ ∀ t : ℝ × ℂ, ∃ b : ℝ, displacement 0 0 b = t := by
  intro h
  obtain ⟨b, hb⟩ := h (0, Complex.I)
  have := congrArg Prod.snd hb
  simp only [displacement] at this
  exact Complex.I_ne_zero this.symm

/-- **Contract C from single ownership.** If one sector must repair every reference drift by
itself (one owner per job, with colour fixing the reference, `ReferenceStabilizer.colour_unbroken`),
the owner is weak: weak can and hypercharge cannot. -/
theorem weak_is_owner :
    (∀ t : ℝ × ℂ, ∃ p : ℝ × ℂ, displacement p.1 p.2 0 = t) ∧
      ¬ ∀ t : ℝ × ℂ, ∃ b : ℝ, displacement 0 0 b = t :=
  ⟨weak_repairs_all, hyper_alone_fails⟩

/-- **Colour reads each coloured channel.** -/
theorem colour_needs_twelve_reads {n : Type*} [Fintype n] [Nonempty n] (R : ℕ)
    (P : ((Fin 12 → n → ℂ) × (Fin R → n → ℂ)) →ₗ[ℂ] ((Fin 12 → n → ℂ) × (Fin R → n → ℂ)))
    (hP : Function.Injective P) (hreset : ∀ inputs, (P (inputs, 0)).1 = 0) : 12 ≤ R :=
  PMAction.ReadoutAdditivity.exact_refresh_needs_records 12 R P hP hreset

/-- **The colour ledger is twelve payload reads.** -/
theorem colour_cost (C : Finset (Fin 12) → ℝ) (hempty : C ∅ = 0)
    (hsingle : ∀ i, C {i} = PMConstants.overhead)
    (hadd : ∀ s t : Finset (Fin 12), Disjoint s t → C (s ∪ t) = C s + C t) :
    C Finset.univ = ColourChannels.colourLedger := by
  rw [PMAction.ReadoutAdditivity.additive_read C (fun _ => PMConstants.overhead) hempty hsingle
    hadd, ColourChannels.colourLedger]
  simp

/-- **The refresh is exact.** -/
theorem refresh_exact {d : ℕ} (v : Fin d → ℤ) (hv : v ≠ 0) (o : Fin d → ℤ) {A : Type*}
    (s : (Fin d → ℤ) → A × A) (r : A) (hrec : ∀ x, (s x).2 = r) (t : ℕ) (ht : 1 ≤ t) :
    (PMAction.RecordSupply.run o (Equiv.addRight v) t s o).1 = r :=
  PMAction.RecordSupply.lattice_forever v hv o s r hrec t ht

/-- **The refresh is exact for any homogeneous routing that moves records.** No translation
premise: site-homogeneity makes the routing a translation
(`HomogeneousRouting.equivariant_is_translation`), and a routing that leaves the site fixed
never repairs it (`fixed_routing_returns`). -/
theorem refresh_exact_homogeneous {d : ℕ} (e : Equiv.Perm (Fin d → ℤ))
    (hcomm : ∀ w x, e (x + w) = e x + w) (o : Fin d → ℤ) (hmove : e o ≠ o) {A : Type*}
    (s : (Fin d → ℤ) → A × A) (r : A) (hrec : ∀ x, (s x).2 = r) (t : ℕ) (ht : 1 ≤ t) :
    (PMAction.RecordSupply.run o e t s o).1 = r :=
  PMAction.HomogeneousRouting.homogeneous_forever e hcomm o hmove s r hrec t ht

/-! ## Single ownership is Economy

Conservation requires the engaged sectors to produce every reference correction. Each sector engaged
on the reference is one more refresh of the same resource, priced `η > 0`
(`RefreshSchedule.strict_if_extra`: a repeated refresh costs strictly more). Colour fixes the
reference (`ReferenceStabilizer.colour_unbroken`), so it contributes no displacement. -/

inductive Sector | weak | hyper | colour
  deriving DecidableEq

/-- The engaged set `S` can produce every reference correction: weak supplies `(a, z)`,
hypercharge supplies `b`, colour supplies nothing. -/
def Covers (S : Finset Sector) : Prop :=
  ∀ t : ℝ × ℂ, ∃ a z b, (Sector.weak ∉ S → a = 0 ∧ z = 0) ∧ (Sector.hyper ∉ S → b = 0) ∧
    displacement a z b = t

theorem covers_of_weak {S : Finset Sector} (h : Sector.weak ∈ S) : Covers S :=
  fun t => ⟨t.1, t.2, 0, fun h' => absurd h h', fun _ => rfl, by simp [displacement]⟩

theorem weak_mem_of_covers {S : Finset Sector} (h : Covers S) : Sector.weak ∈ S := by
  by_contra hw
  obtain ⟨a, z, b, hwz, -, hd⟩ := h (0, Complex.I)
  have := congrArg Prod.snd hd
  simp only [displacement, (hwz hw).2] at this
  exact Complex.I_ne_zero this.symm

/-- **Single ownership from Economy.** Among engaged sets that cover every correction, the
cheapest, at a positive price per engaged sector, is exactly `{weak}`. So weak alone repairs the
reference (Contract C), with no separate ownership premise. -/
theorem economy_single_owner (η : ℝ) (hη : 0 < η) (S : Finset Sector) :
    (Covers S ∧ ∀ T, Covers T → η * S.card ≤ η * T.card) ↔ S = {Sector.weak} := by
  constructor
  · rintro ⟨hS, hmin⟩
    have hw := weak_mem_of_covers hS
    have hle : η * S.card ≤ η * ({Sector.weak} : Finset Sector).card :=
      hmin _ (covers_of_weak (Finset.mem_singleton_self _))
    have hc : S.card ≤ 1 := by
      have := le_of_mul_le_mul_left hle hη
      simpa using this
    exact (Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hw, fun x hx => (Finset.card_le_one.mp hc) x hx _ hw⟩)
  · rintro rfl
    refine ⟨covers_of_weak (Finset.mem_singleton_self _), fun T hT => ?_⟩
    have : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, weak_mem_of_covers hT⟩
    simp only [Finset.card_singleton, Nat.cast_one, mul_one]
    nlinarith [(by exact_mod_cast this : (1 : ℝ) ≤ T.card)]

/-! ## Colour's contribution, derived

`Covers` gave colour no displacement by hand. Here the engaged generator is the full
`gen a z b + colourGen B`, and what it does to the reference is its column at `lepton 0`. Colour's
column is zero (`ReferenceStabilizer.colour_unbroken`). The electroweak column is fixed by the
displacement, so the full condition is exactly `Covers`. -/

/-- The reference column carrying displacement `d`. -/
def refCol (d : ℝ × ℂ) : PacketGaugeActions.Channels → ℂ := fun c =>
  if c = ReferenceAnchor.lepton 0 then (d.1 : ℂ) else if c = ReferenceAnchor.lepton 1 then d.2 else 0

theorem refCol_inj (d d' : ℝ × ℂ) : refCol d = refCol d' ↔ d = d' := by
  constructor
  · intro h
    have h0 := congrFun h (ReferenceAnchor.lepton 0)
    have h1 := congrFun h (ReferenceAnchor.lepton 1)
    simp [refCol, ReferenceAnchor.lepton] at h0 h1
    exact Prod.ext h0 h1
  · rintro rfl; rfl

/-- The electroweak column is the displacement's column. -/
theorem gen_column (a : ℝ) (z : ℂ) (b : ℝ) (c : PacketGaugeActions.Channels) :
    gen a z b c (ReferenceAnchor.lepton 0) = refCol (displacement a z b) c := by
  rcases c with q | q | t | t
  · simp [gen, PacketTraceForm.weakGen, PacketTraceForm.hyperGen, PacketGaugeActions.block,
      PacketGaugeActions.charge, ReferenceAnchor.lepton, refCol]
  · simp [gen, PacketTraceForm.weakGen, PacketTraceForm.hyperGen, PacketGaugeActions.block,
      PacketGaugeActions.charge, ReferenceAnchor.lepton, refCol]
  · fin_cases t
    · simp [gen, PacketTraceForm.weakGen, PacketTraceForm.hyperGen,
        PacketGaugeActions.block, PacketGaugeActions.charge, ReferenceAnchor.lepton, refCol,
        displacement]
      ring
    · simp [gen, PacketTraceForm.weakGen, PacketTraceForm.hyperGen,
        PacketGaugeActions.block, PacketGaugeActions.charge, ReferenceAnchor.lepton, refCol,
        displacement]
  · simp [gen, PacketTraceForm.weakGen, PacketTraceForm.hyperGen, PacketGaugeActions.block,
      PacketGaugeActions.charge, ReferenceAnchor.lepton, refCol]

/-- **Colour adds nothing to the reference column**, for every colour generator. -/
theorem full_column (a : ℝ) (z : ℂ) (b : ℝ) (B : Matrix (Fin 3) (Fin 3) ℂ) :
    (fun c => (gen a z b + PacketTraceForm.colourGen B) c (ReferenceAnchor.lepton 0)) =
      refCol (displacement a z b) := by
  funext c
  rw [Matrix.add_apply, ReferenceStabilizer.colour_unbroken B 0 c, add_zero, gen_column]

/-- Coverage with colour's actual generator: every correction `t` is produced on the reference
column by the engaged sectors' combined generator. -/
def CoversFull (S : Finset Sector) : Prop :=
  ∀ t : ℝ × ℂ, ∃ a z b B, (Sector.weak ∉ S → a = 0 ∧ z = 0) ∧ (Sector.hyper ∉ S → b = 0) ∧
    (Sector.colour ∉ S → B = 0) ∧
    (fun c => (gen a z b + PacketTraceForm.colourGen B) c (ReferenceAnchor.lepton 0)) = refCol t

/-- **The hand-encoded coverage is the derived one.** -/
theorem coversFull_iff (S : Finset Sector) : CoversFull S ↔ Covers S := by
  constructor
  · intro h t
    obtain ⟨a, z, b, B, hw, hh, -, hcol⟩ := h t
    rw [full_column, refCol_inj] at hcol
    exact ⟨a, z, b, hw, hh, hcol⟩
  · intro h t
    obtain ⟨a, z, b, hw, hh, hd⟩ := h t
    exact ⟨a, z, b, 0, hw, hh, fun _ => rfl, by rw [full_column, hd]⟩

/-- **Single ownership with colour's generator included.** -/
theorem economy_single_owner_full (η : ℝ) (hη : 0 < η) (S : Finset Sector) :
    (CoversFull S ∧ ∀ T, CoversFull T → η * S.card ≤ η * T.card) ↔ S = {Sector.weak} := by
  simp only [coversFull_iff]
  exact economy_single_owner η hη S

/-- **Contract C from persistence.** Under Paper I's survival law `exp(−β · cost)` with `β > 0`,
and an engagement price `c₀ · p` (`c₀ = 1` by Closure, `p > 0`), the covering set that persists
best is exactly `{weak}`. -/
theorem persistent_owner (β c₀ p : ℝ) (hβ : 0 < β) (hc : c₀ = 1) (hp : 0 < p) (S : Finset Sector) :
    (CoversFull S ∧ ∀ T, CoversFull T →
        Real.exp (-β * (c₀ * p * T.card)) ≤ Real.exp (-β * (c₀ * p * S.card))) ↔
      S = {Sector.weak} := by
  rw [← economy_single_owner_full (c₀ * p) (PMAction.PersistenceSelection.event_price_pos c₀ p hc hp) S]
  refine and_congr_right fun _ => forall_congr' fun T => imp_congr_right fun _ => ?_
  exact (PMAction.PersistenceSelection.survival_strictAnti β hβ).le_iff_ge

end PMConstants.SectorObligations
