import PMElementaryParticles.CompositeMasses
import PMElementaryParticles.LeptonMasses
import PMConstants.FloorNeutrino
import Mathlib.Tactic

/-!
# Composite particles: what persists, and what decays

This is the generic decay ledger above `Nucleon`/`Nucleus`/`Atom`. A species has
a certified mass (in electron-mass units), charge, baryon number and lepton
number. A decay is a nonempty product list with conserved `Q`, `B`, `L` and a
strictly smaller total mass. `Stable` means no such channel exists.

The interesting content is not the definition but the mass comparisons: `β⁻`
decay of the neutron, muon decay, charged-pion decay and tau decay are all
kinematically allowed by the **certified** mass enclosures. Stability of the
proton is a baryon-number statement, not a mass coincidence.
-/

noncomputable section
namespace PMAtoms

open PMElementaryParticles.CompositeMasses PMElementaryParticles.LeptonMasses

/-- Species with a certified mass in `m_e` units and the three conserved
quantum numbers used by the substrate ledger. -/
inductive Species
  | proton | neutron | electron | positron | neutrino | antineutrino
  | muon | antimuon | tau | pion0 | pionPlus | kaon0 | kaonPlus
  deriving DecidableEq, Repr

namespace Species

/-- Mass in electron-mass units. Neutrinos are massless in this ledger. -/
def mass : Species → ℝ
  | .proton => PMElementaryParticles.CompositeMasses.proton
  | .neutron => PMElementaryParticles.CompositeMasses.neutron
  | .electron => 1
  | .positron => 1
  | .neutrino => 0
  | .antineutrino => 0
  | .muon => PMElementaryParticles.LeptonMasses.muon
  | .antimuon => PMElementaryParticles.LeptonMasses.muon
  | .tau => PMElementaryParticles.LeptonMasses.tau
  | .pion0 => PMElementaryParticles.CompositeMasses.pion0
  | .pionPlus => PMElementaryParticles.LeptonMasses.pionPlus
  | .kaon0 => PMElementaryParticles.CompositeMasses.kaon0
  | .kaonPlus => PMElementaryParticles.CompositeMasses.kaonPlus

def charge : Species → ℚ
  | .proton => 1
  | .neutron => 0
  | .electron => -1
  | .positron => 1
  | .neutrino => 0
  | .antineutrino => 0
  | .muon => -1
  | .antimuon => 1
  | .tau => -1
  | .pion0 => 0
  | .pionPlus => 1
  | .kaon0 => 0
  | .kaonPlus => 1

def baryon : Species → ℚ
  | .proton => 1
  | .neutron => 1
  | _ => 0

def lepton : Species → ℚ
  | .electron => 1
  | .positron => -1
  | .neutrino => 1
  | .antineutrino => -1
  | .muon => 1
  | .antimuon => -1
  | .tau => 1
  | _ => 0

end Species

def pCharge (ds : List Species) : ℚ := (ds.map Species.charge).sum
def pBaryon (ds : List Species) : ℚ := (ds.map Species.baryon).sum
def pLepton (ds : List Species) : ℚ := (ds.map Species.lepton).sum
def pMass (ds : List Species) : ℝ := (ds.map Species.mass).sum

/-- A decay is kinematically allowed when charge, baryon and lepton number are
conserved and the products are lighter than the parent. -/
def ParticleDecay (p : Species) (ds : List Species) : Prop :=
  ds ≠ [] ∧ pCharge ds = p.charge ∧ pBaryon ds = p.baryon ∧
    pLepton ds = p.lepton ∧ pMass ds < p.mass

/-- A species persists when no allowed decay channel exists. -/
def Stable (p : Species) : Prop := ∀ ds, ¬ ParticleDecay p ds

theorem stable_of_no_channel (p : Species) (h : ∀ ds, ¬ ParticleDecay p ds) : Stable p := h

theorem decay_charge {p : Species} {ds : List Species} (h : ParticleDecay p ds) :
    pCharge ds = p.charge := h.2.1

theorem decay_baryon {p : Species} {ds : List Species} (h : ParticleDecay p ds) :
    pBaryon ds = p.baryon := h.2.2.1

theorem decay_lepton {p : Species} {ds : List Species} (h : ParticleDecay p ds) :
    pLepton ds = p.lepton := h.2.2.2.1

theorem decay_lighter {p : Species} {ds : List Species} (h : ParticleDecay p ds) :
    pMass ds < p.mass := h.2.2.2.2

theorem mass_nonneg : ∀ s : Species, 0 ≤ s.mass
  | .proton => le_of_lt (by simp [Species.mass]; linarith [PMElementaryParticles.CompositeMasses.proton_value.1])
  | .neutron => le_of_lt (by simp [Species.mass]; linarith [PMElementaryParticles.CompositeMasses.neutron_value.1])
  | .electron => by norm_num [Species.mass]
  | .positron => by norm_num [Species.mass]
  | .neutrino => by norm_num [Species.mass]
  | .antineutrino => by norm_num [Species.mass]
  | .muon => le_of_lt (by simp [Species.mass]; linarith [PMElementaryParticles.LeptonMasses.muon_value.1])
  | .antimuon => le_of_lt (by simp [Species.mass]; linarith [PMElementaryParticles.LeptonMasses.muon_value.1])
  | .tau => by simp [Species.mass, PMElementaryParticles.LeptonMasses.tau_value]
  | .pion0 => le_of_lt PMElementaryParticles.CompositeMasses.pion0_pos
  | .pionPlus => le_of_lt (by simp [Species.mass]; linarith [PMElementaryParticles.LeptonMasses.pionPlus_value.1])
  | .kaon0 => le_of_lt PMElementaryParticles.CompositeMasses.kaon0_pos
  | .kaonPlus => le_of_lt PMElementaryParticles.CompositeMasses.kaonPlus_pos

theorem baryon_nonneg (s : Species) : 0 ≤ s.baryon := by
  cases s <;> norm_num [Species.baryon]

theorem baryon_pos_cases {s : Species} (h : 0 < s.baryon) :
    s = .proton ∨ s = .neutron := by
  cases s <;> simp [Species.baryon] at h ⊢

lemma exists_pos_of_sum_pos : ∀ (ds : List Species),
    0 < pBaryon ds → ∃ d ∈ ds, 0 < Species.baryon d
  | [], h => by simp [pBaryon] at h
  | a :: as, h => by
      by_cases ha : 0 < Species.baryon a
      · exact ⟨a, by simp, ha⟩
      · have has : 0 < pBaryon as := by
          simp [pBaryon] at h ⊢
          have := baryon_nonneg a
          linarith
        obtain ⟨d, hd, hdpos⟩ := exists_pos_of_sum_pos as has
        exact ⟨d, by simp [hd], hdpos⟩

lemma le_pMass_of_mem (d : Species) : ∀ (ds : List Species), d ∈ ds → d.mass ≤ pMass ds
  | [], hd => by simp at hd
  | a :: as, hd => by
      rw [pMass]
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · have := List.sum_nonneg (l := as.map Species.mass)
          (fun x hx => by
            obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
            exact mass_nonneg s)
        linarith
      · have ih := le_pMass_of_mem d as hd'
        rw [pMass] at ih
        have := mass_nonneg a
        linarith

/-- **The proton does not decay.** Any channel with total baryon number one must
contain a proton or neutron; both weigh at least the proton, and all other
products have nonnegative mass, so the products cannot be lighter. -/
theorem proton_stable : Stable .proton := by
  intro ds hdec
  have hB : pBaryon ds = 1 := by
    rw [decay_baryon hdec]
    norm_num [Species.baryon]
  have hpos : 0 < pBaryon ds := by rw [hB]; norm_num
  obtain ⟨d, hd, hdpos⟩ := exists_pos_of_sum_pos ds hpos
  have hdcase := baryon_pos_cases hdpos
  have hdge : Species.mass .proton ≤ d.mass := by
    rcases hdcase with rfl | rfl
    · exact le_rfl
    · have hp := PMElementaryParticles.CompositeMasses.proton_value
      have hn := PMElementaryParticles.CompositeMasses.neutron_value
      simp [Species.mass]
      linarith
  have hle : Species.mass .proton ≤ pMass ds :=
    le_trans hdge (le_pMass_of_mem d ds hd)
  have hlt := decay_lighter hdec
  linarith

theorem pMass_nonneg (ds : List Species) : 0 ≤ pMass ds := by
  unfold pMass
  exact List.sum_nonneg (by
    intro x hx
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
    exact mass_nonneg s)

/-- **The massless neutrino is stable** in the particle ledger: every channel has
nonnegative mass, so no products can be lighter than zero. -/
theorem neutrino_stable : Stable .neutrino := by
  intro ds hdec
  have hlt := decay_lighter hdec
  have hnn := pMass_nonneg ds
  have hm : Species.mass .neutrino = 0 := by norm_num [Species.mass]
  rw [hm] at hlt
  linarith

/-- **The massless antineutrino is stable** for the same reason. -/
theorem antineutrino_stable : Stable .antineutrino := by
  intro ds hdec
  have hlt := decay_lighter hdec
  have hnn := pMass_nonneg ds
  have hm : Species.mass .antineutrino = 0 := by norm_num [Species.mass]
  rw [hm] at hlt
  linarith

/-- **Neutron `β⁻` decay is allowed**: `n → p e ν̄`, with
`m_p + m_e < m_n` from the certified mass enclosures. -/
theorem neutron_beta :
    ParticleDecay .neutron [.proton, .electron, .antineutrino] := by
  have hp := PMElementaryParticles.CompositeMasses.proton_value
  have hn := PMElementaryParticles.CompositeMasses.neutron_value
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · norm_num [pCharge, Species.charge]
  · norm_num [pBaryon, Species.baryon]
  · norm_num [pLepton, Species.lepton]
  · simp [pMass, Species.mass]
    linarith

/-- **Muon decay is allowed**: `μ → e ν ν̄`. -/
theorem muon_decay :
    ParticleDecay .muon [.electron, .neutrino, .antineutrino] := by
  have hm := PMElementaryParticles.LeptonMasses.muon_value
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · norm_num [pCharge, Species.charge]
  · norm_num [pBaryon, Species.baryon]
  · norm_num [pLepton, Species.lepton]
  · simp [pMass, Species.mass]
    linarith

/-- **Charged-pion decay is allowed**: `π⁺ → μ⁺ ν`. -/
theorem pionPlus_decay :
    ParticleDecay .pionPlus [.antimuon, .neutrino] := by
  have hp := PMElementaryParticles.LeptonMasses.pionPlus_value
  have hm := PMElementaryParticles.LeptonMasses.muon_value
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · norm_num [pCharge, Species.charge]
  · norm_num [pBaryon, Species.baryon]
  · norm_num [pLepton, Species.lepton]
  · simp [pMass, Species.mass]
    linarith

/-- **Tau decay is allowed**: `τ → μ ν ν̄`. -/
theorem tau_decay :
    ParticleDecay .tau [.muon, .neutrino, .antineutrino] := by
  have ht := PMElementaryParticles.LeptonMasses.tau_value
  have hm := PMElementaryParticles.LeptonMasses.muon_value
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · norm_num [pCharge, Species.charge]
  · norm_num [pBaryon, Species.baryon]
  · norm_num [pLepton, Species.lepton]
  · simp [pMass, Species.mass]
    rw [ht]
    linarith

/-! ## The massive-neutrino ledger (Review item A5)

`Species.mass` gives the neutrino mass **zero**, so `neutrino_stable` is almost trivial. A
*physical* neutrino is not massless: the E8 floor mass is `Bulk.floorMass α meEV ≈ 9.2 meV ≈
1.8×10⁻⁸ m_e` (`PMConstants.FloorNeutrino.floor_bounds`). We record the one-parameter **massive
ledger** `Species.massWith mν` (neutrino/antineutrino carry `mν`; every other species keeps its
certified mass) and prove that for any `mν ∈ [0,1]` the neutrino stays **stable**: it remains the
lightest species, so no channel's products can be lighter. In particular `neutrino_stable_floor`
applies at the E8 floor mass.

The content is exactly what A5 asked for — a *new mass ledger*. With `mν > 0` the old massless
argument (`pMass ds ≥ 0 = mν`) is unavailable; the bound `pMass ds ≥ mν` now needs every species'
mass to be `≥ mν`, which holds because every non-neutrino mass is `≥ 1`. -/

namespace Species

/-- Mass in `m_e` units with the neutrino and antineutrino given a common mass `mν` (the E8 floor
mass); every other species keeps its certified mass. -/
noncomputable def massWith (mν : ℝ) : Species → ℝ
  | .neutrino => mν
  | .antineutrino => mν
  | s => s.mass

theorem massWith_neutrino (mν : ℝ) : massWith mν .neutrino = mν := rfl

theorem massWith_antineutrino (mν : ℝ) : massWith mν .antineutrino = mν := rfl

theorem massWith_of_ne (mν : ℝ) {s : Species} (h : s ≠ .neutrino) (h' : s ≠ .antineutrino) :
    massWith mν s = s.mass := by cases s <;> simp_all [massWith]

end Species

/-- Total product mass in the massive ledger. -/
noncomputable def pMassWith (mν : ℝ) (ds : List Species) : ℝ :=
  (ds.map (Species.massWith mν)).sum

/-- **Every non-neutrino species weighs at least `1`** (`m_e`). -/
theorem one_le_mass_of_neutrino_ne {s : Species} (h : s ≠ .neutrino) (h' : s ≠ .antineutrino) :
    1 ≤ Species.mass s := by
  cases s <;> simp_all [Species.mass, PMElementaryParticles.LeptonMasses.tau_value]
  all_goals
    first
      | linarith [PMElementaryParticles.CompositeMasses.proton_value.1]
      | linarith [PMElementaryParticles.CompositeMasses.neutron_value.1]
      | linarith [PMElementaryParticles.LeptonMasses.muon_value.1]
      | linarith [PMElementaryParticles.CompositeMasses.pion0_value.1]
      | linarith [PMElementaryParticles.LeptonMasses.pionPlus_value.1]
      | linarith [PMElementaryParticles.CompositeMasses.kaonPlus_value.1]
      | (unfold PMElementaryParticles.CompositeMasses.kaon0
         linarith [PMElementaryParticles.CompositeMasses.g_b.1,
                   PMElementaryParticles.CompositeMasses.pi_b.2])

/-- **The floor mass is below every species' mass** for `mν ∈ [0,1]` — the neutrino is the lightest. -/
theorem massWith_ge (mν : ℝ) (h1 : mν ≤ 1) (s : Species) :
    mν ≤ Species.massWith mν s := by
  cases s <;> simp only [Species.massWith] <;> first
    | exact le_refl mν
    | exact le_trans h1 (one_le_mass_of_neutrino_ne (by simp) (by simp))

/-- A decay is kinematically allowed in the massive ledger. -/
def ParticleDecayWith (mν : ℝ) (p : Species) (ds : List Species) : Prop :=
  ds ≠ [] ∧ pCharge ds = p.charge ∧ pBaryon ds = p.baryon ∧
    pLepton ds = p.lepton ∧ pMassWith mν ds < Species.massWith mν p

/-- A species persists in the massive ledger when no allowed channel exists. -/
def StableWith (mν : ℝ) (p : Species) : Prop := ∀ ds, ¬ ParticleDecayWith mν p ds

/-- Product mass is at least the neutrino mass whenever the channel is nonempty. -/
theorem pMassWith_ge_of_ne_nil (mν : ℝ) (h0 : 0 ≤ mν) (h1 : mν ≤ 1)
    {ds : List Species} (hds : ds ≠ []) : mν ≤ pMassWith mν ds := by
  cases ds with
  | nil => exact absurd rfl hds
  | cons d rest =>
      have hd : mν ≤ Species.massWith mν d := massWith_ge mν h1 d
      have hrest : 0 ≤ (rest.map (Species.massWith mν)).sum :=
        List.sum_nonneg (by
          intro x hx
          obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
          exact le_trans h0 (massWith_ge mν h1 s))
      simp only [pMassWith, List.map_cons, List.sum_cons]
      linarith

/-- **The massive neutrino is stable** for every `mν ∈ [0,1]`: it is the lightest species, so no
channel's products can be strictly lighter. -/
theorem neutrino_stable_massive (mν : ℝ) (h0 : 0 ≤ mν) (h1 : mν ≤ 1) :
    StableWith mν .neutrino := by
  intro ds hdec
  have hlt : pMassWith mν ds < Species.massWith mν .neutrino := hdec.2.2.2.2
  rw [Species.massWith_neutrino] at hlt
  have hge : mν ≤ pMassWith mν ds := pMassWith_ge_of_ne_nil mν h0 h1 hdec.1
  linarith

theorem antineutrino_stable_massive (mν : ℝ) (h0 : 0 ≤ mν) (h1 : mν ≤ 1) :
    StableWith mν .antineutrino := by
  intro ds hdec
  have hlt : pMassWith mν ds < Species.massWith mν .antineutrino := hdec.2.2.2.2
  rw [Species.massWith_antineutrino] at hlt
  have hge : mν ≤ pMassWith mν ds := pMassWith_ge_of_ne_nil mν h0 h1 hdec.1
  linarith

/-- The E8 floor mass in `m_e` units (`≈ 1.8×10⁻⁸`). -/
noncomputable def floorMassME : ℝ :=
  PMConstants.Bulk.floorMass PMConstants.CertifiedConstants.α PMConstants.FloorNeutrino.meEV /
    PMConstants.FloorNeutrino.meEV

theorem floorMassME_bounds : 0 ≤ floorMassME ∧ floorMassME ≤ 1 := by
  have hb := PMConstants.FloorNeutrino.floor_bounds
  have hme : PMConstants.FloorNeutrino.meEV = 510998.95 := rfl
  have hm : (0 : ℝ) < PMConstants.FloorNeutrino.meEV := by rw [hme]; norm_num
  refine ⟨?_, ?_⟩
  · unfold floorMassME; exact div_nonneg (by linarith [hb.1]) hm.le
  · rw [floorMassME, div_le_one hm]; rw [hme] at hb ⊢; linarith [hb.2]

/-- **The neutrino with the E8 floor mass is stable.** A5's "new mass ledger" is instantiated at
the floor mass, whose E8 origin is `PMConstants.FloorNeutrino.floor_bounds`. -/
theorem neutrino_stable_floor : StableWith floorMassME .neutrino :=
  neutrino_stable_massive floorMassME floorMassME_bounds.1 floorMassME_bounds.2

end PMAtoms
