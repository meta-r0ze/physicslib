import PMAction.ReferenceNode

/-!
# The restoring node's boundary: floating spectators versus a host load

This is the scalar, conserving, zero-energy network of `ReferenceNode`.
It distinguishes deleting a leg, eliminating a free internal port, and holding
that port at a host-supplied potential. No occupancy rule selects between them.

Any finite collection of floating positive-conductance leaf ports contributes
zero steady current. Eliminating those ports and the central node gives the
usual two-terminal series response, even when all the spectator legs exist.
The same response is the minimum of the network's quadratic dissipation.
More generally, any finite symmetric host network attached only to the central
node contributes zero net steady current under its local Kirchhoff balances.

A port clamped by a host instead supplies a shunt load: the off-diagonal Kron
coupling equals the unloaded series value exactly when that load vanishes.
Equal legs give α/2 unloaded and α/3 with one equal clamped spectator. These
are boundary-conditioned admittances, not Hamiltonian rates or finite-frequency
claims. Native host coupling, its boundary condition and its clock remain open.
-/
noncomputable section
namespace PMAction.ReferenceNodeBoundary
open scoped BigOperators

variable {S : Type*} [Fintype S]

def center (a b u v : ℝ) : ℝ := (a * u + b * v) / (a + b)
def series (a b : ℝ) : ℝ := a * b / (a + b)

/-- Quadratic dissipation, without the optional overall factor 1/2. -/
def dissipation (a b : ℝ) (w : S → ℝ) (u v x : ℝ) (z : S → ℝ) : ℝ :=
  a * (u - x)^2 + b * (v - x)^2 + ∑ j, w j * (z j - x)^2

/-- Completing the square separates the two-terminal response from all internal work. -/
theorem dissipation_split (a b : ℝ) (hab : a + b ≠ 0) (w : S → ℝ)
    (u v x : ℝ) (z : S → ℝ) :
    dissipation a b w u v x z =
      series a b * (u - v)^2 + (a + b) * (x - center a b u v)^2 +
        ∑ j, w j * (z j - x)^2 := by
  unfold dissipation series center
  field_simp
  ring

/-- Floating spectators cannot lower the two-terminal minimum. -/
theorem dissipation_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (w : S → ℝ) (hw : ∀ j, 0 ≤ w j) (u v x : ℝ) (z : S → ℝ) :
    series a b * (u - v)^2 ≤ dissipation a b w u v x z := by
  rw [dissipation_split a b (by positivity)]
  have hx : 0 ≤ (a + b) * (x - center a b u v)^2 := by positivity
  have hz : 0 ≤ ∑ j, w j * (z j - x)^2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  linarith

/-- The minimizing spectator potentials follow the center; they are not fixed to zero. -/
theorem floating_attains (a b : ℝ) (hab : a + b ≠ 0) (w : S → ℝ) (u v : ℝ) :
    dissipation a b w u v (center a b u v) (fun _ => center a b u v) =
      series a b * (u - v)^2 := by
  rw [dissipation_split a b hab]
  simp

/-- Eliminate every floating port, with no assumption about how many there are. -/
theorem floating_minimum (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (w : S → ℝ) (hw : ∀ j, 0 ≤ w j) (u v : ℝ) :
    IsLeast {e | ∃ x z, dissipation a b w u v x z = e}
      (series a b * (u - v)^2) := by
  refine ⟨⟨center a b u v, fun _ => center a b u v,
    floating_attains a b (by positivity) w u v⟩, ?_⟩
  rintro e ⟨x,z,rfl⟩
  exact dissipation_bound a b ha hb w hw u v x z

/-- Zero injection at a positive-conductance leaf forces it to follow the center. -/
theorem floating_leaf (w x z : ℝ) (hw : 0 < w) :
    w * (z - x) = 0 ↔ z = x := by
  rw [mul_eq_zero]
  simp [hw.ne', sub_eq_zero]

/-- Kirchhoff balance plus free spectator equations determine the center uniquely. -/
theorem floating_center (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (w : S → ℝ) (hw : ∀ j, 0 < w j) (u v x : ℝ) (z : S → ℝ)
    (hports : ∀ j, w j * (z j - x) = 0)
    (hnode : a * (x - u) + b * (x - v) + ∑ j, w j * (x - z j) = 0) :
    x = center a b u v := by
  have hz : z = fun _ => x := funext fun j => (floating_leaf _ _ _ (hw j)).mp (hports j)
  subst z
  simp only [sub_self, mul_zero, Finset.sum_const_zero, add_zero] at hnode
  unfold center
  apply (eq_div_iff (by positivity : a + b ≠ 0)).mpr
  nlinarith

/-- The terminal current is exactly the unloaded series current. -/
theorem floating_current (a b : ℝ) (hab : a + b ≠ 0) (u v : ℝ) :
    a * (u - center a b u v) = series a b * (u - v) := by
  unfold center series
  field_simp
  ring

/-! ## A finite conserving host with no other boundary

The host may contain arbitrary symmetric internal links. Summing its local
Kirchhoff equations cancels those links. With no other injections or maintained
terminal, it contributes zero net steady current at the inner node. No statement
about transient storage, an open record flow or a driven host is inferred.
-/

/-- Every internal current cancels its reverse when summed over the whole host. -/
theorem internal_current_sum_zero (c : S → S → ℝ) (hc : ∀ i j, c i j = c j i)
    (z : S → ℝ) : (∑ i, ∑ j, c i j * (z i-z j)) = 0 := by
  have he : (∑ i, ∑ j, c i j * (z i-z j)) =
      ∑ i, ∑ j, c j i * (z j-z i) := Finset.sum_comm
  have hn : (∑ i, ∑ j, c j i * (z j-z i)) =
      -(∑ i, ∑ j, c i j * (z i-z j)) := by
    calc
      _ = ∑ i, ∑ j, -(c i j * (z i-z j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hc j i]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  linarith

/-- A finite host in steady local balance and with no other boundary draws no net current. -/
theorem closed_host_current (w : S → ℝ) (c : S → S → ℝ)
    (hc : ∀ i j, c i j = c j i) (x : ℝ) (z : S → ℝ)
    (hhost : ∀ i, w i*(z i-x) + ∑ j, c i j*(z i-z j) = 0) :
    (∑ i, w i*(x-z i)) = 0 := by
  have hs : (∑ i, (w i*(z i-x) + ∑ j, c i j*(z i-z j))) = 0 := by
    simp only [hhost, Finset.sum_const_zero]
  rw [Finset.sum_add_distrib, internal_current_sum_zero c hc z, add_zero] at hs
  calc
    _ = -(∑ i, w i*(z i-x)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [hs, neg_zero]

/-- A closed conserving host can remain attached without changing the two-terminal response. -/
theorem closed_host_response (a b : ℝ) (hab : a+b ≠ 0) (w : S → ℝ)
    (c : S → S → ℝ) (hc : ∀ i j, c i j = c j i) (u v x : ℝ) (z : S → ℝ)
    (hhost : ∀ i, w i*(z i-x) + ∑ j, c i j*(z i-z j) = 0)
    (hnode : a*(x-u) + b*(x-v) + ∑ i, w i*(x-z i) = 0) :
    x = center a b u v ∧ a*(u-x) = series a b*(u-v) := by
  rw [closed_host_current w c hc x z hhost, add_zero] at hnode
  have hx : x = center a b u v := by
    unfold center
    apply (eq_div_iff hab).mpr
    nlinarith
  refine ⟨hx, ?_⟩
  rw [hx]
  exact floating_current a b hab u v

/-- Off-diagonal Kron coupling when the host supplies a load to a fixed potential.
This is the mutual coefficient; a loaded two-port also has diagonal shunts. -/
def coupling (a b load : ℝ) : ℝ := a * b / (a + b + load)

/-- Eliminating the center gives this cross coefficient and separate host currents. -/
theorem loaded_current (a b load u v host : ℝ) (h : a + b + load ≠ 0) :
    a * (u - (a*u + b*v + load*host) / (a + b + load)) =
      coupling a b load * (u-v) + a*load / (a+b+load) * (u-host) := by
  unfold coupling
  field_simp
  ring

/-- A nonnegative host load changes the mutual coupling unless it is zero. -/
theorem series_iff_no_load (a b load : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hl : 0 ≤ load) : coupling a b load = series a b ↔ load = 0 := by
  unfold coupling series
  have hab : a + b ≠ 0 := by positivity
  have hall : a + b + load ≠ 0 := by positivity
  rw [div_eq_div_iff hall hab]
  constructor
  · intro h
    have hp : 0 < a*b := mul_pos ha hb
    nlinarith
  · intro h
    subst load
    ring

/-- The spectator's connection to an externally maintained host potential. -/
def hostLoad (g t : ℝ) : ℝ := g*t / (g+t)

/-- Local conservation fixes the spectator potential, including a nonzero host reference. -/
theorem host_port_balance (g t x host z : ℝ) (hg : 0 < g) (ht : 0 ≤ t) :
    g*(z-x) + t*(z-host) = 0 ↔ z = (g*x + t*host)/(g+t) := by
  have hgt : g+t ≠ 0 := by positivity
  rw [eq_div_iff hgt]
  constructor <;> intro h <;> nlinarith

/-- Eliminating that spectator leaves precisely its series connection to the host. -/
theorem spectator_load (g t x host : ℝ) (hg : 0 < g) (ht : 0 ≤ t) :
    g * (x - (g*x + t*host) / (g+t)) = hostLoad g t * (x-host) := by
  have hgt : g+t ≠ 0 := by positivity
  unfold hostLoad
  field_simp
  ring

theorem host_load_nonneg (g t : ℝ) (hg : 0 < g) (ht : 0 ≤ t) :
    0 ≤ hostLoad g t := by
  unfold hostLoad
  positivity

/-- For a present spectator leg, a passive host connection is unloaded exactly when absent. -/
theorem host_load_zero_iff (g t : ℝ) (hg : 0 < g) (ht : 0 ≤ t) :
    hostLoad g t = 0 ↔ t = 0 := by
  have hgt : g+t ≠ 0 := by positivity
  unfold hostLoad
  rw [div_eq_zero_iff, mul_eq_zero]
  simp [hg.ne', hgt]

/-- The two-leg coefficient is recovered exactly when the spectator has no passive host load. -/
theorem host_series_iff (a b g t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hg : 0 < g) (ht : 0 ≤ t) :
    coupling a b (hostLoad g t) = series a b ↔ t = 0 := by
  rw [series_iff_no_load a b _ ha hb (host_load_nonneg g t hg ht),
    host_load_zero_iff g t hg ht]

/-- Sum of terminal injections into the reduced two-port with the host held at zero. -/
def terminalSum (a b load u v : ℝ) : ℝ :=
  let x := (a*u + b*v)/(a+b+load)
  a*(u-x) + b*(v-x)

/-- Calling the inner response a closed two-port for every drive excludes a hidden load.
Total conservation of the larger host-plus-protocol network alone does not do so. -/
theorem closed_two_port_iff (a b load : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hl : 0 ≤ load) : (∀ u v, terminalSum a b load u v = 0) ↔ load = 0 := by
  have hall : a+b+load ≠ 0 := by positivity
  constructor
  · intro h
    have hh := h 1 1
    unfold terminalSum at hh
    field_simp at hh
    nlinarith [show 0 < a+b by positivity]
  · rintro rfl u v
    unfold terminalSum
    field_simp
    ring

/-- Equal terminal legs give the desired two-leg response with floating spectators. -/
theorem equal_floating (α : ℝ) (hα : 0 < α) : series α α = α/2 := by
  unfold series
  field_simp
  ring

/-- An equal spectator held fixed by the host instead gives the three-port coefficient. -/
theorem equal_clamped (α : ℝ) (hα : 0 < α) : coupling α α α = α/3 := by
  unfold coupling
  field_simp
  ring

end PMAction.ReferenceNodeBoundary
