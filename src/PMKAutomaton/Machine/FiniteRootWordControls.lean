import PMKAutomaton.Machine.D4EdgeSeparation

/-!
# Smooth controls for arbitrary finite ordered root programs

An edge may carry any finite list of supplied primitive-root instructions,
including repeated roots and repeated passes. Disjoint smooth slots preserve
that order without assuming that different root generators commute. All slots
stay in the existing middle half of the edge, so the same D4 edge-separation
and bump construction can localize the program to a finite configuration.

The slots parametrize space along an edge. They do not derive a microscopic
event clock, optimal rate, gate admission or physical root prices. This is a
smooth realization of supplied packet-link data, not selection of that data.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.FiniteRootWordControls
open Matrix NativeCoherentLinks NativePacketUpdate ProfileControls
open scoped Matrix.Norms.L2Operator

local notation "M" => Matrix (Fin 4) (Fin 4) ℂ
local notation "st" => Real.smoothTransition

/-- Slot i of n, staggered inside the same middle half for every finite length. -/
def G {n : ℕ} (i : Fin n) (t : ℝ) := st (2*(n : ℝ)*t - ((n : ℝ)/2 + (i.val : ℝ)))
def g {n : ℕ} (i : Fin n) (t : ℝ) :=
  2*(n : ℝ)*deriv st (2*(n : ℝ)*t - ((n : ℝ)/2 + (i.val : ℝ)))

lemma hasDerivAt_G {n : ℕ} (i : Fin n) (t : ℝ) : HasDerivAt (G i) (g i t) t := by
  have h := (transition_diff.1 (2*(n : ℝ)*t - ((n : ℝ)/2 + (i.val : ℝ)))).hasDerivAt
  have hi := ((hasDerivAt_id' t).const_mul (2*(n : ℝ))).sub_const
    ((n : ℝ)/2 + (i.val : ℝ))
  rw [show g i t = deriv st (2*(n : ℝ)*t - ((n : ℝ)/2 + (i.val : ℝ))) *
    (2*(n : ℝ)*1) by unfold g; ring]
  exact h.comp t hi

lemma rate_ne {n : ℕ} {i : Fin n} {t : ℝ} (h : g i t ≠ 0) :
    0 < 2*(n : ℝ)*t - ((n : ℝ)/2 + (i.val : ℝ)) ∧
      2*(n : ℝ)*t - ((n : ℝ)/2 + (i.val : ℝ)) < 1 := by
  unfold g at h
  constructor
  · by_contra hn
    exact h (by rw [RootWordControls.deriv_transition_zero_of_nonpos (not_lt.1 hn), mul_zero])
  · by_contra hn
    exact h (by rw [RootWordControls.deriv_transition_zero_of_one_le (not_lt.1 hn), mul_zero])

lemma rate_outside {n : ℕ} (i : Fin n) {t : ℝ} (ht : t ≤ 1/4 ∨ 3/4 ≤ t) : g i t = 0 := by
  by_contra h
  have hr := rate_ne h
  have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  rcases ht with ht | ht <;> nlinarith [hr.1, hr.2]

def R {n : ℕ} (c : Fin 3) (roots : Fin n → Fin 4) (a : Fin n → ℝ) (i : Fin n) : M :=
  a i • packetRoot c (roots i)
def E {n : ℕ} (c : Fin 3) (roots : Fin n → Fin 4) (a : Fin n → ℝ) (i : Fin n) (t : ℝ) : M :=
  NormedSpace.exp (G i t • R c roots a i)

def product {n : ℕ} (c : Fin 3) (roots : Fin n → Fin 4) (a : Fin n → ℝ) (t : ℝ) : M :=
  (List.ofFn (fun i => E c roots a i t)).prod

def word {n : ℕ} (c : Fin 3) (roots : Fin n → Fin 4) (a : Fin n → ℝ) : M :=
  (List.ofFn (fun i => NormedSpace.exp (R c roots a i))).prod

lemma hasDerivAt_E {n : ℕ} (c : Fin 3) (roots : Fin n → Fin 4) (a : Fin n → ℝ)
    (i : Fin n) (t : ℝ) :
    HasDerivAt (E c roots a i) (E c roots a i t * (g i t • R c roots a i)) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (R c roots a i) (G i t)
  rw [mul_smul_comm]
  exact h.scomp t (hasDerivAt_G i t)

lemma E_zero {n : ℕ} (c : Fin 3) (roots : Fin n → Fin 4) (a : Fin n → ℝ) (i : Fin n) :
    E c roots a i 0 = 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  unfold E G
  rw [Real.smoothTransition.zero_of_nonpos (by nlinarith), zero_smul, NormedSpace.exp_zero]

lemma E_one {n : ℕ} (c : Fin 3) (roots : Fin n → Fin 4) (a : Fin n → ℝ) (i : Fin n) :
    E c roots a i 1 = NormedSpace.exp (R c roots a i) := by
  have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  unfold E G
  rw [Real.smoothTransition.one_of_one_le (by nlinarith), one_smul]

lemma later_idle {n : ℕ} (c : Fin 3) (roots : Fin n → Fin 4) (a : Fin n → ℝ)
    {i j : Fin n} (hij : i < j) {t : ℝ} (h : g i t ≠ 0) : E c roots a j t = 1 := by
  have hr := (rate_ne h).2
  have hi : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (Fin.lt_def.1 hij)
  unfold E G
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_smul, NormedSpace.exp_zero]

/-- Product differentiation only needs an active generator to commute with
later factors at that point; completed earlier factors need not commute. -/
lemma ordered_derivative {n : ℕ} (F : Fin n → ℝ → M) (B : Fin n → M) (t : ℝ)
    (hd : ∀ i, HasDerivAt (F i) (F i t * B i) t)
    (hc : ∀ i j, i < j → Commute (B i) (F j t)) :
    HasDerivAt (fun s => (List.ofFn (fun i => F i s)).prod)
      ((List.ofFn (fun i => F i t)).prod * ∑ i, B i) t := by
  induction n with
  | zero => simpa using (hasDerivAt_const t (1 : M))
  | succ n ih =>
    have ht := ih (fun i s => F i.succ s) (fun i => B i.succ)
      (fun i => hd i.succ) (fun i j hij => hc i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij))
    have hcomm : Commute (B 0) (List.ofFn (fun i : Fin n => F i.succ t)).prod := by
      apply Commute.list_prod_right
      intro A hA
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
      exact hc 0 i.succ (Fin.succ_pos i)
    simpa only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ] using
      RootWordControls.stagger_mul (hd 0) ht hcomm.eq

lemma product_derivative {n : ℕ} (c : Fin 3) (roots : Fin n → Fin 4) (a : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (product c roots a)
      (product c roots a t * ∑ i, g i t • R c roots a i) t := by
  apply ordered_derivative _ _ t (fun i => hasDerivAt_E c roots a i t)
  intro i j hij
  by_cases h : g i t = 0
  · simp [h]
  · rw [later_idle c roots a hij h]
    exact Commute.one_right _

/-- Repeated occurrences of the same root are accumulated in its control channel. -/
def controls {n : ℕ} (f : V →L[ℝ] ℝ) (b : ℝ) (roots : Fin n → Fin 4) (a : Fin n → ℝ) : Controls :=
  fun j x => (∑ i, if roots i = j then a i * g i (f x-b) else 0) • f

lemma controls_c2 {n : ℕ} (f : V →L[ℝ] ℝ) (b : ℝ) (roots : Fin n → Fin 4) (a : Fin n → ℝ) :
    ∀ j, ContDiff ℝ 2 (controls f b roots a j) := by
  intro j
  unfold controls
  have hc : ContDiff ℝ 2 (fun x : V =>
      ∑ i, if roots i = j then a i * g i (f x-b) else 0) := by
    apply ContDiff.sum
    intro i _
    by_cases h : roots i = j
    · simp only [h, ite_true]
      unfold g
      exact contDiff_const.mul ((contDiff_const.mul (transition_diff.2.comp
        ((contDiff_const.mul contDiff_id).sub contDiff_const))).comp
          (f.contDiff.sub contDiff_const))
    · simp only [h, ite_false]
      exact contDiff_const
  exact hc.smul contDiff_const

lemma packetA_controls {n : ℕ} (c : Fin 3) (f : V →L[ℝ] ℝ) (b : ℝ)
    (roots : Fin n → Fin 4) (a : Fin n → ℝ) (y v : V) :
    packetA c (controls f b roots a) y v = ∑ i, (g i (f y-b) * f v) • R c roots a i := by
  simp only [packetA, form, controls, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, smul_eq_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul, ite_smul, zero_smul]
  rw [Finset.sum_eq_single (roots i)]
  · simp only [ite_true, R, smul_smul]
    congr 1
    ring
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- Every finite ordered program has a smooth link realization, including the empty word. -/
theorem word_link {n : ℕ} (c : Fin 3) (f : V →L[ℝ] ℝ) (b : ℝ)
    (roots : Fin n → Fin 4) (a : Fin n → ℝ) (r : Realization c (controls f b roots a))
    (y v : V) (hv : f v = 1) (hy : f y = b) : r.packet y v 1 = word c roots a := by
  let B : ℝ → M := fun t => ∑ i, g i t • R c roots a i
  have key (t : ℝ) : packetA c (controls f b roots a) (y+t • v) v = B t := by
    rw [packetA_controls, map_add, map_smul, hy, hv]
    simp [B]
  have hskew (t : ℝ) : star (B t) = -B t := by
    have h := packet_skew c (controls f b roots a) (y+t • v) v
    rwa [key] at h
  have hU (t : ℝ) : HasDerivAt (r.packet y v) (r.packet y v t * B t) t := by
    have h := r.packet_deriv y v t
    rwa [key] at h
  have h := transport_unique hskew (by simp [product, E_zero]) (r.packet_zero y v)
    (fun t => product_derivative c roots a t) hU (r.packet_unitary y v) 1
  rw [← h]
  simp only [product, E_one, word]

/-- Agreement with the original four-root slot profiles. -/
lemma four_profile (i : Fin 4) (t : ℝ) : G i t = RootWordControls.G i t := by
  norm_num [G, RootWordControls.G]

lemma four_rate (i : Fin 4) (t : ℝ) : g i t = RootWordControls.g i t := by
  norm_num [g, RootWordControls.g]

/-- The previous single pass is a special case, in the same multiplication order. -/
lemma single_pass_word (c : Fin 3) (a : Fin 4 → ℝ) : word c id a =
    NormedSpace.exp (RootWordControls.R c a 0) * (NormedSpace.exp (RootWordControls.R c a 1) *
      (NormedSpace.exp (RootWordControls.R c a 2) * NormedSpace.exp (RootWordControls.R c a 3))) := by
  simp [word, R, RootWordControls.R, List.ofFn_succ]

lemma single_pass_controls (f : V →L[ℝ] ℝ) (b : ℝ) (a : Fin 4 → ℝ) :
    controls f b id a = RootWordControls.stagger f b a := by
  funext j x
  simp [controls, RootWordControls.stagger, four_rate]

/-- A list interface preserves every supplied occurrence and its position. -/
def listWord (c : Fin 3) (program : List (Fin 4 × ℝ)) : M :=
  (program.map fun s => NormedSpace.exp (s.2 • packetRoot c s.1)).prod

lemma word_from_list (c : Fin 3) (program : List (Fin 4 × ℝ)) :
    word c (fun i : Fin program.length => program[i.val].1)
      (fun i : Fin program.length => program[i.val].2) = listWord c program := by
  unfold word listWord
  exact congrArg List.prod (List.ofFn_getElem_eq_map program
    (fun s : Fin 4 × ℝ => NormedSpace.exp (s.2 • packetRoot c s.1)))

/-- Concatenation retains order; no commutativity of successive roots is imposed. -/
lemma listWord_append (c : Fin 3) (first second : List (Fin 4 × ℝ)) :
    listWord c (first ++ second) = listWord c first * listWord c second := by
  simp [listWord]

end PMAction.FiniteRootWordControls
