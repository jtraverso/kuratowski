/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.FaceRing
public import LeanPool.K5MinorFreeChoosability.Wagner.Contract

/-!
# The rotation around a vertex and the necklace of faces

For a dart `e0` of a plane map, `rd e0 i = rot^i e0` runs around the tail of `e0` with period
`rper e0`.  The *necklace segment* `ring e0 a b` is the union of the ring sets of the darts
`rd e0 t`, `a ≤ t < b`.  For a graph without small separations these segments are connected,
consecutive segments touch, and segments inside one period are disjoint.

For the contraction `G / xy` (`contractGraph`) the segments around `x` avoid `x` and `y` and
hence are connected and touching in `G` as well.  This gives the two obstructions of
Thomassen's proof of Kuratowski's theorem:

* `not_k5MinorFree_of_three`: three neighbours of the contracted vertex, all adjacent to both
  `x` and `y` in `G`, give a `K_5` minor;
* `isMinor_K33_of_alternating`: four neighbours alternating `y, x, y, x` around the contracted
  vertex give a `K_{3,3}` minor.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {V : Type*}

theorem ConnSet.union_touch [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}
    (hA : ConnSet G ↑A) (hB : ConnSet G ↑B) (h : Touch G A B) : ConnSet G ↑(A ∪ B) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := h
  have hAU : (↑A : Set V) ⊆ ↑(A ∪ B) := Finset.coe_subset.2 Finset.subset_union_left
  have hBU : (↑B : Set V) ⊆ ↑(A ∪ B) := Finset.coe_subset.2 Finset.subset_union_right
  have hpq' : RIn G ↑(A ∪ B) p q := RIn.single hpq (hAU hp) (hBU hq)
  have key : ∀ c ∈ (↑(A ∪ B) : Set V), RIn G ↑(A ∪ B) p c := by
    intro c hc
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hc | hc
    · exact (hA.2 p hp c hc).mono_set hAU
    · exact hpq'.trans ((hB.2 q hq c hc).mono_set hBU)
  exact ⟨⟨p, hAU hp⟩, fun a ha b hb => (key a ha).symm.trans (key b hb)⟩

theorem ConnSet.of_adj {G G' : SimpleGraph V} {X : Set V} (h : ConnSet G X)
    (hadj : ∀ u ∈ X, ∀ v ∈ X, G.Adj u v → G'.Adj u v) : ConnSet G' X := by
  refine ⟨h.1, fun a ha b hb => ?_⟩
  have hr := h.2 a ha b hb
  clear hb
  induction hr with
  | refl => exact RIn.refl _
  | tail _ hcd ih => exact ih.tail (hadj _ hcd.2.1 _ hcd.2.2 hcd.1) hcd.2.1 hcd.2.2

namespace PlaneMap

variable {G : SimpleGraph V} (M : PlaneMap G) (e0 : G.Dart)

/-- The `i`-th dart around the tail of `e0`. -/
def rd (i : ℕ) : G.Dart := (M.rot ^ i) e0

theorem rd_zero : M.rd e0 0 = e0 := by simp [rd]

theorem rd_succ (i : ℕ) : M.rd e0 (i + 1) = M.rot (M.rd e0 i) := by
  simp [rd, pow_succ']

theorem rd_fst (i : ℕ) : (M.rd e0 i).fst = e0.fst := by
  induction i with
  | zero => simp [rd]
  | succ i ih => rw [rd_succ, M.isRotationSystem.fst_apply, ih]

theorem rd_add (i j : ℕ) : M.rd e0 (i + j) = (M.rot ^ i) (M.rd e0 j) := by
  simp [rd, pow_add]

variable [Finite V]

theorem exists_rper : ∃ n, 0 < n ∧ (M.rot ^ n) e0 = e0 := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨i, hi, -, h⟩ := (SameCycle.refl M.rot e0).exists_pow_eq''
  exact ⟨i, hi, h⟩

open Classical in
/-- The number of darts around the tail of `e0`. -/
noncomputable def rper : ℕ := Nat.find (M.exists_rper e0)

theorem rper_pos : 0 < M.rper e0 := by
  classical
  exact (Nat.find_spec (M.exists_rper e0)).1

theorem rd_rper : M.rd e0 (M.rper e0) = e0 := by
  classical
  exact (Nat.find_spec (M.exists_rper e0)).2

theorem rd_ne_self {n : ℕ} (h0 : 0 < n) (hn : n < M.rper e0) : M.rd e0 n ≠ e0 := by
  classical
  exact fun h => Nat.find_min (M.exists_rper e0) hn ⟨h0, h⟩

theorem rd_add_rper (i : ℕ) : M.rd e0 (i + M.rper e0) = M.rd e0 i := by
  rw [rd_add, rd_rper]
  rfl

theorem rd_add_mul (i m : ℕ) : M.rd e0 (i + M.rper e0 * m) = M.rd e0 i := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, ← add_assoc, rd_add_rper, ih]

theorem rd_mod (i : ℕ) : M.rd e0 (i % M.rper e0) = M.rd e0 i := by
  conv_rhs => rw [← Nat.mod_add_div i (M.rper e0)]
  rw [rd_add_mul]

theorem rd_injOn {i j : ℕ} (hij : i < j) (hj : j < i + M.rper e0) : M.rd e0 i ≠ M.rd e0 j := by
  intro h
  have h2 : M.rd e0 j = (M.rot ^ i) (M.rd e0 (j - i)) := by
    rw [← rd_add]; congr 1; omega
  rw [h2] at h
  have h3 : M.rd e0 (j - i) = e0 :=
    (M.rot ^ i).injective (h.symm.trans (rfl : M.rd e0 i = (M.rot ^ i) e0))
  exact M.rd_ne_self e0 (by omega) (by omega) h3

theorem exists_rd_eq {d : G.Dart} (hd : d.fst = e0.fst) : ∃ i < M.rper e0, M.rd e0 i = d := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨i, -, -, h⟩ := (M.isRotationSystem.sameCycle e0 d hd.symm).exists_pow_eq''
  exact ⟨i % M.rper e0, Nat.mod_lt _ (M.rper_pos e0), by rw [rd_mod]; exact h⟩

/-- Every dart around the vertex occurs in every window of one period. -/
theorem exists_window (s i : ℕ) : ∃ t < M.rper e0, M.rd e0 (s + t) = M.rd e0 i := by
  set k := M.rper e0 with hk
  have hk1 : 1 ≤ k := M.rper_pos e0
  refine ⟨(i + (k - 1) * s) % k, Nat.mod_lt _ (by omega), ?_⟩
  have e1 : s + (i + (k - 1) * s) % k + k * ((i + (k - 1) * s) / k) = i + k * s := by
    have := Nat.mod_add_div (i + (k - 1) * s) k
    have h2 : (k - 1) * s + s = k * s := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hk1]
    omega
  rw [← M.rd_add_mul e0 (s + (i + (k - 1) * s) % k) ((i + (k - 1) * s) / k), e1, rd_add_mul]

theorem rot_rd_ne (h2 : 2 ≤ M.rper e0) (i : ℕ) : M.rot (M.rd e0 i) ≠ M.rd e0 i := by
  rw [← rd_succ]
  exact (M.rd_injOn e0 (Nat.lt_succ_self i) (by omega)).symm

variable [DecidableEq V]

/-- The necklace segment: ring sets of the darts `rd e0 t`, `a ≤ t < b`. -/
noncomputable def ring (a b : ℕ) : Finset V :=
  (Finset.Ico a b).biUnion fun t => M.ringSet (M.rd e0 t)

theorem mem_ring {a b : ℕ} {v : V} :
    v ∈ M.ring e0 a b ↔ ∃ t, a ≤ t ∧ t < b ∧ v ∈ M.ringSet (M.rd e0 t) := by
  simp [ring, and_assoc]

theorem ringSet_subset_ring {a b t : ℕ} (ha : a ≤ t) (hb : t < b) :
    M.ringSet (M.rd e0 t) ⊆ M.ring e0 a b :=
  Finset.subset_biUnion_of_mem (fun t => M.ringSet (M.rd e0 t)) (Finset.mem_Ico.2 ⟨ha, hb⟩)

theorem snd_mem_ring (h2 : 2 ≤ M.rper e0) {a b j : ℕ} (ha : a ≤ j) (hb : j < b) :
    (M.rd e0 (j + 1)).snd ∈ M.ring e0 a b := by
  refine M.ringSet_subset_ring e0 ha hb ?_
  rw [rd_succ]
  exact M.ringSet_mem_snd_rot (M.rot_rd_ne e0 h2 j)

theorem snd_mem_ring' (h2 : 2 ≤ M.rper e0) {a b : ℕ} (hab : a < b) :
    (M.rd e0 b).snd ∈ M.ring e0 a b := by
  have := M.snd_mem_ring e0 h2 (j := b - 1) (by omega : a ≤ b - 1) (by omega : b - 1 < b)
  rwa [Nat.sub_add_cancel (by omega)] at this

theorem exists_adj_of_mem_ring {a b : ℕ} {v : V} (hv : v ∈ M.ring e0 a b) : ∃ u, G.Adj v u := by
  obtain ⟨t, -, -, hv⟩ := (M.mem_ring e0).1 hv
  obtain ⟨n, -, -, rfl⟩ := (M.mem_ringSet).1 hv
  exact ⟨_, ((M.facePerm ^ n) (M.rot (M.rd e0 t))).adj⟩

theorem connSet_ring (h2 : 2 ≤ M.rper e0) {a b : ℕ} (hab : a < b) : ConnSet G ↑(M.ring e0 a b) := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [ring, Nat.Ico_succ_singleton, Finset.singleton_biUnion]
    exact M.connSet_ringSet (M.rot_rd_ne e0 h2 a)
  | succ b hb ih =>
    have e : M.ring e0 a (b + 1) = M.ringSet (M.rd e0 b) ∪ M.ring e0 a b := by
      rw [ring, Nat.Ico_succ_right_eq_insert_Ico (by omega), Finset.biUnion_insert]
      rfl
    rw [e]
    refine ConnSet.union_touch (M.connSet_ringSet (M.rot_rd_ne e0 h2 b)) ih ?_
    have ht := M.touch_ringSet_rot (M.rot_rd_ne e0 h2 (b - 1))
    rw [← rd_succ, Nat.sub_add_cancel (by omega)] at ht
    exact ht.mono subset_rfl (M.ringSet_subset_ring e0 (by omega) (by omega))

theorem touch_ring (h2 : 2 ≤ M.rper e0) {a b c : ℕ} (hab : a < b) (hbc : b < c) :
    Touch G (M.ring e0 a b) (M.ring e0 b c) := by
  have ht := M.touch_ringSet_rot (M.rot_rd_ne e0 h2 (b - 1))
  rw [← rd_succ, Nat.sub_add_cancel (by omega)] at ht
  exact (ht.mono (M.ringSet_subset_ring e0 le_rfl hbc)
    (M.ringSet_subset_ring e0 (by omega) (by omega))).symm

theorem ring_add_rper (a b : ℕ) : M.ring e0 (a + M.rper e0) (b + M.rper e0) = M.ring e0 a b := by
  ext v
  rw [mem_ring, mem_ring]
  constructor
  · rintro ⟨t, h1, h2, h3⟩
    refine ⟨t - M.rper e0, by omega, by omega, ?_⟩
    rwa [← rd_add_rper, Nat.sub_add_cancel (by omega)]
  · rintro ⟨t, h1, h2, h3⟩
    exact ⟨t + M.rper e0, by omega, by omega, by rwa [rd_add_rper]⟩

variable {S : Finset V} (hS : ∀ u v, G.Adj u v → u ∈ S) (hsep : NoSmallSep G S)
  (hK : numComponents M.rot (dartSymm G) ≤ 1)
include hS hsep hK

theorem disjoint_ring {a b c d : ℕ} (hbc : b ≤ c) (hd : d ≤ a + M.rper e0) :
    Disjoint (M.ring e0 a b) (M.ring e0 c d) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨t, ht1, ht2, ht3⟩ := (M.mem_ring e0).1 hv
  obtain ⟨t', ht1', ht2', ht3'⟩ := (M.mem_ring e0).1 hv'
  have hne := M.rd_injOn e0 (i := t) (j := t') (by omega) (by omega)
  have := M.disjoint_ringSet hS hsep hK hne (by rw [rd_fst, rd_fst])
  exact Finset.disjoint_left.1 this ht3 ht3'

theorem not_mem_ring_fst (a b : ℕ) : e0.fst ∉ M.ring e0 a b := by
  intro h
  obtain ⟨t, -, -, ht⟩ := (M.mem_ring e0).1 h
  have := M.not_mem_ringSet_fst hS hsep hK (M.rd e0 t)
  rw [rd_fst] at this
  exact this ht

end PlaneMap

/-! ### The necklace around a contracted vertex -/

section Contracted

variable [DecidableEq V] [Finite V] {H : SimpleGraph V} {x y : V}
  (M : PlaneMap (contractGraph H x y)) (e0 : (contractGraph H x y).Dart)

omit [DecidableEq V] [Finite V] in
theorem rd_snd_ne_y (i : ℕ) : (M.rd e0 i).snd ≠ y := by
  intro h
  have := (M.rd e0 i).adj.symm
  rw [h] at this
  exact contractGraph_not_adj_y _ this

theorem not_mem_ring_y (a b : ℕ) : y ∉ M.ring e0 a b := by
  intro h
  obtain ⟨u, hu⟩ := M.exists_adj_of_mem_ring e0 h
  exact contractGraph_not_adj_y _ hu

omit [DecidableEq V] [Finite V] in
theorem adj_of_contract_adj {u v : V} (hux : u ≠ x) (hvx : v ≠ x) (huy : u ≠ y) (hvy : v ≠ y)
    (h : (contractGraph H x y).Adj u v) : H.Adj u v :=
  (contractGraph_adj_of_ne hux hvx huy hvy).1 h

omit [DecidableEq V] [Finite V] in
theorem ne_of_not_mem {X : Finset V} {z u : V} (hz : z ∉ X) (hu : u ∈ (↑X : Set V)) : u ≠ z :=
  fun e => hz (by rw [← e]; exact Finset.mem_coe.1 hu)

omit [DecidableEq V] [Finite V] in
theorem connSet_finset_singleton (z : V) : ConnSet H ↑({z} : Finset V) := by
  rw [Finset.coe_singleton]
  exact connSet_singleton H z

omit [DecidableEq V] [Finite V] in
theorem connSet_of_contract {X : Finset V} (hx : x ∉ X) (hy : y ∉ X)
    (h : ConnSet (contractGraph H x y) ↑X) : ConnSet H ↑X :=
  h.of_adj fun _ hu _ hv huv =>
    adj_of_contract_adj (ne_of_not_mem hx hu) (ne_of_not_mem hx hv) (ne_of_not_mem hy hu)
      (ne_of_not_mem hy hv) huv

omit [DecidableEq V] [Finite V] in
theorem touch_of_contract {X Y : Finset V} (hx : x ∉ X) (hy : y ∉ X) (hx' : x ∉ Y)
    (hy' : y ∉ Y) (h : Touch (contractGraph H x y) X Y) : Touch H X Y := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  exact ⟨u, hu, v, hv, adj_of_contract_adj (ne_of_not_mem hx hu) (ne_of_not_mem hx' hv)
    (ne_of_not_mem hy hu) (ne_of_not_mem hy' hv) huv⟩

variable {S : Finset V} (hS : ∀ u v, (contractGraph H x y).Adj u v → u ∈ S)
  (hsep : NoSmallSep (contractGraph H x y) S)
  (hK : numComponents M.rot (dartSymm (contractGraph H x y)) ≤ 1)
  (he0 : e0.fst = x) (h2 : 2 ≤ M.rper e0)
include hS hsep hK he0 h2

omit h2 in
theorem not_mem_ring_x (a b : ℕ) : x ∉ M.ring e0 a b := by
  have := M.not_mem_ring_fst e0 hS hsep hK a b
  rwa [he0] at this

theorem connSet_ring_H {a b : ℕ} (hab : a < b) : ConnSet H ↑(M.ring e0 a b) :=
  connSet_of_contract (not_mem_ring_x M e0 hS hsep hK he0 a b) (not_mem_ring_y M e0 a b)
    (M.connSet_ring e0 h2 hab)

theorem touch_ring_H {a b c : ℕ} (hab : a < b) (hbc : b < c) :
    Touch H (M.ring e0 a b) (M.ring e0 b c) :=
  touch_of_contract (not_mem_ring_x M e0 hS hsep hK he0 a b) (not_mem_ring_y M e0 a b)
    (not_mem_ring_x M e0 hS hsep hK he0 b c) (not_mem_ring_y M e0 b c)
    (M.touch_ring e0 h2 hab hbc)

omit h2 in
theorem disjoint_singleton_x_ring (a b : ℕ) : Disjoint {x} (M.ring e0 a b) :=
  Finset.disjoint_singleton_left.2 (not_mem_ring_x M e0 hS hsep hK he0 a b)

omit hS hsep hK he0 h2 in
theorem disjoint_singleton_y_ring (a b : ℕ) : Disjoint {y} (M.ring e0 a b) :=
  Finset.disjoint_singleton_left.2 (not_mem_ring_y M e0 a b)

omit hS hsep hK he0 h2 in
theorem touch_singleton_ring {z : V} {a b j : ℕ} (hj : (M.rd e0 j).snd ∈ M.ring e0 a b)
    (h : H.Adj z (M.rd e0 j).snd) : Touch H {z} (M.ring e0 a b) :=
  ⟨z, Finset.mem_singleton_self z, _, hj, h⟩

/-- **The `K_5` obstruction**: three neighbours of the contracted vertex, each adjacent to both
`x` and `y`, give a `K_5` minor of `H`. -/
theorem not_k5MinorFree_of_three (hxy : H.Adj x y) {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (hca : c < a + M.rper e0)
    (hxa : H.Adj x (M.rd e0 a).snd) (hya : H.Adj y (M.rd e0 a).snd)
    (hxb : H.Adj x (M.rd e0 b).snd) (hyb : H.Adj y (M.rd e0 b).snd)
    (hxc : H.Adj x (M.rd e0 c).snd) (hyc : H.Adj y (M.rd e0 c).snd) : ¬ K5MinorFree H := by
  intro hfree
  apply hfree
  set k := M.rper e0
  have hwa : (M.rd e0 (a + k)).snd = (M.rd e0 a).snd := by rw [M.rd_add_rper]
  have mb := M.snd_mem_ring' e0 h2 hab
  have mc := M.snd_mem_ring' e0 h2 hbc
  have ma := M.snd_mem_ring' e0 h2 (by omega : c < a + k)
  rw [hwa] at ma
  have c1 := connSet_ring_H M e0 hS hsep hK he0 h2 hab
  have c2 := connSet_ring_H M e0 hS hsep hK he0 h2 hbc
  have c3 := connSet_ring_H M e0 hS hsep hK he0 h2 (by omega : c < a + k)
  have dx := disjoint_singleton_x_ring M e0 hS hsep hK he0
  have dy := disjoint_singleton_y_ring (H := H) M e0
  have d12 := M.disjoint_ring e0 hS hsep hK (a := a) (b := b) (c := b) (d := c) le_rfl (by omega)
  have d13 := M.disjoint_ring e0 hS hsep hK (a := a) (b := b) (c := c) (d := a + k)
    (by omega) le_rfl
  have d23 := M.disjoint_ring e0 hS hsep hK (a := b) (b := c) (c := c) (d := a + k) le_rfl
    (by omega)
  have dxy : Disjoint ({x} : Finset V) {y} := Finset.disjoint_singleton.2 hxy.ne
  have t01 : Touch H {x} {y} :=
    ⟨x, Finset.mem_singleton_self _, y, Finset.mem_singleton_self _, hxy⟩
  have t02 := touch_singleton_ring M e0 mb hxb
  have t03 := touch_singleton_ring M e0 mc hxc
  have t04 := touch_singleton_ring M e0 ma hxa
  have t12 := touch_singleton_ring M e0 mb hyb
  have t13 := touch_singleton_ring M e0 mc hyc
  have t14 := touch_singleton_ring M e0 ma hya
  have t23 := touch_ring_H M e0 hS hsep hK he0 h2 hab hbc
  have t34 := touch_ring_H M e0 hS hsep hK he0 h2 hbc (by omega : c < a + k)
  have t24 : Touch H (M.ring e0 a b) (M.ring e0 c (a + k)) := by
    have := touch_ring_H M e0 hS hsep hK he0 h2 (a := c) (b := a + k) (c := b + k) (by omega)
      (by omega)
    rw [M.ring_add_rper] at this
    exact this.symm
  refine ⟨CliqueMinorModel.ofConnSet
    ![{x}, {y}, M.ring e0 a b, M.ring e0 b c, M.ring e0 c (a + k)] (fun i => ?_)
    (fun i j hij => ?_) (fun i j hij => ?_)⟩
  · fin_cases i
    · exact connSet_finset_singleton x
    · exact connSet_finset_singleton y
    · exact c1
    · exact c2
    · exact c3
  · fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact dxy | exact dxy.symm | exact dx _ _ | exact (dx _ _).symm
      | exact dy _ _ | exact (dy _ _).symm | exact d12 | exact d12.symm | exact d13
      | exact d13.symm | exact d23 | exact d23.symm
  · fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact t01 | exact t01.symm | exact t02 | exact t02.symm | exact t03 | exact t03.symm
      | exact t04 | exact t04.symm | exact t12 | exact t12.symm | exact t13 | exact t13.symm
      | exact t14 | exact t14.symm | exact t23 | exact t23.symm | exact t34 | exact t34.symm
      | exact t24 | exact t24.symm

/-- **The `K_{3,3}` obstruction**: four neighbours of the contracted vertex alternating
`y, x, y, x` around it give a `K_{3,3}` minor of `H`. -/
theorem isMinor_K33_of_alternating (hxy : H.Adj x y) {a b c d : ℕ} (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hda : d < a + M.rper e0)
    (hya : H.Adj y (M.rd e0 a).snd) (hxb : H.Adj x (M.rd e0 b).snd)
    (hyc : H.Adj y (M.rd e0 c).snd) (hxd : H.Adj x (M.rd e0 d).snd) : IsMinor K33 H := by
  set k := M.rper e0
  have hwa : (M.rd e0 (a + k)).snd = (M.rd e0 a).snd := by rw [M.rd_add_rper]
  have ma := M.snd_mem_ring' e0 h2 hda
  rw [hwa] at ma
  have mb := M.snd_mem_ring' e0 h2 hab
  have mc := M.snd_mem_ring' e0 h2 hbc
  have md := M.snd_mem_ring' e0 h2 hcd
  have dx := disjoint_singleton_x_ring M e0 hS hsep hK he0
  have dy := disjoint_singleton_y_ring (H := H) M e0
  have DR := fun {a b c d : ℕ} (h1 : b ≤ c) (h2 : d ≤ a + k) =>
    M.disjoint_ring e0 hS hsep hK (a := a) (b := b) (c := c) (d := d) h1 h2
  have TR := fun {a b c : ℕ} (h1 : a < b) (h2' : b < c) =>
    touch_ring_H M e0 hS hsep hK he0 h2 (a := a) (b := b) (c := c) h1 h2'
  have t11 : Touch H (M.ring e0 d (a + k)) (M.ring e0 a b) := by
    have := TR (a := d) (b := a + k) (c := b + k) (by omega) (by omega)
    rwa [M.ring_add_rper] at this
  exact isMinor_K33_of_six (X₀ := {x}) (X₁ := M.ring e0 d (a + k)) (X₂ := M.ring e0 b c)
    (Y₀ := {y}) (Y₁ := M.ring e0 a b) (Y₂ := M.ring e0 c d)
    (connSet_finset_singleton x) (connSet_ring_H M e0 hS hsep hK he0 h2 hda)
    (connSet_ring_H M e0 hS hsep hK he0 h2 hbc) (connSet_finset_singleton y)
    (connSet_ring_H M e0 hS hsep hK he0 h2 hab) (connSet_ring_H M e0 hS hsep hK he0 h2 hcd)
    (dx _ _) (dx _ _) (DR (by omega) (by omega)).symm
    (dy _ _) (dy _ _) (DR (by omega) (by omega))
    (Finset.disjoint_singleton.2 hxy.ne) (dx _ _) (dx _ _)
    (dy _ _).symm (DR (by omega) (by omega)).symm (DR (by omega) (by omega)).symm
    (dy _ _).symm (DR (by omega) (by omega)).symm (DR (by omega) (by omega))
    ⟨x, Finset.mem_singleton_self _, y, Finset.mem_singleton_self _, hxy⟩
    (touch_singleton_ring M e0 mb hxb) (touch_singleton_ring M e0 md hxd)
    (touch_singleton_ring M e0 ma hya).symm t11 (TR hcd (by omega)).symm
    (touch_singleton_ring M e0 mc hyc).symm (TR hab hbc).symm (TR hbc hcd)

end Contracted

end LeanPool.K5MinorFreeChoosability
