/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.Star

/-!
# Hall's lemma

**Hall (1943).**  A graph without a separation of order at most two, with at least six
vertices and a `K_5` minor, has a `K_{3,3}` minor (`isMinor_K33_of_noSmallSep`).

Proof.  Take a `K_5` model of minimum size; without a `K_{3,3}` minor every branch set is a
star (`exists_branchStar`).  If some ray `R_{ab}` is nonempty, the set `Y` of vertices
reachable from it through `R_{ab} ∪ R_{ba}` and the vertices outside the model has, since
`{z_a, z_b}` is not a separator, a neighbour `u ∉ {z_a, z_b}` outside `Y`; according to
where `u` lies, `Y` (possibly enlarged by the ray containing `u`) is a bridge touching three
(shrunk) branch sets (`isMinor_K33_of_bridge`).  If all rays are empty the model consists
of five vertices; a component of the remaining vertices has at least three neighbours
among them, again a bridge.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} {G : SimpleGraph V}

/-! ### Reachability closures -/

open Classical in
/-- The vertices of `W` reachable from `x` inside `W`. -/
noncomputable def reachIn (G : SimpleGraph V) (W : Finset V) (x : V) : Finset V :=
  W.filter fun y => RIn G ↑W x y

theorem mem_reachIn {W : Finset V} {x y : V} : y ∈ reachIn G W x ↔ y ∈ W ∧ RIn G ↑W x y := by
  unfold reachIn; simp

theorem reachIn_sub (W : Finset V) (x : V) : reachIn G W x ⊆ W := fun _ hy =>
  (mem_reachIn.1 hy).1

theorem reachIn_conn {W : Finset V} {x : V} (hx : x ∈ W) : ConnSet G ↑(reachIn G W x) := by
  have h := connSet_reach G (↑W) (a := x) (by exact_mod_cast hx)
  have he : (↑(reachIn G W x) : Set V) = {y | y ∈ (↑W : Set V) ∧ RIn G ↑W x y} := by
    ext y; simp [mem_reachIn]
  rw [he]; exact h

theorem mem_reachIn_self {W : Finset V} {x : V} (hx : x ∈ W) : x ∈ reachIn G W x :=
  mem_reachIn.2 ⟨hx, RIn.refl _⟩

theorem reachIn_closed {W : Finset V} {x y w : V} (hy : y ∈ reachIn G W x) (hw : w ∈ W)
    (hyw : G.Adj y w) : w ∈ reachIn G W x := by
  obtain ⟨hyW, hxy⟩ := mem_reachIn.1 hy
  exact mem_reachIn.2 ⟨hw, hxy.tail hyw (by exact_mod_cast hyW) (by exact_mod_cast hw)⟩

/-- A connected subset of `W` meeting the closure lies in it. -/
theorem sub_reachIn {W Q : Finset V} {x q : V} (hQW : Q ⊆ W) (hQ : ConnSet G ↑Q)
    (hq : q ∈ Q) (hqR : q ∈ reachIn G W x) : Q ⊆ reachIn G W x := by
  intro y hy
  obtain ⟨-, hxq⟩ := mem_reachIn.1 hqR
  exact mem_reachIn.2 ⟨hQW hy, hxq.trans ((hQ.2 q hq y hy).mono_set (by exact_mod_cast hQW))⟩

variable [DecidableEq V]

/-! ### Rays: shrunk branch sets -/

namespace BranchStar

variable {M : CliqueMinorModel G 5} {i : Fin 5} (st : BranchStar M i)

theorem rest_conn1 (j : Fin 5) : ConnSet G ↑(M.branch i \ st.R j) := by
  simpa using st.rest_conn {j}

theorem rest_conn2 (j k : Fin 5) : ConnSet G ↑(M.branch i \ (st.R j ∪ st.R k)) := by
  have h := st.rest_conn {j, k}
  rwa [Finset.biUnion_insert, Finset.singleton_biUnion] at h

theorem rest_touch1 {j k : Fin 5} (hki : k ≠ i) (hkj : k ≠ j) :
    Touch G (M.branch i \ st.R j) (M.branch k) := by
  simpa using st.rest_touch {j} hki (by simpa using Ne.symm hkj)

theorem rest_touch2 {j l k : Fin 5} (hki : k ≠ i) (hkj : k ≠ j) (hkl : k ≠ l) :
    Touch G (M.branch i \ (st.R j ∪ st.R l)) (M.branch k) := by
  have h := st.rest_touch {j, l} hki (by
    intro m hm
    rcases Finset.mem_insert.1 hm with h | h
    · rw [h]; exact Ne.symm hkj
    · rw [Finset.mem_singleton.1 h]; exact Ne.symm hkl)
  rwa [Finset.biUnion_insert, Finset.singleton_biUnion] at h

theorem z_mem_rest1 (j : Fin 5) : st.z ∈ M.branch i \ st.R j :=
  Finset.mem_sdiff.2 ⟨st.z_mem, st.z_not_mem j⟩

theorem z_mem_rest2 (j k : Fin 5) : st.z ∈ M.branch i \ (st.R j ∪ st.R k) :=
  Finset.mem_sdiff.2 ⟨st.z_mem, by simp [st.z_not_mem j, st.z_not_mem k]⟩

end BranchStar

/-! ### Hall's lemma -/

/-- **Hall's lemma.**  Let `G` be a graph whose edges lie inside the finite vertex set `S`,
with `|S| ≥ 6` and no separation of `S` of order at most two.  If `G` has a `K_5` minor,
then `G` has a `K_{3,3}` minor. -/
theorem isMinor_K33_of_noSmallSep {S : Finset V} (hS : ∀ u v, G.Adj u v → u ∈ S)
    (hsep : NoSmallSep G S) (hcard : 6 ≤ S.card) (hK5 : Nonempty (CliqueMinorModel G 5)) :
    IsMinor K33 G := by
  classical
  by_contra hK
  obtain ⟨M, hM⟩ := exists_isMinimalK5 hK5
  have st : ∀ i, BranchStar M i := fun i => (exists_branchStar hM hK i).some
  have hBS : ∀ i, M.branch i ⊆ S := fun i x hx =>
    M.mem_of_edges (by norm_num) (↑S) (fun x y h => hS x y h) i hx
  have DB := M.branch_disjoint
  have disjB : ∀ {i j : Fin 5} {x : V}, i ≠ j → x ∈ M.branch i → x ∉ M.branch j :=
    fun hij hx hx' => Finset.disjoint_left.1 (DB _ _ hij) hx hx'
  set D := S.filter fun v => ∀ i, v ∉ M.branch i with hD
  have hDB : ∀ {i : Fin 5} {x : V}, x ∈ D → x ∉ M.branch i := fun hx =>
    (Finset.mem_filter.1 hx).2 _
  by_cases hA : ∃ a b, a ≠ b ∧ ((st a).R b).Nonempty
  · obtain ⟨a, b, hab, x₀, hx₀⟩ := hA
    set Q₁ := (st a).R b with hQ₁
    set Q₂ := (st b).R a with hQ₂
    set W := Q₁ ∪ Q₂ ∪ D with hW
    set Y := reachIn G W x₀ with hY
    have hQ₁a : Q₁ ⊆ M.branch a := (st a).R_sub_branch b
    have hQ₂b : Q₂ ⊆ M.branch b := (st b).R_sub_branch a
    have hQ₁W : Q₁ ⊆ W := fun x hx => by simp [hW, hx]
    have hQ₂W : Q₂ ⊆ W := fun x hx => by simp [hW, hx]
    have hQ₁ne : Q₁.Nonempty := ⟨x₀, hx₀⟩
    have hx₀W : x₀ ∈ W := hQ₁W hx₀
    have hQ₁Y : Q₁ ⊆ Y := sub_reachIn hQ₁W ((st a).conn b hQ₁ne) hx₀ (mem_reachIn_self hx₀W)
    have hYW : Y ⊆ W := reachIn_sub W x₀
    have hYconn : ConnSet G ↑Y := reachIn_conn hx₀W
    -- membership of `W` in the branch sets
    have hWbranch : ∀ {x : V} {c : Fin 5}, x ∈ W → x ∈ M.branch c → (c = a ∧ x ∈ Q₁) ∨
        (c = b ∧ x ∈ Q₂) := by
      intro x c hxW hxc
      simp only [hW, Finset.mem_union] at hxW
      rcases hxW with (hx | hx) | hx
      · by_cases hca : c = a
        · exact Or.inl ⟨hca, hx⟩
        · exact absurd hxc (disjB (Ne.symm hca) (hQ₁a hx))
      · by_cases hcb : c = b
        · exact Or.inr ⟨hcb, hx⟩
        · exact absurd hxc (disjB (Ne.symm hcb) (hQ₂b hx))
      · exact absurd hxc (hDB hx)
    have hYdisj : ∀ c, c ≠ a → c ≠ b → Disjoint Y (M.branch c) := by
      intro c hca hcb
      rw [Finset.disjoint_left]
      intro x hxY hxc
      rcases hWbranch (hYW hxY) hxc with ⟨h, -⟩ | ⟨h, -⟩
      · exact hca h
      · exact hcb h
    have hYdisja : Disjoint Y (M.branch a \ Q₁) := by
      rw [Finset.disjoint_left]
      intro x hxY hx
      obtain ⟨hxa, hxQ⟩ := Finset.mem_sdiff.1 hx
      rcases hWbranch (hYW hxY) hxa with ⟨-, h⟩ | ⟨h, -⟩
      · exact hxQ h
      · exact hab h
    have hYdisjb : Disjoint Y (M.branch b \ Q₂) := by
      rw [Finset.disjoint_left]
      intro x hxY hx
      obtain ⟨hxb, hxQ⟩ := Finset.mem_sdiff.1 hx
      rcases hWbranch (hYW hxY) hxb with ⟨h, -⟩ | ⟨-, h⟩
      · exact hab h.symm
      · exact hxQ h
    -- `Y` touches the shrunk branch sets `a` and `b`
    have T1 : Touch G Y (M.branch a \ Q₁) := by
      obtain ⟨w, hw, z', hz', hwz⟩ := (st a).touch_center b hQ₁ne
      rw [Finset.mem_singleton] at hz'
      subst hz'
      exact ⟨w, hQ₁Y hw, _, (st a).z_mem_rest1 b, hwz⟩
    have T2 : Touch G Y (M.branch b \ Q₂) := by
      obtain ⟨w, hw, v, hv, hwv⟩ := (st a).touch_target b hQ₁ne
      by_cases hvQ : v ∈ Q₂
      · have hvY : v ∈ Y := reachIn_closed (hQ₁Y hw) (hQ₂W hvQ) hwv
        have hQ₂ne : Q₂.Nonempty := ⟨v, hvQ⟩
        have hQ₂Y : Q₂ ⊆ Y := sub_reachIn hQ₂W ((st b).conn a hQ₂ne) hvQ hvY
        obtain ⟨w', hw', z', hz', hwz⟩ := (st b).touch_center a hQ₂ne
        rw [Finset.mem_singleton] at hz'
        subst hz'
        exact ⟨w', hQ₂Y hw', _, (st b).z_mem_rest1 a, hwz⟩
      · exact ⟨w, hQ₁Y hw, v, Finset.mem_sdiff.2 ⟨hv, hvQ⟩, hwv⟩
    -- an outside neighbour of `Y` other than the two centres
    obtain ⟨c₀, hc₀a, hc₀b⟩ := fin5_exists_third a b
    have hzW : ∀ c, (st c).z ∉ W := by
      intro c hzW
      rcases hWbranch hzW (st c).z_mem with ⟨rfl, h⟩ | ⟨rfl, h⟩
      · exact (st _).z_not_mem _ h
      · exact (st _).z_not_mem _ h
    have hzne : ∀ {c c' : Fin 5}, c ≠ c' → (st c).z ≠ (st c').z := fun h he =>
      disjB h (st _).z_mem (he ▸ (st _).z_mem)
    have hbridge : ∃ y ∈ Y, ∃ u, G.Adj y u ∧ u ∉ Y ∧ u ≠ (st a).z ∧ u ≠ (st b).z := by
      by_contra hno
      push Not at hno
      refine false_of_noSmallSep hsep Y {(st a).z, (st b).z}
        (fun x hx => ?_) (fun x hx => ?_) ?_ ?_ ⟨x₀, hQ₁Y hx₀⟩ ?_ ?_
      · rcases Finset.mem_union.1 (hYW hx) with h | h
        · rcases Finset.mem_union.1 h with h | h
          · exact hBS a (hQ₁a h)
          · exact hBS b (hQ₂b h)
        · exact (Finset.mem_filter.1 h).1
      · rcases Finset.mem_insert.1 hx with rfl | h
        · exact hBS a (st a).z_mem
        · rw [Finset.mem_singleton.1 h]; exact hBS b (st b).z_mem
      · rw [Finset.disjoint_left]
        intro x hxY hx
        rcases Finset.mem_insert.1 hx with rfl | h
        · exact hzW a (hYW hxY)
        · rw [Finset.mem_singleton.1 h] at hxY; exact hzW b (hYW hxY)
      · exact Finset.card_le_two
      · refine ⟨(st c₀).z, hBS c₀ (st c₀).z_mem, fun h => hzW c₀ (hYW h), ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hzne hc₀a, hzne hc₀b⟩
      · intro y hy u hyu
        by_cases huY : u ∈ Y
        · exact Or.inl huY
        · right
          by_cases hua : u = (st a).z
          · simp [hua]
          · simp [hno y hy u hyu huY hua]
    obtain ⟨y, hy, u, hyu, huY, hua, hub⟩ := hbridge
    have huS : u ∈ S := hS u y hyu.symm
    have huW : u ∉ W := fun h => huY (reachIn_closed hy h hyu)
    have huD : u ∉ D := fun h => huW (by simp [hW, h])
    have huQ₁ : u ∉ Q₁ := fun h => huW (hQ₁W h)
    have huQ₂ : u ∉ Q₂ := fun h => huW (hQ₂W h)
    obtain ⟨c, huc⟩ : ∃ c, u ∈ M.branch c := by
      by_contra h
      push Not at h
      exact huD (Finset.mem_filter.2 ⟨huS, h⟩)
    by_cases hca : c = a
    · -- `u` lies on another ray of `B_a`
      subst hca
      obtain ⟨k, hk⟩ := (st c).cover u huc hua
      have hkc : k ≠ c := fun h => by rw [h, (st c).R_self] at hk; simp at hk
      have hkb : k ≠ b := fun h => huQ₁ (by rw [hQ₁, ← h]; exact hk)
      obtain ⟨d, e, hdc, hdb, hdk, hec, heb, hek, hde⟩ := fin5_exists_rest c b k hab
        (Ne.symm hkc) (Ne.symm hkb)
      set Rk := (st c).R k
      have hRk : Rk.Nonempty := ⟨u, hk⟩
      have hRkc : Rk ⊆ M.branch c := (st c).R_sub_branch k
      refine hK (isMinor_K33_of_bridge M hab (Ne.symm hkc) (Ne.symm hdc) (Ne.symm hec)
        (Ne.symm hkb) (Ne.symm hdb) (Ne.symm heb) (Ne.symm hdk) (Ne.symm hek) hde
        (Y ∪ Rk) (M.branch c \ (Q₁ ∪ Rk)) (M.branch b \ Q₂) Finset.sdiff_subset
        Finset.sdiff_subset (hYconn.union_of_touch ((st c).conn k hRk) ⟨y, hy, u, hk, hyu⟩)
        ((st c).rest_conn2 b k) ((st b).rest_conn1 c) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [Finset.disjoint_union_left]
        refine ⟨hYdisja.mono_right (Finset.sdiff_subset_sdiff subset_rfl
          Finset.subset_union_left), ?_⟩
        exact Finset.disjoint_left.2 fun x hx hx' => (Finset.mem_sdiff.1 hx').2
          (Finset.mem_union_right _ hx)
      · rw [Finset.disjoint_union_left]
        exact ⟨hYdisjb, (DB c b hab).mono hRkc Finset.sdiff_subset⟩
      · rw [Finset.disjoint_union_left]
        exact ⟨hYdisj k hkc hkb, (DB c k (Ne.symm hkc)).mono_left hRkc⟩
      · rw [Finset.disjoint_union_left]
        exact ⟨hYdisj d hdc hdb, (DB c d (Ne.symm hdc)).mono_left hRkc⟩
      · rw [Finset.disjoint_union_left]
        exact ⟨hYdisj e hec heb, (DB c e (Ne.symm hec)).mono_left hRkc⟩
      · obtain ⟨w, hw, z', hz', hwz⟩ := (st c).touch_center k hRk
        rw [Finset.mem_singleton] at hz'
        subst hz'
        exact ⟨w, Finset.mem_union_right _ hw, _, (st c).z_mem_rest2 b k, hwz⟩
      · exact T2.mono Finset.subset_union_left subset_rfl
      · exact ((st c).touch_target k hRk).mono Finset.subset_union_right subset_rfl
      · exact ((st c).rest_touch2 hdc hdb hdk).symm
      · exact ((st b).rest_touch1 hdb hdc).symm
      · exact ((st c).rest_touch2 hec heb hek).symm
      · exact ((st b).rest_touch1 heb hec).symm
    by_cases hcb : c = b
    · -- `u` lies on another ray of `B_b`
      subst hcb
      obtain ⟨k, hk⟩ := (st c).cover u huc hub
      have hkc : k ≠ c := fun h => by rw [h, (st c).R_self] at hk; simp at hk
      have hka : k ≠ a := fun h => huQ₂ (by rw [hQ₂, ← h]; exact hk)
      obtain ⟨d, e, hda, hdc, hdk, hea, hec, hek, hde⟩ := fin5_exists_rest a c k hab
        (Ne.symm hka) (Ne.symm hkc)
      set Rk := (st c).R k
      have hRk : Rk.Nonempty := ⟨u, hk⟩
      have hRkc : Rk ⊆ M.branch c := (st c).R_sub_branch k
      refine hK (isMinor_K33_of_bridge M hab (Ne.symm hka) (Ne.symm hda) (Ne.symm hea)
        (Ne.symm hkc) (Ne.symm hdc) (Ne.symm hec) (Ne.symm hdk) (Ne.symm hek) hde
        (Y ∪ Rk) (M.branch a \ Q₁) (M.branch c \ (Q₂ ∪ Rk)) Finset.sdiff_subset
        Finset.sdiff_subset (hYconn.union_of_touch ((st c).conn k hRk) ⟨y, hy, u, hk, hyu⟩)
        ((st a).rest_conn1 c) ((st c).rest_conn2 a k) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [Finset.disjoint_union_left]
        exact ⟨hYdisja, (DB c a (Ne.symm hab)).mono hRkc Finset.sdiff_subset⟩
      · rw [Finset.disjoint_union_left]
        refine ⟨hYdisjb.mono_right (Finset.sdiff_subset_sdiff subset_rfl
          Finset.subset_union_left), ?_⟩
        exact Finset.disjoint_left.2 fun x hx hx' => (Finset.mem_sdiff.1 hx').2
          (Finset.mem_union_right _ hx)
      · rw [Finset.disjoint_union_left]
        exact ⟨hYdisj k hka hkc, (DB c k (Ne.symm hkc)).mono_left hRkc⟩
      · rw [Finset.disjoint_union_left]
        exact ⟨hYdisj d hda hdc, (DB c d (Ne.symm hdc)).mono_left hRkc⟩
      · rw [Finset.disjoint_union_left]
        exact ⟨hYdisj e hea hec, (DB c e (Ne.symm hec)).mono_left hRkc⟩
      · exact T1.mono Finset.subset_union_left subset_rfl
      · obtain ⟨w, hw, z', hz', hwz⟩ := (st c).touch_center k hRk
        rw [Finset.mem_singleton] at hz'
        subst hz'
        exact ⟨w, Finset.mem_union_right _ hw, _, (st c).z_mem_rest2 a k, hwz⟩
      · exact ((st c).touch_target k hRk).mono Finset.subset_union_right subset_rfl
      · exact ((st a).rest_touch1 hda hdc).symm
      · exact ((st c).rest_touch2 hdc hda hdk).symm
      · exact ((st a).rest_touch1 hea hec).symm
      · exact ((st c).rest_touch2 hec hea hek).symm
    · -- `u` lies in a third branch set
      obtain ⟨d, e, hda, hdb, hdc, hea, heb, hec, hde⟩ := fin5_exists_rest a b c hab
        (Ne.symm hca) (Ne.symm hcb)
      exact hK (isMinor_K33_of_bridge M hab (Ne.symm hca) (Ne.symm hda) (Ne.symm hea)
        (Ne.symm hcb) (Ne.symm hdb) (Ne.symm heb) (Ne.symm hdc) (Ne.symm hec) hde
        Y (M.branch a \ Q₁) (M.branch b \ Q₂) Finset.sdiff_subset Finset.sdiff_subset hYconn
        ((st a).rest_conn1 b) ((st b).rest_conn1 a) hYdisja hYdisjb (hYdisj c hca hcb)
        (hYdisj d hda hdb) (hYdisj e hea heb) T1 T2 ⟨y, hy, u, huc, hyu⟩
        ((st a).rest_touch1 hda hdb).symm ((st b).rest_touch1 hdb hda).symm
        ((st a).rest_touch1 hea heb).symm ((st b).rest_touch1 heb hea).symm)
  · -- all rays are empty: the model has five vertices
    push Not at hA
    have hsing : ∀ i, ∀ x ∈ M.branch i, x = (st i).z := by
      intro i x hx
      by_contra hxz
      obtain ⟨j, hj⟩ := (st i).cover x hx hxz
      by_cases hji : j = i
      · rw [hji, (st i).R_self] at hj; simp at hj
      · rw [hA i j (Ne.symm hji)] at hj; simp at hj
    set Z := Finset.univ.image fun i => (st i).z with hZ
    have hzinj : Function.Injective fun i => (st i).z := by
      intro i j hij
      by_contra hne
      exact disjB hne (st i).z_mem (by simpa [← hij] using (st j).z_mem)
    have hZcard : Z.card = 5 := by
      rw [hZ, Finset.card_image_of_injective _ hzinj]; simp
    obtain ⟨x₀, hx₀S, hx₀Z⟩ : ∃ x ∈ S, x ∉ Z := by
      by_contra h
      push Not at h
      have := Finset.card_le_card (show S ⊆ Z from h)
      omega
    have hx₀D : x₀ ∈ D := by
      refine Finset.mem_filter.2 ⟨hx₀S, fun i hi => hx₀Z ?_⟩
      rw [hsing i x₀ hi]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    set Y := reachIn G D x₀ with hY
    have hYD : Y ⊆ D := reachIn_sub D x₀
    set N := Z.filter fun v => ∃ y ∈ Y, G.Adj y v with hN
    have hNZ : N ⊆ Z := Finset.filter_subset _ _
    have hZS : Z ⊆ S := by
      intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      exact hBS i (st i).z_mem
    have hZD : ∀ v ∈ Z, v ∉ D := by
      intro v hv hvD
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      exact hDB hvD (st i).z_mem
    by_cases hNc : N.card ≤ 2
    · refine false_of_noSmallSep hsep Y N (hYD.trans (Finset.filter_subset _ _))
        (hNZ.trans hZS) ?_ hNc ⟨x₀, mem_reachIn_self hx₀D⟩ ?_ ?_
      · rw [Finset.disjoint_left]
        intro x hxY hxN
        exact hZD x (hNZ hxN) (hYD hxY)
      · obtain ⟨v, hvZ, hvN⟩ : ∃ v ∈ Z, v ∉ N := by
          by_contra h
          push Not at h
          have := Finset.card_le_card (show Z ⊆ N from h)
          omega
        exact ⟨v, hZS hvZ, fun h => hZD v hvZ (hYD h), hvN⟩
      · intro y hy u hyu
        have huS : u ∈ S := hS u y hyu.symm
        by_cases huD : u ∈ D
        · exact Or.inl (reachIn_closed hy huD hyu)
        · right
          obtain ⟨c, huc⟩ : ∃ c, u ∈ M.branch c := by
            by_contra h
            push Not at h
            exact huD (Finset.mem_filter.2 ⟨huS, h⟩)
          refine Finset.mem_filter.2 ⟨?_, y, hy, hyu⟩
          rw [hsing c u huc]; exact Finset.mem_image_of_mem _ (Finset.mem_univ c)
    · push Not at hNc
      obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.1 hNc
      obtain ⟨hpZ, yp, hyp, hpa⟩ := Finset.mem_filter.1 hp
      obtain ⟨hqZ, yq, hyq, hqa⟩ := Finset.mem_filter.1 hq
      obtain ⟨hrZ, yr, hyr, hra⟩ := Finset.mem_filter.1 hr
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hpZ
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hqZ
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hrZ
      have hab : a ≠ b := fun h => hpq (by rw [h])
      have hac : a ≠ c := fun h => hpr (by rw [h])
      have hbc : b ≠ c := fun h => hqr (by rw [h])
      obtain ⟨d, e, hda, hdb, hdc, hea, heb, hec, hde⟩ := fin5_exists_rest a b c hab hac hbc
      have hYdisj : ∀ i, Disjoint Y (M.branch i) := fun i =>
        Finset.disjoint_left.2 fun x hx hx' => hDB (hYD hx) hx'
      exact hK (isMinor_K33_of_bridge M hab hac (Ne.symm hda) (Ne.symm hea) hbc
        (Ne.symm hdb) (Ne.symm heb) (Ne.symm hdc) (Ne.symm hec) hde Y (M.branch a) (M.branch b)
        subset_rfl subset_rfl (reachIn_conn hx₀D) (M.connSet a) (M.connSet b) (hYdisj a)
        (hYdisj b) (hYdisj c) (hYdisj d) (hYdisj e) ⟨yp, hyp, _, (st a).z_mem, hpa⟩
        ⟨yq, hyq, _, (st b).z_mem, hqa⟩ ⟨yr, hyr, _, (st c).z_mem, hra⟩
        (M.branch_adjacent d a hda) (M.branch_adjacent d b hdb) (M.branch_adjacent e a hea)
        (M.branch_adjacent e b heb))

end LeanPool.K5MinorFreeChoosability
