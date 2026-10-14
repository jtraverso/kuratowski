/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.K5Model

/-!
# Star structure of the branch sets of a minimal `K_5` model

Let `M` be a `K_5` model of minimum total size in a graph without a `K_{3,3}` minor.  Then
every branch set `B_i` is a *star*: it has a centre `z` and disjoint connected "rays"
`R j` (`j ≠ i`, possibly empty) covering `B_i \ {z}`, such that each nonempty ray touches
the centre and the branch set `B_j`, touches no other branch set `B_k`, and the centre
touches `B_j` whenever `R j` is empty (`exists_branchStar`).

The proof chooses a minimal "heavy" part `X` of `B_i` (connected, with connected
complement in `B_i`, touching two other branch sets).  The pieces of `B_i` left after
removing a suitable centre `z ∈ X` touch at most one other branch set each: for the
complement this is the split lemma (`isMinor_K33_of_split`), for the components of
`X \ {z}` it is the minimality of `X`.  Minimality of the model then shows that every
piece touches exactly one other branch set and different pieces touch different ones.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A star decomposition of the branch set `i` of a `K_5` model. -/
structure BranchStar (M : CliqueMinorModel G 5) (i : Fin 5) where
  z : V
  R : Fin 5 → Finset V
  z_mem : z ∈ M.branch i
  R_sub : ∀ j, R j ⊆ (M.branch i).erase z
  R_self : R i = ∅
  R_disj : ∀ j k, j ≠ k → Disjoint (R j) (R k)
  cover : ∀ x ∈ M.branch i, x ≠ z → ∃ j, x ∈ R j
  touch_z : ∀ j, j ≠ i → R j = ∅ → Touch G {z} (M.branch j)
  conn : ∀ j, (R j).Nonempty → ConnSet G ↑(R j)
  touch_center : ∀ j, (R j).Nonempty → Touch G (R j) {z}
  touch_target : ∀ j, (R j).Nonempty → Touch G (R j) (M.branch j)
  no_other : ∀ j k, k ≠ i → k ≠ j → ¬ Touch G (R j) (M.branch k)

namespace BranchStar

variable {M : CliqueMinorModel G 5} {i : Fin 5} (st : BranchStar M i)

theorem z_not_mem (j : Fin 5) : st.z ∉ st.R j := fun h => by
  simpa using st.R_sub j h

theorem R_sub_branch (j : Fin 5) : st.R j ⊆ M.branch i :=
  (st.R_sub j).trans (Finset.erase_subset _ _)

/-- Removing any family of rays from a star leaves a connected set. -/
theorem rest_conn (J : Finset (Fin 5)) : ConnSet G ↑(M.branch i \ J.biUnion st.R) := by
  have hz : st.z ∈ M.branch i \ J.biUnion st.R := by
    refine Finset.mem_sdiff.2 ⟨st.z_mem, ?_⟩
    simp only [Finset.mem_biUnion, not_exists, not_and]
    exact fun j _ => st.z_not_mem j
  have key : ∀ y ∈ M.branch i \ J.biUnion st.R, RIn G ↑(M.branch i \ J.biUnion st.R) y st.z := by
    intro y hy
    obtain ⟨hyB, hyJ⟩ := Finset.mem_sdiff.1 hy
    by_cases hyz : y = st.z
    · subst hyz; exact RIn.refl _
    obtain ⟨k, hk⟩ := st.cover y hyB hyz
    have hkJ : k ∉ J := fun hkJ => hyJ (Finset.mem_biUnion.2 ⟨k, hkJ, hk⟩)
    have hsub : st.R k ⊆ M.branch i \ J.biUnion st.R := by
      intro x hx
      refine Finset.mem_sdiff.2 ⟨st.R_sub_branch k hx, ?_⟩
      simp only [Finset.mem_biUnion, not_exists, not_and]
      intro j hj hxj
      have hjk : j ≠ k := fun h => hkJ (h ▸ hj)
      exact Finset.disjoint_left.1 (st.R_disj j k hjk) hxj hx
    have hne : (st.R k).Nonempty := ⟨y, hk⟩
    obtain ⟨w, hw, z', hz', hwz⟩ := st.touch_center k hne
    rw [Finset.mem_singleton] at hz'
    subst hz'
    exact (((st.conn k hne).2 y hk w hw).mono_set (by exact_mod_cast hsub)).tail hwz
      (by exact_mod_cast hsub hw) (by exact_mod_cast hz)
  refine ⟨⟨st.z, by exact_mod_cast hz⟩, fun x hx y hy => ?_⟩
  exact (key x (by exact_mod_cast hx)).trans (key y (by exact_mod_cast hy)).symm

/-- A branch set with some rays removed still touches `B_k` if no removed ray points
to `k`. -/
theorem rest_touch (J : Finset (Fin 5)) {k : Fin 5} (hki : k ≠ i)
    (hkJ : ∀ j ∈ J, j ≠ k) :
    Touch G (M.branch i \ J.biUnion st.R) (M.branch k) := by
  obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent i k hki.symm
  refine ⟨u, Finset.mem_sdiff.2 ⟨hu, ?_⟩, v, hv, huv⟩
  simp only [Finset.mem_biUnion, not_exists, not_and]
  intro j hj huj
  exact st.no_other j k hki (hkJ j hj).symm ⟨u, huj, v, hv, huv⟩

end BranchStar

/-! ### Construction -/

namespace StarConstruction

variable (M : CliqueMinorModel G 5) (i : Fin 5)

/-- `X` touches two branch sets other than `B_i`. -/
def TwoC (X : Finset V) : Prop :=
  ∃ j k, j ≠ k ∧ j ≠ i ∧ k ≠ i ∧ Touch G X (M.branch j) ∧ Touch G X (M.branch k)

/-- A heavy part of `B_i`. -/
def Heavy (X : Finset V) : Prop :=
  X ⊆ M.branch i ∧ ConnSet G ↑X ∧ (M.branch i \ X = ∅ ∨ ConnSet G ↑(M.branch i \ X)) ∧
    TwoC M i X

theorem heavy_branch : Heavy M i (M.branch i) := by
  obtain ⟨j, k, hjk, hji, hki⟩ := fin5_exists_two_ne i
  exact ⟨subset_rfl, M.connSet i, Or.inl (Finset.sdiff_self _), j, k, hjk, hji, hki,
    M.branch_adjacent i j hji.symm, M.branch_adjacent i k hki.symm⟩

/-- The data of the construction: a heavy part `X` of minimum size and a centre `z ∈ X`
adjacent to the rest of `B_i` (if it is nonempty). -/
structure Setup where
  X : Finset V
  z : V
  heavy : Heavy M i X
  min : ∀ Y, Heavy M i Y → X.card ≤ Y.card
  z_mem : z ∈ X
  z_adj : (M.branch i \ X).Nonempty → ∃ u ∈ M.branch i \ X, G.Adj z u

theorem exists_setup : Nonempty (Setup M i) := by
  classical
  have hex : ∃ n, ∃ X, Heavy M i X ∧ X.card = n := ⟨_, _, heavy_branch M i, rfl⟩
  obtain ⟨X, hX, hXc⟩ := Nat.find_spec hex
  have hmin : ∀ Y, Heavy M i Y → X.card ≤ Y.card := fun Y hY => by
    rw [hXc]; exact Nat.find_min' hex ⟨Y, hY, rfl⟩
  obtain ⟨⟨x₀, hx₀⟩, hXc'⟩ := hX.2.1
  by_cases hU : (M.branch i \ X).Nonempty
  · obtain ⟨u₀, hu₀⟩ := hU
    have hr := (M.connSet i).2 x₀ (hX.1 hx₀) u₀ (Finset.mem_sdiff.1 hu₀).1
    obtain ⟨p, q, -, hp, hpX, hq, hqX, hpq⟩ := hr.exit (P := ↑X) hx₀
      (by exact_mod_cast (Finset.mem_sdiff.1 hu₀).2)
    exact ⟨⟨X, p, hX, hmin, hpX, fun _ => ⟨q, Finset.mem_sdiff.2 ⟨hq, hqX⟩, hpq⟩⟩⟩
  · exact ⟨⟨X, x₀, hX, hmin, hx₀, fun h => absurd h hU⟩⟩

variable {M i} (s : Setup M i)

/-- The rest `B_i \ X`. -/
def U : Finset V := M.branch i \ s.X

/-- `X \ {z}`. -/
def Xz : Finset V := s.X.erase s.z

open Classical in
/-- The component of `x` in `X \ {z}`. -/
noncomputable def comp (x : V) : Finset V := (Xz s).filter fun y => RIn G ↑(Xz s) x y

open Classical in
/-- The piece of `B_i \ {z}` containing `x`. -/
noncomputable def piece (x : V) : Finset V := if x ∈ U s then U s else comp s x

theorem X_sub : s.X ⊆ M.branch i := s.heavy.1

theorem X_conn : ConnSet G ↑s.X := s.heavy.2.1

theorem U_conn (h : (U s).Nonempty) : ConnSet G ↑(U s) := by
  rcases s.heavy.2.2.1 with h' | h'
  · exact absurd h' h.ne_empty
  · exact h'

theorem mem_comp {x y : V} : y ∈ comp s x ↔ y ∈ Xz s ∧ RIn G ↑(Xz s) x y := by
  unfold comp; simp

theorem comp_sub (x : V) : comp s x ⊆ Xz s := fun _ hy => ((mem_comp s).1 hy).1

theorem mem_comp_self {x : V} (hx : x ∈ Xz s) : x ∈ comp s x :=
  (mem_comp s).2 ⟨hx, RIn.refl _⟩

theorem comp_conn {x : V} (hx : x ∈ Xz s) : ConnSet G ↑(comp s x) := by
  have h := connSet_reach G (↑(Xz s)) (a := x) (by exact_mod_cast hx)
  have he : (↑(comp s x) : Set V) = {y | y ∈ (↑(Xz s) : Set V) ∧ RIn G ↑(Xz s) x y} := by
    ext y; simp [mem_comp]
  rw [he]; exact h

theorem comp_eq {x y : V} (hy : y ∈ comp s x) : comp s y = comp s x := by
  obtain ⟨hyX, hxy⟩ := (mem_comp s).1 hy
  ext w
  simp only [mem_comp]
  constructor
  · rintro ⟨hw, hyw⟩; exact ⟨hw, hxy.trans hyw⟩
  · rintro ⟨hw, hxw⟩; exact ⟨hw, hxy.symm.trans hxw⟩

theorem comp_disj {x y : V} (hy : y ∉ comp s x) : Disjoint (comp s x) (comp s y) := by
  rw [Finset.disjoint_left]
  intro w hwx hwy
  obtain ⟨-, hxw⟩ := (mem_comp s).1 hwx
  obtain ⟨-, hyw⟩ := (mem_comp s).1 hwy
  have hyX : y ∈ Xz s := by
    have := (mem_comp s).1 hwy
    exact hyw.symm.mem this.1
  exact hy ((mem_comp s).2 ⟨hyX, hxw.trans hyw.symm⟩)

theorem comp_touch_z {x : V} (hx : x ∈ Xz s) : ∃ w ∈ comp s x, G.Adj w s.z := by
  have hxX : x ∈ s.X := Finset.mem_of_mem_erase hx
  have hr := (X_conn s).2 x hxX s.z s.z_mem
  have hzc : s.z ∉ comp s x := fun h => by
    have := comp_sub s x h
    simp [Xz] at this
  obtain ⟨p, q, hxp, hp, hpP, hq, hqP, hpq⟩ := hr.exit (P := ↑(comp s x))
    (by exact_mod_cast mem_comp_self s hx) (by exact_mod_cast hzc)
  by_cases hqz : q = s.z
  · subst hqz; exact ⟨p, by exact_mod_cast hpP, hpq⟩
  · exfalso
    have hpc : p ∈ comp s x := by exact_mod_cast hpP
    have hqX : q ∈ Xz s := Finset.mem_erase.2 ⟨hqz, by exact_mod_cast hq⟩
    obtain ⟨hpX, hxp'⟩ := (mem_comp s).1 hpc
    exact hqP (by exact_mod_cast (mem_comp s).2 ⟨hqX, hxp'.tail hpq
      (by exact_mod_cast hpX) (by exact_mod_cast hqX)⟩)

theorem mem_U_or_Xz {x : V} (hx : x ∈ (M.branch i).erase s.z) : x ∈ U s ∨ x ∈ Xz s := by
  by_cases hxX : x ∈ s.X
  · exact Or.inr (Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hx).1, hxX⟩)
  · exact Or.inl (Finset.mem_sdiff.2 ⟨Finset.mem_of_mem_erase hx, hxX⟩)

theorem Xz_not_U {x : V} (hx : x ∈ Xz s) : x ∉ U s := fun h =>
  (Finset.mem_sdiff.1 h).2 (Finset.mem_of_mem_erase hx)

theorem piece_U {x : V} (hx : x ∈ U s) : piece s x = U s := by
  unfold piece; simp [hx]

theorem piece_comp {x : V} (hx : x ∈ Xz s) : piece s x = comp s x := by
  unfold piece; simp [Xz_not_U s hx]

theorem mem_piece_self {x : V} (hx : x ∈ (M.branch i).erase s.z) : x ∈ piece s x := by
  rcases mem_U_or_Xz s hx with h | h
  · rw [piece_U s h]; exact h
  · rw [piece_comp s h]; exact mem_comp_self s h

theorem z_not_U : s.z ∉ U s := fun h => (Finset.mem_sdiff.1 h).2 s.z_mem

theorem piece_sub {x : V} (hx : x ∈ (M.branch i).erase s.z) :
    piece s x ⊆ (M.branch i).erase s.z := by
  rcases mem_U_or_Xz s hx with h | h
  · rw [piece_U s h]
    intro y hy
    exact Finset.mem_erase.2 ⟨fun hyz => z_not_U s (hyz ▸ hy), (Finset.mem_sdiff.1 hy).1⟩
  · rw [piece_comp s h]
    intro y hy
    have := comp_sub s x hy
    exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 this).1,
      X_sub s (Finset.mem_of_mem_erase this)⟩

theorem piece_conn {x : V} (hx : x ∈ (M.branch i).erase s.z) : ConnSet G ↑(piece s x) := by
  rcases mem_U_or_Xz s hx with h | h
  · rw [piece_U s h]; exact U_conn s ⟨x, h⟩
  · rw [piece_comp s h]; exact comp_conn s h

theorem piece_eq {x y : V} (hx : x ∈ (M.branch i).erase s.z) (hy : y ∈ piece s x) :
    piece s y = piece s x := by
  rcases mem_U_or_Xz s hx with h | h
  · rw [piece_U s h] at hy ⊢; exact piece_U s hy
  · rw [piece_comp s h] at hy ⊢
    rw [piece_comp s (comp_sub s x hy)]
    exact comp_eq s hy

theorem piece_touch_z {x : V} (hx : x ∈ (M.branch i).erase s.z) :
    Touch G (piece s x) {s.z} := by
  rcases mem_U_or_Xz s hx with h | h
  · rw [piece_U s h]
    obtain ⟨u, hu, hzu⟩ := s.z_adj ⟨x, h⟩
    exact ⟨u, hu, s.z, Finset.mem_singleton_self _, hzu.symm⟩
  · rw [piece_comp s h]
    obtain ⟨w, hw, hwz⟩ := comp_touch_z s h
    exact ⟨w, hw, s.z, Finset.mem_singleton_self _, hwz⟩

theorem piece_disj {x y : V} (hx : x ∈ (M.branch i).erase s.z)
    (hy : y ∈ (M.branch i).erase s.z) (hne : piece s x ≠ piece s y) :
    Disjoint (piece s x) (piece s y) := by
  rw [Finset.disjoint_left]
  intro w hwx hwy
  exact hne ((piece_eq s hx hwx).symm.trans (piece_eq s hy hwy))

theorem rest_conn_comp (x : V) : ConnSet G ↑(M.branch i \ comp s x) := by
  have hzB : s.z ∈ M.branch i \ comp s x := by
    refine Finset.mem_sdiff.2 ⟨X_sub s s.z_mem, fun h => ?_⟩
    have := comp_sub s x h
    simp [Xz] at this
  set R := M.branch i \ comp s x with hR
  have key : ∀ y ∈ R, RIn G ↑R y s.z := by
    intro y hy
    obtain ⟨hyB, hyc⟩ := Finset.mem_sdiff.1 hy
    by_cases hyz : y = s.z
    · subst hyz; exact RIn.refl _
    rcases mem_U_or_Xz s (Finset.mem_erase.2 ⟨hyz, hyB⟩) with hyU | hyX
    · have hUsub : U s ⊆ R := by
        intro u hu
        refine Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hu).1, fun h => ?_⟩
        exact Xz_not_U s (comp_sub s x h) hu
      obtain ⟨u, hu, hzu⟩ := s.z_adj ⟨y, hyU⟩
      exact (((U_conn s ⟨y, hyU⟩).2 y hyU u hu).mono_set (by exact_mod_cast hUsub)).tail
        hzu.symm (by exact_mod_cast hUsub hu) (by exact_mod_cast hzB)
    · have hdisj := comp_disj s hyc
      have hcsub : comp s y ⊆ R := by
        intro w hw
        refine Finset.mem_sdiff.2 ⟨X_sub s (Finset.mem_of_mem_erase (comp_sub s y hw)),
          fun h => Finset.disjoint_left.1 hdisj h hw⟩
      obtain ⟨w, hw, hwz⟩ := comp_touch_z s hyX
      exact (((comp_conn s hyX).2 y (mem_comp_self s hyX) w hw).mono_set
        (by exact_mod_cast hcsub)).tail hwz (by exact_mod_cast hcsub hw)
        (by exact_mod_cast hzB)
  refine ⟨⟨s.z, by exact_mod_cast hzB⟩, fun a ha b hb => ?_⟩
  exact (key a (by exact_mod_cast ha)).trans (key b (by exact_mod_cast hb)).symm

theorem piece_rest_conn {x : V} (hx : x ∈ (M.branch i).erase s.z) :
    ConnSet G ↑(M.branch i \ piece s x) := by
  rcases mem_U_or_Xz s hx with h | h
  · rw [piece_U s h]
    unfold U
    rw [Finset.sdiff_sdiff_eq_self (X_sub s)]
    exact X_conn s
  · rw [piece_comp s h]; exact rest_conn_comp s x

/-- Each piece touches at most one other branch set. -/
theorem piece_not_twoC (hK : ¬ IsMinor K33 G) {x : V} (hx : x ∈ (M.branch i).erase s.z) :
    ¬ TwoC M i (piece s x) := by
  intro h2
  rcases mem_U_or_Xz s hx with h | h
  · rw [piece_U s h] at h2
    obtain ⟨u, hu, hzu⟩ := s.z_adj ⟨x, h⟩
    refine hK (isMinor_K33_of_split M i s.X (U s) (X_sub s) Finset.sdiff_subset
      (Finset.disjoint_sdiff) (X_conn s) (U_conn s ⟨x, h⟩) ⟨s.z, s.z_mem, u, hu, hzu⟩
      (fun j hji => ?_) s.heavy.2.2.2 h2)
    obtain ⟨a, ha, b, hb, hab⟩ := M.branch_adjacent i j hji.symm
    by_cases haX : a ∈ s.X
    · exact Or.inl ⟨a, haX, b, hb, hab⟩
    · exact Or.inr ⟨a, Finset.mem_sdiff.2 ⟨ha, haX⟩, b, hb, hab⟩
  · rw [piece_comp s h] at h2
    have hheavy : Heavy M i (comp s x) :=
      ⟨fun y hy => X_sub s (Finset.mem_of_mem_erase (comp_sub s x hy)), comp_conn s h,
        Or.inr (rest_conn_comp s x), h2⟩
    have h1 := s.min _ hheavy
    have h2' : (comp s x).card < s.X.card :=
      lt_of_le_of_lt (Finset.card_le_card (comp_sub s x))
        (Finset.card_erase_lt_of_mem s.z_mem)
    omega

theorem piece_contact (hM : IsMinimalK5 M) {x : V} (hx : x ∈ (M.branch i).erase s.z) :
    ∃ j, j ≠ i ∧ Touch G (piece s x) (M.branch j) := by
  by_contra hcon
  push Not at hcon
  refine hM.no_replace i (M.branch i \ piece s x) (piece_rest_conn s hx) Finset.sdiff_subset
    (fun h => ?_) (fun j hji => ?_)
  · have hxB := Finset.mem_of_mem_erase hx
    rw [← h] at hxB
    exact (Finset.mem_sdiff.1 hxB).2 (mem_piece_self s hx)
  · obtain ⟨a, ha, b, hb, hab⟩ := M.branch_adjacent i j hji.symm
    refine ⟨a, Finset.mem_sdiff.2 ⟨ha, fun hap => ?_⟩, b, hb, hab⟩
    exact hcon j hji ⟨a, hap, b, hb, hab⟩

theorem piece_unique (hM : IsMinimalK5 M) (hK : ¬ IsMinor K33 G) {x y : V}
    (hx : x ∈ (M.branch i).erase s.z) (hy : y ∈ (M.branch i).erase s.z) {j : Fin 5}
    (hji : j ≠ i) (htx : Touch G (piece s x) (M.branch j))
    (hty : Touch G (piece s y) (M.branch j)) : piece s x = piece s y := by
  by_contra hne
  have hdisj := piece_disj s hx hy hne
  refine hM.no_replace i (M.branch i \ piece s x) (piece_rest_conn s hx) Finset.sdiff_subset
    (fun h => ?_) (fun k hki => ?_)
  · have hxB := Finset.mem_of_mem_erase hx
    rw [← h] at hxB
    exact (Finset.mem_sdiff.1 hxB).2 (mem_piece_self s hx)
  · by_cases hkj : k = j
    · subst hkj
      obtain ⟨a, ha, b, hb, hab⟩ := hty
      refine ⟨a, Finset.mem_sdiff.2 ⟨Finset.mem_of_mem_erase (piece_sub s hy ha), fun hax =>
        Finset.disjoint_left.1 hdisj hax ha⟩, b, hb, hab⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := M.branch_adjacent i k hki.symm
      refine ⟨a, Finset.mem_sdiff.2 ⟨ha, fun hap => ?_⟩, b, hb, hab⟩
      exact piece_not_twoC s hK hx ⟨j, k, Ne.symm hkj, hji, hki, htx, ⟨a, hap, b, hb, hab⟩⟩

open Classical in
/-- The rays. -/
noncomputable def ray (j : Fin 5) : Finset V :=
  ((M.branch i).erase s.z).filter fun x => j ≠ i ∧ Touch G (piece s x) (M.branch j)

theorem mem_ray {j : Fin 5} {x : V} :
    x ∈ ray s j ↔ x ∈ (M.branch i).erase s.z ∧ j ≠ i ∧ Touch G (piece s x) (M.branch j) := by
  unfold ray; simp

theorem ray_eq_piece (hM : IsMinimalK5 M) (hK : ¬ IsMinor K33 G) {j : Fin 5} {x₀ : V}
    (hx₀ : x₀ ∈ ray s j) : ray s j = piece s x₀ := by
  obtain ⟨hx₀B, hji, ht₀⟩ := (mem_ray s).1 hx₀
  ext y
  constructor
  · intro hy
    obtain ⟨hyB, -, hty⟩ := (mem_ray s).1 hy
    rw [← piece_unique s hM hK hyB hx₀B hji hty ht₀]
    exact mem_piece_self s hyB
  · intro hy
    have hyB := piece_sub s hx₀B hy
    refine (mem_ray s).2 ⟨hyB, hji, ?_⟩
    rw [piece_eq s hx₀B hy]; exact ht₀

/-- The star built from the setup. -/
noncomputable def toStar (hM : IsMinimalK5 M) (hK : ¬ IsMinor K33 G) : BranchStar M i where
  z := s.z
  R := ray s
  z_mem := X_sub s s.z_mem
  R_sub j := fun x hx => ((mem_ray s).1 hx).1
  R_self := by
    ext x; simp [mem_ray]
  R_disj j k hjk := by
    rw [Finset.disjoint_left]
    intro x hxj hxk
    obtain ⟨hxB, hji, htj⟩ := (mem_ray s).1 hxj
    obtain ⟨-, hki, htk⟩ := (mem_ray s).1 hxk
    exact piece_not_twoC s hK hxB ⟨j, k, hjk, hji, hki, htj, htk⟩
  cover x hx hxz := by
    have hxB : x ∈ (M.branch i).erase s.z := Finset.mem_erase.2 ⟨hxz, hx⟩
    obtain ⟨j, hji, ht⟩ := piece_contact s hM hxB
    exact ⟨j, (mem_ray s).2 ⟨hxB, hji, ht⟩⟩
  touch_z j hji hR := by
    obtain ⟨a, ha, b, hb, hab⟩ := M.branch_adjacent i j hji.symm
    by_cases haz : a = s.z
    · exact ⟨s.z, Finset.mem_singleton_self _, b, hb, haz ▸ hab⟩
    · exfalso
      have haB : a ∈ (M.branch i).erase s.z := Finset.mem_erase.2 ⟨haz, ha⟩
      have : a ∈ ray s j := (mem_ray s).2 ⟨haB, hji, ⟨a, mem_piece_self s haB, b, hb, hab⟩⟩
      rw [hR] at this
      simp at this
  conn j hne := by
    obtain ⟨x₀, hx₀⟩ := hne
    rw [ray_eq_piece s hM hK hx₀]
    exact piece_conn s ((mem_ray s).1 hx₀).1
  touch_center j hne := by
    obtain ⟨x₀, hx₀⟩ := hne
    rw [ray_eq_piece s hM hK hx₀]
    exact piece_touch_z s ((mem_ray s).1 hx₀).1
  touch_target j hne := by
    obtain ⟨x₀, hx₀⟩ := hne
    rw [ray_eq_piece s hM hK hx₀]
    exact ((mem_ray s).1 hx₀).2.2
  no_other j k hki hkj := by
    rintro ⟨x, hx, b, hb, hxb⟩
    obtain ⟨hxB, hji, htj⟩ := (mem_ray s).1 hx
    exact piece_not_twoC s hK hxB ⟨j, k, Ne.symm hkj, hji, hki, htj,
      ⟨x, mem_piece_self s hxB, b, hb, hxb⟩⟩

end StarConstruction

/-- **Star lemma.**  In a graph without a `K_{3,3}` minor, every branch set of a `K_5`
model of minimum size admits a star decomposition. -/
theorem exists_branchStar {M : CliqueMinorModel G 5} (hM : IsMinimalK5 M)
    (hK : ¬ IsMinor K33 G) (i : Fin 5) : Nonempty (BranchStar M i) :=
  ⟨StarConstruction.toStar (StarConstruction.exists_setup M i).some hM hK⟩

end LeanPool.K5MinorFreeChoosability
