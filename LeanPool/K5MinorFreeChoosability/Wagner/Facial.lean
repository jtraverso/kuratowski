/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.HypermapKit
public import LeanPool.K5MinorFreeChoosability.Wagner.Separation
public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar

/-!
# Facial structure of plane maps without small separations

Combinatorial Jordan-curve facts for genus-zero rotation systems, obtained purely by counting:
splitting a vertex at two corners of one face raises the number of components (Euler's
inequality `eulerDefect_nonneg`), and a disconnected split yields a vertex separation.

* `false_of_split`: a rotation-like permutation whose components split the darts nontrivially,
  away from a set `Z` of at most two vertices, contradicts `NoSmallSep`.
* `PlaneMap.eq_of_sameCycle_face_of_fst`: in a plane map of a graph without separations of
  order at most two, a face visits every vertex at most once.
* `PlaneMap.two_faces_share`: two different faces through a vertex `z` meeting again at a vertex
  `u` must be the two faces on either side of the edge `zu`.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {D : Type*}

/-- If `π'` agrees with `π` on a block `f ⁻¹' {c}` preserved by `π`, then cycles of `π` inside
that block are cycles of `π'`. -/
theorem sameCycle_of_agree {β : Type*} {π π' : Perm D} (f : D → β) (hf : ∀ z, f (π z) = f z)
    {c : β} (hag : ∀ z, f z = c → π' z = π z) {d e : D} (hd : f d = c) (hde : SameCycle π d e) :
    SameCycle π' d e := by
  let s : Setoid D :=
    { r := fun a b => (f a = c ∧ f b = c ∧ SameCycle π' a b) ∨ (f a ≠ c ∧ f b ≠ c)
      iseqv := by
        refine ⟨fun a => ?_, fun {a b} h => ?_, fun {a b c'} h k => ?_⟩
        · by_cases h : f a = c
          · exact Or.inl ⟨h, h, SameCycle.refl _ _⟩
          · exact Or.inr ⟨h, h⟩
        · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h2, h1, h3.symm⟩
          · exact Or.inr ⟨h2, h1⟩
        · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;> rcases k with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
          · exact Or.inl ⟨h1, k2, h3.trans k3⟩
          · exact absurd h2 k1
          · exact absurd k1 h2
          · exact Or.inr ⟨h1, k2⟩ }
  have key : s d e := by
    refine sameCycle_of_step s (fun z => ?_) hde
    by_cases hz : f z = c
    · refine Or.inl ⟨hz, (hf z).trans hz, ?_⟩
      rw [← hag z hz]
      exact ⟨1, by simp⟩
    · exact Or.inr ⟨hz, fun h => hz ((hf z).symm.trans h)⟩
  rcases key with ⟨-, -, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd hd h

theorem exists_not_rel_of_one_lt [Finite D] (s : Setoid D) (h : 1 < numClasses s) :
    ∃ a b, ¬ s a b := by
  by_contra hn
  push Not at hn
  have hsub : Subsingleton (Quotient s) :=
    ⟨fun p q => Quotient.inductionOn₂ p q fun a b => Quotient.sound (hn a b)⟩
  have := Finite.card_le_one_iff_subsingleton.2 hsub
  unfold numClasses at h
  omega

variable {V : Type*} {G : SimpleGraph V}

@[simp] theorem dartSymm_inv_apply (d : G.Dart) : (dartSymm G)⁻¹ d = d.symm := by
  rw [Perm.inv_eq_iff_eq]
  simp

/-- A face step: `facePerm (rot⁻¹ g).symm = g`. -/
theorem PlaneMap.facePerm_symm_rot_inv (M : PlaneMap G) (g : G.Dart) :
    M.facePerm (M.rot⁻¹ g).symm = g := by
  rw [PlaneMap.facePerm_apply]
  simp

theorem PlaneMap.fst_rot_inv (M : PlaneMap G) (g : G.Dart) : (M.rot⁻¹ g).fst = g.fst := by
  have := M.isRotationSystem.fst_apply (M.rot⁻¹ g)
  rw [show M.rot (M.rot⁻¹ g) = g by simp] at this
  exact this.symm

variable [DecidableEq V]

theorem fst_swap_of_fst_eq {a b w : G.Dart} (h : a.fst = b.fst) : (swap a b w).fst = w.fst := by
  by_cases ha : w = a
  · subst ha; simp [h]
  by_cases hb : w = b
  · subst hb; simp [h]
  rw [swap_apply_of_ne_of_ne ha hb]

open Classical in
/-- A permutation of the darts which, away from a set `Z` of at most two vertices, has all darts
at a vertex in one cycle, and whose components (with the edge involution) are not all equal,
with every component reaching outside `Z`, yields a separation of order at most two. -/
theorem false_of_split {S Z : Finset V} (σ' : Perm G.Dart) (hS : ∀ u v, G.Adj u v → u ∈ S)
    (hsep : NoSmallSep G S) (hZ : Z.card ≤ 2)
    (hcyc : ∀ d e : G.Dart, d.fst = e.fst → d.fst ∉ Z → SameCycle σ' d e)
    {d1 d2 : G.Dart} (hnot : ¬ compSetoid σ' (dartSymm G) d1 d2)
    (hgood : ∀ d, ∃ e, compSetoid σ' (dartSymm G) d e ∧ e.fst ∉ Z) : False := by
  let R := compSetoid σ' (dartSymm G)
  let A := S.filter fun v => ∃ d : G.Dart, R d1 d ∧ d.fst = v
  let B := S.filter fun v => v ∈ Z ∨ ¬ ∃ d : G.Dart, R d1 d ∧ d.fst = v
  have hcov : A ∪ B = S := by
    ext v
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    tauto
  have hinter : A ∩ B ⊆ Z := by
    intro v hv
    obtain ⟨hA, hB⟩ := Finset.mem_inter.1 hv
    rcases (Finset.mem_filter.1 hB).2 with h | h
    · exact h
    · exact absurd (Finset.mem_filter.1 hA).2 h
  have hcard : (A ∩ B).card ≤ 2 := (Finset.card_le_card hinter).trans hZ
  have link : ∀ d d' : G.Dart, d.fst = d'.fst → d.fst ∉ Z → R d d' := fun d d' h hz =>
    compSetoid_of_sameCycle_left (hcyc d d' h hz)
  have hcross : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ G.Adj u v := by
    intro u hu huB v hv hvA huv
    obtain ⟨d, hd, hdu⟩ := (Finset.mem_filter.1 hu).2
    have huZ : u ∉ Z := fun h => huB (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hu).1, Or.inl h⟩)
    let x : G.Dart := ⟨(u, v), huv⟩
    have hdx : R d x := link d x hdu (hdu ▸ huZ)
    have hxs : R x x.symm := compSetoid_right _ _ x
    exact hvA (Finset.mem_filter.2 ⟨hS v u huv.symm, x.symm,
      R.trans hd (R.trans hdx hxs), rfl⟩)
  rcases hsep A B hcov hcard hcross with hAB | hBA
  · obtain ⟨e, he, heZ⟩ := hgood d1
    have hA : e.fst ∈ A := Finset.mem_filter.2 ⟨hS _ _ e.adj, e, he, rfl⟩
    rcases (Finset.mem_filter.1 (hAB hA)).2 with h | h
    · exact heZ h
    · exact h ⟨e, he, rfl⟩
  · obtain ⟨e, he, heZ⟩ := hgood d2
    have hB : e.fst ∈ B := Finset.mem_filter.2 ⟨hS _ _ e.adj, Or.inr fun ⟨d', hd', hfd⟩ =>
      hnot (R.trans hd' (R.trans (link d' e hfd (hfd ▸ heZ)) (R.symm he)))⟩
    obtain ⟨d', hd', hfd⟩ := (Finset.mem_filter.1 (hBA hB)).2
    exact hnot (R.trans hd' (R.trans (link d' e hfd (hfd ▸ heZ)) (R.symm he)))

variable [Finite V]

/-- **Faces are simple**: in a plane map of a connected graph without separations of order at
most two, a face visits every vertex at most once. -/
theorem PlaneMap.eq_of_sameCycle_face_of_fst (M : PlaneMap G) {S : Finset V}
    (hS : ∀ u v, G.Adj u v → u ∈ S) (hsep : NoSmallSep G S)
    (hK : numComponents M.rot (dartSymm G) ≤ 1) {g g' : G.Dart}
    (hsame : SameCycle M.facePerm g g') (hfst : g.fst = g'.fst) : g = g' := by
  classical
  have := Fintype.ofFinite V
  by_contra hne
  set p := M.rot⁻¹ g with hp
  set q := M.rot⁻¹ g' with hq
  have hpq : p ≠ q := fun h => hne (by simpa [p, q] using congrArg M.rot h)
  have hpf : p.fst = g.fst := M.fst_rot_inv g
  have hqf : q.fst = g.fst := (M.fst_rot_inv g').trans hfst.symm
  have hs : SameCycle M.rot p q := M.isRotationSystem.sameCycle p q (hpf.trans hqf.symm)
  have hf : SameCycle (M.rot * dartSymm G) ((dartSymm G)⁻¹ p) ((dartSymm G)⁻¹ q) := by
    rw [dartSymm_inv_apply, dartSymm_inv_apply]
    have h1 : SameCycle M.facePerm p.symm g :=
      ⟨1, by rw [zpow_one]; exact M.facePerm_symm_rot_inv g⟩
    have h2 : SameCycle M.facePerm q.symm g' :=
      ⟨1, by rw [zpow_one]; exact M.facePerm_symm_rot_inv g'⟩
    exact h1.trans (hsame.trans h2.symm)
  have heq := eulerDefect_mulSwap_split_face_eq hpq hs hf
  have h0 := M.eulerDefect_eq_zero
  have hnn := eulerDefect_nonneg (M.rot * swap p q) (dartSymm G)
  have : Nonempty G.Dart := ⟨g⟩
  have hK1 := one_le_numComponents M.rot (dartSymm G)
  have hK' : 1 < numComponents (M.rot * swap p q) (dartSymm G) := by
    have : (1 : ℤ) < numComponents (M.rot * swap p q) (dartSymm G) := by
      have : (numComponents M.rot (dartSymm G) : ℤ) ≤ 1 := by exact_mod_cast hK
      linarith
    exact_mod_cast this
  obtain ⟨d1, d2, hn⟩ := exists_not_rel_of_one_lt _ hK'
  refine false_of_split (Z := {g.fst}) (M.rot * swap p q) hS hsep (by simp) ?_ hn ?_
  · intro d e hde hdZ
    have hdZ' : d.fst ≠ g.fst := by simpa using hdZ
    refine sameCycle_of_agree (fun d : G.Dart => d.fst) M.isRotationSystem.fst_apply
      (c := d.fst) (fun z hz => ?_) rfl (M.isRotationSystem.sameCycle d e hde)
    have hzp : z ≠ p := fun h => hdZ' (by rw [← hz, h, hpf])
    have hzq : z ≠ q := fun h => hdZ' (by rw [← hz, h, hqf])
    simp [swap_apply_of_ne_of_ne hzp hzq]
  · intro d
    by_cases hd : d.fst = g.fst
    · refine ⟨d.symm, compSetoid_right _ _ d, ?_⟩
      simp only [SimpleGraph.Dart.symm_toProd, Prod.fst_swap, Finset.mem_singleton]
      intro h
      exact d.adj.ne (hd.trans h.symm)
    · exact ⟨d, (compSetoid _ _).refl d, by simpa using hd⟩

/-- **Two faces through a vertex.**  In a plane map of a connected graph without separations of
order at most two, if two different faces through `z` (entered at the darts `g₁`, `g₂` leaving
`z`) meet again at a vertex `u ≠ z` (at darts `g₁'`, `g₂'` leaving `u`), then they are the two
faces on either side of the edge `zu`, and `g₁`, `g₂` are consecutive around `z`. -/
theorem PlaneMap.two_faces_share (M : PlaneMap G) {S : Finset V}
    (hS : ∀ u v, G.Adj u v → u ∈ S) (hsep : NoSmallSep G S)
    (hK : numComponents M.rot (dartSymm G) ≤ 1) {g₁ g₂ g₁' g₂' : G.Dart}
    (hz : g₁.fst = g₂.fst) (hu : g₁'.fst = g₂'.fst) (hzu : g₁.fst ≠ g₁'.fst)
    (h₁ : SameCycle M.facePerm g₁ g₁') (h₂ : SameCycle M.facePerm g₂ g₂')
    (hdiff : ¬ SameCycle M.facePerm g₁ g₂) :
    (g₁.snd = g₁'.fst ∧ M.rot g₁ = g₂) ∨ (g₂.snd = g₁'.fst ∧ M.rot g₂ = g₁) := by
  classical
  have := Fintype.ofFinite V
  by_contra hn
  push Not at hn
  obtain ⟨hn1, hn2⟩ := hn
  set z := g₁.fst with hzdef
  set u := g₁'.fst with hudef
  have hrs := M.isRotationSystem
  set p₁ := M.rot⁻¹ g₁ with hp₁
  set q₁ := M.rot⁻¹ g₂ with hq₁
  set p₂ := M.rot⁻¹ g₁' with hp₂
  set q₂ := M.rot⁻¹ g₂' with hq₂
  have hp₁f : p₁.fst = z := M.fst_rot_inv g₁
  have hq₁f : q₁.fst = z := (M.fst_rot_inv g₂).trans hz.symm
  have hp₂f : p₂.fst = u := M.fst_rot_inv g₁'
  have hq₂f : q₂.fst = u := (M.fst_rot_inv g₂').trans hu.symm
  have hg12 : g₁ ≠ g₂ := fun h => hdiff (h ▸ SameCycle.refl _ _)
  have hg12' : g₁' ≠ g₂' := fun h => hdiff (h₁.trans ((h ▸ h₂).symm))
  have hpq₁ : p₁ ≠ q₁ := fun h => hg12 (by simpa [p₁, q₁] using congrArg M.rot h)
  have hpq₂ : p₂ ≠ q₂ := fun h => hg12' (by simpa [p₂, q₂] using congrArg M.rot h)
  have fp₁ : SameCycle M.facePerm p₁.symm g₁ :=
    ⟨1, by rw [zpow_one]; exact M.facePerm_symm_rot_inv g₁⟩
  have fq₁ : SameCycle M.facePerm q₁.symm g₂ :=
    ⟨1, by rw [zpow_one]; exact M.facePerm_symm_rot_inv g₂⟩
  have fp₂ : SameCycle M.facePerm p₂.symm g₁' :=
    ⟨1, by rw [zpow_one]; exact M.facePerm_symm_rot_inv g₁'⟩
  have fq₂ : SameCycle M.facePerm q₂.symm g₂' :=
    ⟨1, by rw [zpow_one]; exact M.facePerm_symm_rot_inv g₂'⟩
  -- first split, at `z`, between two different faces
  have hs₁ : SameCycle M.rot p₁ q₁ := hrs.sameCycle p₁ q₁ (hp₁f.trans hq₁f.symm)
  have hnf₁ : ¬ SameCycle (M.rot * dartSymm G) ((dartSymm G)⁻¹ p₁) ((dartSymm G)⁻¹ q₁) := by
    rw [dartSymm_inv_apply, dartSymm_inv_apply]
    intro h
    exact hdiff (fp₁.symm.trans (h.trans fq₁))
  have e₁ := eulerDefect_mulSwap_split_noface_eq hpq₁ hs₁ hnf₁
  set σ₁ := M.rot * swap p₁ q₁ with hσ₁
  -- second split, at `u`, now inside one merged face
  have hag₁ : ∀ w : G.Dart, w.fst = u → σ₁ w = M.rot w := by
    intro w hw
    have h1 : w ≠ p₁ := fun h => hzu (by rw [← hp₁f, ← h, hw])
    have h2 : w ≠ q₁ := fun h => hzu (by rw [← hq₁f, ← h, hw])
    simp [σ₁, swap_apply_of_ne_of_ne h1 h2]
  have hs₂ : SameCycle σ₁ p₂ q₂ :=
    sameCycle_of_agree (fun d : G.Dart => d.fst) hrs.fst_apply hag₁ hp₂f
      (hrs.sameCycle p₂ q₂ (hp₂f.trans hq₂f.symm))
  have hf₂ : SameCycle (σ₁ * dartSymm G) ((dartSymm G)⁻¹ p₂) ((dartSymm G)⁻¹ q₂) := by
    rw [hσ₁, mulSwap_mul_eq, dartSymm_inv_apply, dartSymm_inv_apply, dartSymm_inv_apply,
      dartSymm_inv_apply]
    have hn' : ¬ SameCycle (M.rot * dartSymm G) p₁.symm q₁.symm := by
      simpa using hnf₁
    have a1 : SameCycle (M.rot * dartSymm G * swap p₁.symm q₁.symm) p₁.symm p₂.symm :=
      sameCycle_mulSwap_of_not_left hn' (fp₁.trans (h₁.trans fp₂.symm))
    have a2 : SameCycle (M.rot * dartSymm G * swap p₁.symm q₁.symm) p₁.symm q₂.symm :=
      sameCycle_mulSwap_of_not_right hn' (fq₁.trans (h₂.trans fq₂.symm))
    exact a1.symm.trans a2
  have e₂ := eulerDefect_mulSwap_split_face_eq hpq₂ hs₂ hf₂
  set σ₂ := σ₁ * swap p₂ q₂ with hσ₂
  have h0 := M.eulerDefect_eq_zero
  have hnn := eulerDefect_nonneg σ₂ (dartSymm G)
  have : Nonempty G.Dart := ⟨g₁⟩
  have hK1 := one_le_numComponents M.rot (dartSymm G)
  have hK' : 1 < numComponents σ₂ (dartSymm G) := by
    have : (1 : ℤ) < numComponents σ₂ (dartSymm G) := by
      have : (numComponents M.rot (dartSymm G) : ℤ) ≤ 1 := by exact_mod_cast hK
      linarith
    exact_mod_cast this
  obtain ⟨d1, d2, hnd⟩ := exists_not_rel_of_one_lt _ hK'
  -- `σ₂` agrees with the rotation away from `z` and `u`
  have hag₂ : ∀ w : G.Dart, w.fst ≠ z → w.fst ≠ u → σ₂ w = M.rot w := by
    intro w hwz hwu
    have h1 : w ≠ p₂ := fun h => hwu (h ▸ hp₂f)
    have h2 : w ≠ q₂ := fun h => hwu (h ▸ hq₂f)
    have h3 : w ≠ p₁ := fun h => hwz (h ▸ hp₁f)
    have h4 : w ≠ q₁ := fun h => hwz (h ▸ hq₁f)
    simp [σ₂, σ₁, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h3 h4]
  have hσ₂z : ∀ w : G.Dart, w.fst = z → σ₂ w = σ₁ w := by
    intro w hw
    have h1 : w ≠ p₂ := fun h => hzu (by rw [← hw, h, hp₂f])
    have h2 : w ≠ q₂ := fun h => hzu (by rw [← hw, h, hq₂f])
    simp [σ₂, swap_apply_of_ne_of_ne h1 h2]
  have hσ₂f : ∀ w : G.Dart, (σ₂ w).fst = w.fst := by
    intro w
    simp only [σ₂, σ₁, Perm.mul_apply]
    rw [hrs.fst_apply, fst_swap_of_fst_eq (hp₁f.trans hq₁f.symm),
      fst_swap_of_fst_eq (hp₂f.trans hq₂f.symm)]
  refine false_of_split (Z := {z, u}) σ₂ hS hsep (Finset.card_le_two) ?_ hnd ?_
  · intro d e hde hdZ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hdZ
    refine sameCycle_of_agree (fun d : G.Dart => d.fst) hrs.fst_apply (c := d.fst)
      (fun w hw => hag₂ w (hw ▸ hdZ.1) (hw ▸ hdZ.2)) rfl (hrs.sameCycle d e hde)
  · intro d
    by_cases hd : d.fst ∈ ({z, u} : Finset V)
    · by_cases hd' : d.snd ∈ ({z, u} : Finset V)
      · -- `d` is a dart of the edge `zu`; let `w` be its version leaving `z`
        obtain ⟨w, hwd, hwz, hwu⟩ : ∃ w : G.Dart, compSetoid σ₂ (dartSymm G) d w ∧
            w.fst = z ∧ w.snd = u := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd hd'
          rcases hd with h | h <;> rcases hd' with h' | h'
          · exact absurd (h.trans h'.symm) d.adj.ne
          · exact ⟨d, (compSetoid _ _).refl d, h, h'⟩
          · exact ⟨d.symm, compSetoid_right _ _ d, by simpa using h', by simpa using h⟩
          · exact absurd (h.trans h'.symm) d.adj.ne
        by_cases hfix : σ₂ w = w
        · exfalso
          rw [hσ₂z w hwz] at hfix
          simp only [σ₁, Perm.mul_apply] at hfix
          by_cases a : w = p₁
          · rw [a, swap_apply_left] at hfix
            -- `rot q₁ = p₁`, i.e. `g₂ = rot⁻¹ g₁`
            have hg : g₂ = p₁ := by simpa [q₁] using hfix
            refine hn2 ?_ ?_
            · rw [hg, ← a, hwu]
            · rw [hg]; simp [p₁]
          by_cases b : w = q₁
          · rw [b, swap_apply_right] at hfix
            have hg : g₁ = q₁ := by simpa [p₁] using hfix
            refine hn1 ?_ ?_
            · rw [hg, ← b, hwu]
            · rw [hg]; simp [q₁]
          rw [swap_apply_of_ne_of_ne a b] at hfix
          have e1 : g₁ = w := (hrs.sameCycle w g₁ (hwz.trans rfl)).eq_of_left hfix |>.symm
          have e2 : g₂ = w := (hrs.sameCycle w g₂ (hwz.trans hz)).eq_of_left hfix |>.symm
          exact hg12 (e1.trans e2.symm)
        · refine ⟨(σ₂ w).symm, ?_, ?_⟩
          · exact (compSetoid _ _).trans hwd ((compSetoid _ _).trans
              (compSetoid_left _ _ w) (compSetoid_right _ _ _))
          · have hf : (σ₂ w).fst = z := (hσ₂f w).trans hwz
            have hne : (σ₂ w).snd ≠ u := by
              intro h
              apply hfix
              exact (SimpleGraph.Dart.ext_iff _ _).2
                (Prod.ext (hf.trans hwz.symm) (h.trans hwu.symm))
            simp only [SimpleGraph.Dart.symm_toProd, Prod.fst_swap, Finset.mem_insert,
              Finset.mem_singleton, not_or]
            exact ⟨fun h => (σ₂ w).adj.ne (hf.trans h.symm), hne⟩
      · exact ⟨d.symm, compSetoid_right _ _ d, by simpa using hd'⟩
    · exact ⟨d, (compSetoid _ _).refl d, hd⟩

end LeanPool.K5MinorFreeChoosability
