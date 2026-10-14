/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.EdgeAdd
public import LeanPool.K5MinorFreeChoosability.Wagner.RotRing

/-!
# Splitting the contracted vertex

Let `xy` be an edge of `H` and let `G / xy = contractGraph H x y`.  `splitGraph H x y` is `H`
with the edges `y w` removed for the common neighbours `w` of `x` and `y`; its contraction along
`xy` is again `G / xy`, and every edge of `G / xy` lifts to a unique edge of `splitGraph`.

`exists_planeMap_split` is the *vertex splitting* step of Thomassen's proof of Kuratowski's
theorem: if around the contracted vertex of a plane map of `G / xy` the neighbours of `y` that
are not neighbours of `x` form one interval and all other neighbours are neighbours of `x`, then
`splitGraph H x y` has a plane map, with explicit rotation at `x` around the new edge `xy`.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {V : Type*}

/-- `H` without the edges `y w` to common neighbours `w` of `x` and `y`. -/
def splitGraph (H : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ ¬ (u = y ∧ H.Adj x v) ∧ ¬ (v = y ∧ H.Adj x u)
  symm := ⟨fun _ _ ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩⟩
  loopless := ⟨fun u h => H.loopless.irrefl u h.1⟩

variable {H : SimpleGraph V} {x y : V}

theorem splitGraph_adj {u v : V} : (splitGraph H x y).Adj u v ↔
    H.Adj u v ∧ ¬ (u = y ∧ H.Adj x v) ∧ ¬ (v = y ∧ H.Adj x u) := Iff.rfl

theorem splitGraph_le : splitGraph H x y ≤ H := fun _ _ h => h.1

open Classical in
/-- The lift of the vertex `a` of an edge `ab` of `G / xy`. -/
noncomputable def liftV (H : SimpleGraph V) (x y a b : V) : V :=
  if a = x ∧ ¬ H.Adj x b then y else a

theorem liftV_of_ne {a b : V} (ha : a ≠ x) : liftV H x y a b = a := by
  unfold liftV
  split_ifs with h
  · exact absurd h.1 ha
  · rfl

theorem liftV_x_of_adj {b : V} (hb : H.Adj x b) : liftV H x y x b = x := by
  unfold liftV
  split_ifs with h
  · exact absurd hb h.2
  · rfl

theorem liftV_x_of_not_adj {b : V} (hb : ¬ H.Adj x b) : liftV H x y x b = y := by
  unfold liftV
  split_ifs with h
  · rfl
  · exact absurd ⟨rfl, hb⟩ h

theorem splitGraph_adj_lift_x (hxy : H.Adj x y) {v : V} (h : (contractGraph H x y).Adj x v) :
    (splitGraph H x y).Adj (liftV H x y x v) (liftV H x y v x) := by
  obtain ⟨hvx, hvy, hc⟩ := (contractGraph_adj_x hxy.ne).1 h
  rw [liftV_of_ne hvx]
  by_cases hxv : H.Adj x v
  · rw [liftV_x_of_adj hxv]
    exact ⟨hxv, fun h => hxy.ne h.1, fun h => hvy h.1⟩
  · rw [liftV_x_of_not_adj hxv]
    exact ⟨hc.resolve_left hxv, fun h => hxv h.2, fun h => hvy h.1⟩

theorem splitGraph_adj_lift (hxy : H.Adj x y) {u v : V} (h : (contractGraph H x y).Adj u v) :
    (splitGraph H x y).Adj (liftV H x y u v) (liftV H x y v u) := by
  by_cases hux : u = x
  · subst hux
    exact splitGraph_adj_lift_x hxy h
  by_cases hvx : v = x
  · subst hvx
    exact (splitGraph_adj_lift_x hxy h.symm).symm
  obtain ⟨-, huy, hvy, hc⟩ := h
  rw [liftV_of_ne hux, liftV_of_ne hvx]
  have huv : H.Adj u v := by
    rcases hc with hc | ⟨e, -⟩ | ⟨e, -⟩
    · exact hc
    · exact absurd e hux
    · exact absurd e hvx
  exact ⟨huv, fun h => huy h.1, fun h => hvy h.1⟩

/-- The lift of a dart of `G / xy` to `splitGraph H x y`. -/
noncomputable def liftDart (hxy : H.Adj x y) (g : (contractGraph H x y).Dart) :
    (splitGraph H x y).Dart :=
  ⟨(liftV H x y g.fst g.snd, liftV H x y g.snd g.fst), splitGraph_adj_lift hxy g.adj⟩

theorem liftDart_toProd (hxy : H.Adj x y) (g : (contractGraph H x y).Dart) :
    (liftDart hxy g).toProd = (liftV H x y g.fst g.snd, liftV H x y g.snd g.fst) := rfl

theorem liftDart_symm (hxy : H.Adj x y) (g : (contractGraph H x y).Dart) :
    liftDart hxy g.symm = (liftDart hxy g).symm := rfl

theorem fst_ne_y_of_contract (g : (contractGraph H x y).Dart) : g.fst ≠ y := fun e =>
  contractGraph_not_adj_y _ (e ▸ g.adj)

theorem snd_ne_y_of_contract (g : (contractGraph H x y).Dart) : g.snd ≠ y := fun e =>
  contractGraph_not_adj_y _ (e ▸ g.adj.symm)

theorem eq_of_liftV_eq {a b a' b' : V} (ha : a ≠ y) (ha' : a' ≠ y)
    (h : liftV H x y a b = liftV H x y a' b') : a = a' := by
  classical
  have key : ∀ {c d : V}, c ≠ y → (if liftV H x y c d = y then x else liftV H x y c d) = c := by
    intro c d hc
    by_cases hcx : c = x
    · subst hcx
      by_cases hxd : H.Adj c d
      · rw [liftV_x_of_adj hxd]; simp [hc]
      · rw [liftV_x_of_not_adj hxd]; simp
    · rw [liftV_of_ne hcx]; simp [hc]
  rw [← key (d := b) ha, ← key (d := b') ha', h]

theorem liftDart_injective (hxy : H.Adj x y) : Function.Injective (liftDart hxy) := by
  intro g g' h
  have h' : (liftDart hxy g).toProd = (liftDart hxy g').toProd := by rw [h]
  rw [liftDart_toProd, liftDart_toProd, Prod.mk.injEq] at h'
  refine (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext ?_ ?_)
  · exact eq_of_liftV_eq (fst_ne_y_of_contract g) (fst_ne_y_of_contract g') h'.1
  · exact eq_of_liftV_eq (snd_ne_y_of_contract g) (snd_ne_y_of_contract g') h'.2

theorem liftV_mem_xy {a b : V} (ha : a ≠ y) (h : liftV H x y a b = x ∨ liftV H x y a b = y) :
    a = x := by
  by_contra hax
  rw [liftV_of_ne hax] at h
  exact h.elim hax ha

/-- The only darts of `splitGraph H x y` that are not lifts are the two darts of `xy`. -/
theorem liftDart_cover (hxy : H.Adj x y) (d : (splitGraph H x y).Dart) :
    d ∈ Set.range (liftDart hxy) ∨ d.toProd = (x, y) ∨ d.toProd = (y, x) := by
  obtain ⟨⟨p, q⟩, hpq, h2, h3⟩ := d
  have mk : ∀ g : (contractGraph H x y).Dart, liftV H x y g.fst g.snd = p →
      liftV H x y g.snd g.fst = q →
      (⟨(p, q), ⟨hpq, h2, h3⟩⟩ : (splitGraph H x y).Dart) ∈ Set.range (liftDart hxy) :=
    fun g e1 e2 => ⟨g, (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext e1 e2)⟩
  by_cases hpx : p = x
  · subst hpx
    by_cases hqy : q = y
    · exact Or.inr (Or.inl (Prod.ext rfl hqy))
    have hqx : q ≠ p := hpq.ne.symm
    left
    exact mk ⟨(p, q), (contractGraph_adj_x hxy.ne).2 ⟨hqx, hqy, Or.inl hpq⟩⟩
      (liftV_x_of_adj hpq) (liftV_of_ne hqx)
  by_cases hpy : p = y
  · subst hpy
    by_cases hqx : q = x
    · exact Or.inr (Or.inr (Prod.ext rfl hqx))
    have hxq : ¬ H.Adj x q := fun h => h2 ⟨rfl, h⟩
    have hqy : q ≠ p := hpq.ne.symm
    left
    exact mk ⟨(x, q), (contractGraph_adj_x hxy.ne).2 ⟨hqx, hqy, Or.inr hpq⟩⟩
      (liftV_x_of_not_adj hxq) (liftV_of_ne hqx)
  left
  by_cases hqx : q = x
  · subst hqx
    refine mk ⟨(p, q), ((contractGraph_adj_x hxy.ne).2 ⟨hpx, hpy, Or.inl hpq.symm⟩).symm⟩
      (liftV_of_ne hpx) (liftV_x_of_adj hpq.symm)
  by_cases hqy : q = y
  · subst hqy
    have hxp : ¬ H.Adj x p := fun h => h3 ⟨rfl, h⟩
    refine mk ⟨(p, x), ((contractGraph_adj_x hxy.ne).2 ⟨hpx, hpy, Or.inr hpq.symm⟩).symm⟩
      (liftV_of_ne hpx) (liftV_x_of_not_adj hxp)
  exact mk ⟨(p, q), (contractGraph_adj_of_ne hpx hqx hpy hqy).2 hpq⟩ (liftV_of_ne hpx)
    (liftV_of_ne hqx)

theorem liftDart_toProd_ne (hxy : H.Adj x y) (g : (contractGraph H x y).Dart) :
    (liftDart hxy g).toProd ≠ (x, y) ∧ (liftDart hxy g).toProd ≠ (y, x) := by
  have key : ¬ ((liftDart hxy g).fst = x ∨ (liftDart hxy g).fst = y) ∨
      ¬ ((liftDart hxy g).snd = x ∨ (liftDart hxy g).snd = y) := by
    by_contra h
    push Not at h
    have h1 := liftV_mem_xy (fst_ne_y_of_contract g) h.1
    have h2 := liftV_mem_xy (snd_ne_y_of_contract g) h.2
    exact g.adj.ne (h1.trans h2.symm)
  constructor
  · intro e
    have e1 : (liftDart hxy g).fst = x := congrArg Prod.fst e
    have e2 : (liftDart hxy g).snd = y := congrArg Prod.snd e
    rcases key with k | k
    · exact k (Or.inl e1)
    · exact k (Or.inr e2)
  · intro e
    have e1 : (liftDart hxy g).fst = y := congrArg Prod.fst e
    have e2 : (liftDart hxy g).snd = x := congrArg Prod.snd e
    rcases key with k | k
    · exact k (Or.inr e1)
    · exact k (Or.inl e2)

theorem natCard_subtype_lt [Finite V] {P Q : V → Prop} (hPQ : ∀ v, P v → Q v) {z : V}
    (hz : Q z) (hnz : ¬ P z) : Nat.card {v // P v} + 1 ≤ Nat.card {v // Q v} := by
  classical
  have := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).2 ⟨z, by simp [hz], by simp [hnz]⟩)
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact hPQ v hv

/-- A set missing all but at most two elements of a type, covered by two points. -/
theorem natCard_compl_le_two {D : Type*} [Finite D] (R : Set D) (a b : D)
    (h : ∀ e, e ∈ R ∨ e = a ∨ e = b) : Nat.card {e // e ∉ R} ≤ 2 := by
  classical
  have hinj : Function.Injective fun e : {e // e ∉ R} => decide (e.1 = a) := by
    intro e e' he
    rcases h e.1 with h1 | h1 | h1
    · exact absurd h1 e.2
    · rcases h e'.1 with h2 | h2 | h2
      · exact absurd h2 e'.2
      · exact Subtype.ext (h1.trans h2.symm)
      · by_cases hab : b = a
        · exact Subtype.ext (h1.trans (h2.trans hab).symm)
        · simp [h1, h2, hab] at he
    · rcases h e'.1 with h2 | h2 | h2
      · exact absurd h2 e'.2
      · by_cases hab : b = a
        · exact Subtype.ext ((h1.trans hab).trans h2.symm)
        · simp [h1, h2, hab] at he
      · exact Subtype.ext (h1.trans h2.symm)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

section Split

variable [Finite V] [DecidableEq V] (hxy : H.Adj x y) (M : PlaneMap (contractGraph H x y))
  (e0 : (contractGraph H x y).Dart) (he0 : e0.fst = x)
include hxy he0

omit [DecidableEq V] in
/-- **Vertex splitting.**  Around the contracted vertex `x` of a plane map of `G / xy`, starting
after position `s`, suppose the next `ℓ` neighbours are not neighbours of `x` in `H` (so they are
neighbours of `y`), and the remaining ones are neighbours of `x`.  Then `splitGraph H x y` has a
plane map in which, around `x`, the dart to `y` follows the dart to the `s`-th neighbour and
precedes the dart to the `(s + ℓ + 1)`-st neighbour. -/
theorem exists_planeMap_split {s ℓ : ℕ} (hℓ : ℓ + 1 < M.rper e0)
    (hA : ∀ t, 1 ≤ t → t ≤ ℓ → ¬ H.Adj x (M.rd e0 (s + t)).snd)
    (hB : ∀ t, ℓ + 1 ≤ t → t ≤ M.rper e0 → H.Adj x (M.rd e0 (s + t)).snd) :
    ∃ P : PlaneMap (splitGraph H x y),
      (∀ d : (splitGraph H x y).Dart, d.toProd = (x, (M.rd e0 s).snd) →
        (P.rot d).toProd = (x, y)) ∧
      (∀ d : (splitGraph H x y).Dart, d.toProd = (x, y) →
        (P.rot d).toProd = (x, (M.rd e0 (s + ℓ + 1)).snd)) := by
  classical
  classical
  have := Fintype.ofFinite V
  set k := M.rper e0 with hk
  set ι := liftDart hxy with hιdef
  have hι := liftDart_injective hxy
  have hxy' : (splitGraph H x y).Adj x y := ⟨hxy, fun h => hxy.ne h.1, fun h => H.irrefl h.2⟩
  set b : (splitGraph H x y).Dart := ⟨(x, y), hxy'⟩ with hbdef
  set a : (splitGraph H x y).Dart := b.symm with hadef
  have hab : a ≠ b := fun e => hxy.ne (by
    have h := congrArg (fun z : (splitGraph H x y).Dart => z.snd) e
    exact h)
  have hιa : ∀ g, ι g ≠ a := fun g hg => (liftDart_toProd_ne hxy g).2 (by
    change (ι g).toProd = (y, x); rw [hg]; rfl)
  have hιb : ∀ g, ι g ≠ b := fun g hg => (liftDart_toProd_ne hxy g).1 (by
    change (ι g).toProd = (x, y); rw [hg])
  have ha : a ∉ Set.range ι := fun ⟨g, hg⟩ => hιa g hg
  have hb : b ∉ Set.range ι := fun ⟨g, hg⟩ => hιb g hg
  have hcover : ∀ e, e ∈ Set.range ι ∨ e = a ∨ e = b := by
    intro e
    rcases liftDart_cover hxy e with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr ((SimpleGraph.Dart.ext_iff _ _).2 h))
    · exact Or.inr (Or.inl ((SimpleGraph.Dart.ext_iff _ _).2 h))
  -- the darts around `x`
  have hrdfst : ∀ j, (M.rd e0 j).fst = x := fun j => by rw [M.rd_fst, he0]
  have hwx : ∀ j, (M.rd e0 j).snd ≠ x := fun j h => by
    have := (M.rd e0 j).adj
    rw [hrdfst j, h] at this
    exact this.ne rfl
  have hιfst : ∀ j, (ι (M.rd e0 j)).fst = liftV H x y x (M.rd e0 j).snd := fun j => by
    change liftV H x y (M.rd e0 j).fst (M.rd e0 j).snd = _
    rw [hrdfst j]
  have hιsnd : ∀ j, (ι (M.rd e0 j)).snd = (M.rd e0 j).snd := fun j => by
    change liftV H x y (M.rd e0 j).snd (M.rd e0 j).fst = _
    exact liftV_of_ne (hwx j)
  have hfX : ∀ j, H.Adj x (M.rd e0 j).snd → (ι (M.rd e0 j)).fst = x := fun j h => by
    rw [hιfst, liftV_x_of_adj h]
  have hfY : ∀ j, ¬ H.Adj x (M.rd e0 j).snd → (ι (M.rd e0 j)).fst = y := fun j h => by
    rw [hιfst, liftV_x_of_not_adj h]
  have hfst_ne : ∀ g : (contractGraph H x y).Dart, g.fst ≠ x → (ι g).fst = g.fst :=
    fun g h => liftV_of_ne h
  have hwin : ∀ g : (contractGraph H x y).Dart, g.fst = x →
      ∃ t, 1 ≤ t ∧ t ≤ k ∧ g = M.rd e0 (s + t) := by
    intro g hg
    obtain ⟨i, -, hi⟩ := M.exists_rd_eq e0 (d := g) (by rw [he0]; exact hg)
    obtain ⟨t, ht, ht'⟩ := M.exists_window e0 (s + 1) i
    exact ⟨t + 1, by omega, by omega, by rw [← hi, ← ht', add_assoc, add_comm 1 t]⟩
  have hrds : M.rd e0 (s + k) = M.rd e0 s := M.rd_add_rper e0 s
  have hXs : H.Adj x (M.rd e0 s).snd := by rw [← hrds]; exact hB k (by omega) le_rfl
  have hXl : H.Adj x (M.rd e0 (s + ℓ + 1)).snd := by
    rw [add_assoc]; exact hB (ℓ + 1) le_rfl (by omega)
  -- the permutations
  set σ0 := extPerm ι hι M.rot with hσ0
  set α0 := extPerm ι hι (dartSymm _) with hα0
  have hσ0ι : ∀ g, σ0 (ι g) = ι (M.rot g) := extPerm_apply ι hι _
  have hα0ι : ∀ g, α0 (ι g) = ι g.symm := extPerm_apply ι hι _
  have hσ0a : σ0 a = a := extPerm_apply_of_not ι hι _ ha
  have hσ0b : σ0 b = b := extPerm_apply_of_not ι hι _ hb
  have hα0a : α0 a = a := extPerm_apply_of_not ι hι _ ha
  have hα0b : α0 b = b := extPerm_apply_of_not ι hι _ hb
  have hσ0rd : ∀ j, σ0 (ι (M.rd e0 j)) = ι (M.rd e0 (j + 1)) := fun j => by
    rw [hσ0ι, M.rd_succ]
  set h1 := ι (M.rd e0 (s + 1)) with hh1
  set h2 := ι (M.rd e0 (s + ℓ + 1)) with hh2
  set σ1 := insertBefore σ0 h1 b with hσ1
  set σ2 := insertBefore σ1 h2 a with hσ2
  have e1 : ∀ e, e ≠ b → σ1 e = if σ0 e = h1 then b else σ0 e := by
    intro e he
    split_ifs with h
    · exact insertBefore_apply_of_eq h hσ0b (hιb _)
    · exact insertBefore_apply_of_ne' h he
  have e1b : σ1 b = h1 := insertBefore_apply_new
  have e1a : σ1 a = a := by
    rw [e1 a hab, hσ0a, ite_eq_right (fun h => hιa _ h.symm)]
  have e2 : ∀ e, e ≠ a → σ2 e = if σ1 e = h2 then a else σ1 e := by
    intro e he
    split_ifs with h
    · exact insertBefore_apply_of_eq h e1a (hιa _)
    · exact insertBefore_apply_of_ne' h he
  have e2a : σ2 a = h2 := insertBefore_apply_new
  set σ3 := σ2 * swap a b with hσ3
  set α3 := α0 * swap a b with hα3
  have e3a : σ3 a = σ2 b := by rw [hσ3, Perm.mul_apply, swap_apply_left]
  have e3b : σ3 b = h2 := by rw [hσ3, Perm.mul_apply, swap_apply_right, e2a]
  have e3ι : ∀ g, σ3 (ι g) = σ2 (ι g) := fun g => by
    rw [hσ3, Perm.mul_apply, swap_apply_of_ne_of_ne (hιa g) (hιb g)]
  -- the dart `x → w_s` is followed by `b`
  have hs1 : σ1 (ι (M.rd e0 s)) = b := by
    rw [e1 _ (hιb _), ite_eq_left (hσ0rd s)]
  have hs3 : σ3 (ι (M.rd e0 s)) = b := by
    rw [e3ι, e2 _ (hιa _), ite_eq_right (by rw [hs1]; exact fun h => hιb _ h.symm), hs1]
  -- the cycle condition
  have hsc0 : ∀ i j, SameCycle σ0 (ι (M.rd e0 i)) (ι (M.rd e0 j)) := fun i j =>
    sameCycle_of_two_step ι (fun z => Or.inl (hσ0ι z))
      (M.isRotationSystem.sameCycle _ _ (by rw [hrdfst, hrdfst]))
  have hsc12 : SameCycle σ2 h1 h2 :=
    sameCycle_insertBefore e1a (sameCycle_insertBefore hσ0b (hsc0 _ _))
  have hscb : SameCycle σ2 b h1 :=
    sameCycle_insertBefore e1a (by rw [← e1b]; exact ⟨1, by simp⟩)
  have hsca : SameCycle σ2 a h2 := by rw [← e2a]; exact ⟨1, by simp⟩
  have hsc : SameCycle σ2 a b := hsca.trans (hsc12.symm.trans hscb.symm)
  -- the defect
  have hd0 : eulerDefect σ0 α0 = 0 := by
    rw [hσ0, hα0, eulerDefect_extPerm]
    exact M.eulerDefect_eq_zero
  have hd2 : eulerDefect σ2 α0 = 0 := by
    rw [hσ2, eulerDefect_insertBefore e1a hα0a (hιa _), hσ1,
      eulerDefect_insertBefore hσ0b hα0b (hιb _), hd0]
  have hd3 : eulerDefect σ3 α3 ≤ 0 := (eulerDefect_uncontract_le hab hα0a hα0b hsc).trans hd2.le
  -- the cycle count
  have hcc : cycleCount σ3 ≤ Nat.card {v // ∃ u, (splitGraph H x y).Adj v u} := by
    have c1 := cycleCount_insertBefore (σ := σ0) (h := h1) hσ0b (hιb _)
    have c2 := cycleCount_insertBefore (σ := σ1) (h := h2) e1a (hιa _)
    have c3 := cycleCount_mul_swap_of_sameCycle hab hsc
    have c0 := cycleCount_extPerm ι hι M.rot
    rw [cycleCount_eq_card_nonisolated M.isRotationSystem] at c0
    have c4 := natCard_compl_le_two (Set.range ι) a b hcover
    have c5 : Nat.card {v // ∃ u, (contractGraph H x y).Adj v u} + 1 ≤
        Nat.card {v // ∃ u, (splitGraph H x y).Adj v u} := by
      refine natCard_subtype_lt (fun v hv => ?_) ⟨x, hxy'.symm⟩
        (fun ⟨u, hu⟩ => contractGraph_not_adj_y u hu)
      obtain ⟨u, hu⟩ := hv
      by_cases hvx : v = x
      · exact ⟨y, hvx ▸ hxy'⟩
      · have h := (ι ⟨(v, u), hu⟩).adj
        have e : (ι ⟨(v, u), hu⟩).fst = v := liftV_of_ne hvx
        rw [e] at h
        exact ⟨_, h⟩
    rw [← hσ1] at c1
    rw [← hσ2] at c2
    rw [← hσ0] at c0
    rw [← hσ3] at c3
    omega
  -- the involution
  have hα : ∀ e, α3 e = e.symm := by
    intro e
    rcases hcover e with ⟨g, rfl⟩ | rfl | rfl
    · rw [hα3, Perm.mul_apply, swap_apply_of_ne_of_ne (hιa g) (hιb g), hα0ι]
      rfl
    · rw [hα3, Perm.mul_apply, swap_apply_left, hα0b, hadef, SimpleGraph.Dart.symm_symm]
    · rw [hα3, Perm.mul_apply, swap_apply_right, hα0a]
  -- the tails
  have hℓ0 : ℓ = 0 → h1 = h2 := fun h => by simp only [hh1, hh2, h, add_zero]
  have hfst : ∀ e, (σ3 e).fst = e.fst := by
    intro e
    rcases hcover e with ⟨g, rfl⟩ | rfl | rfl
    · rw [e3ι, e2 _ (hιa _)]
      by_cases hg2 : σ1 (ι g) = h2
      · rw [ite_eq_left hg2]
        -- `g` is the dart before `h2`
        have hg1 : σ0 (ι g) ≠ h1 := by
          intro h
          rw [e1 _ (hιb _), ite_eq_left h] at hg2
          exact hιb _ hg2.symm
        rw [e1 _ (hιb _), ite_eq_right hg1, hσ0ι] at hg2
        have hrot : M.rot g = M.rot (M.rd e0 (s + ℓ)) := by
          rw [hι hg2, ← M.rd_succ]
        have hgl : g = M.rd e0 (s + ℓ) := M.rot.injective hrot
        have hl : 1 ≤ ℓ := by
          by_contra hl
          apply hg1
          rw [hσ0ι, hι hg2, hh1, show ℓ = 0 by omega]
        rw [hgl, hfY _ (hA ℓ hl le_rfl)]
        rfl
      rw [ite_eq_right hg2, e1 _ (hιb _)]
      by_cases hg1 : σ0 (ι g) = h1
      · rw [ite_eq_left hg1]
        rw [hσ0ι] at hg1
        have hrot : M.rot g = M.rot (M.rd e0 s) := by rw [hι hg1, ← M.rd_succ]
        rw [M.rot.injective hrot, hfX _ hXs]
      rw [ite_eq_right hg1, hσ0ι]
      by_cases hgx : g.fst = x
      · obtain ⟨t, ht1, htk, rfl⟩ := hwin g hgx
        rw [← M.rd_succ]
        have htk' : t < k := by
          rcases Nat.lt_or_ge t k with h | h
          · exact h
          · exfalso
            apply hg1
            rw [hσ0rd, hh1]
            congr 1
            rw [show s + t + 1 = (s + 1) + k by omega]
            exact M.rd_add_rper e0 (s + 1)
        rw [show s + t + 1 = s + (t + 1) by omega]
        by_cases htl : t + 1 ≤ ℓ
        · rw [hfY _ (hA (t + 1) (by omega) htl), hfY _ (hA t ht1 (by omega))]
        by_cases htl' : t = ℓ
        · exfalso
          apply hg2
          rw [e1 _ (hιb _), ite_eq_right hg1, hσ0rd, hh2, ← htl']
        · rw [hfX _ (hB (t + 1) (by omega) (by omega)), hfX _ (hB t (by omega) (by omega))]
      · rw [hfst_ne _ hgx, hfst_ne _ (by rw [M.isRotationSystem.fst_apply]; exact hgx),
          M.isRotationSystem.fst_apply]
    · rw [e3a, e2 _ hab.symm, e1b]
      by_cases h12 : h1 = h2
      · rw [ite_eq_left h12]
      · rw [ite_eq_right h12]
        have hl : 1 ≤ ℓ := by
          by_contra hl
          exact h12 (hℓ0 (by omega))
        rw [hh1, hfY _ (hA 1 le_rfl hl)]
        rfl
    · rw [e3b, hh2, hfX _ hXl]
  obtain ⟨P, hP⟩ := exists_planeMap_of_hypermap σ3 α3 hd3 id Function.bijective_id hα hfst hcc
  refine ⟨P, fun d hd => ?_, fun d hd => ?_⟩
  · have hd' : d = ι (M.rd e0 s) := by
      refine (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext ?_ ?_)
      · have h' := congrArg Prod.fst hd
        change d.fst = x at h'
        rw [h', hfX _ hXs]
      · have h' := congrArg Prod.snd hd
        change d.snd = (M.rd e0 s).snd at h'
        rw [h', hιsnd]
    have := hP d
    simp only [id] at this
    rw [this, hd', hs3]
  · have hd' : d = b := (SimpleGraph.Dart.ext_iff _ _).2 hd
    have := hP d
    simp only [id] at this
    rw [this, hd', e3b, hh2]
    refine Prod.ext ?_ ?_
    · exact hfX _ hXl
    · exact hιsnd _

end Split

end LeanPool.K5MinorFreeChoosability
