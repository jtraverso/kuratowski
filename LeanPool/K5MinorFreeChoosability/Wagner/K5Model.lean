/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.Separation

/-!
# `K_5` minor models: minimality, splits and bridges

Tools for Hall's lemma (`LeanPool.K5MinorFreeChoosability.Wagner.Hall`):

* `CliqueMinorModel.size`, `CliqueMinorModel.replace`: total size of a `K_5` model and
  replacement of one branch set by a smaller connected set still touching the others;
  a minimum-size model admits no such replacement (`IsMinimalK5.no_replace`).
* `isMinor_K33_of_split`: if a branch set splits into two touching connected parts, each
  touching two other branch sets, and together touching all of them, there is a
  `K_{3,3}` minor.
* `isMinor_K33_of_bridge`: the `K_{3,3}` minor produced by a connected set touching three
  branch sets of a (partially shrunk) `K_5` model.
* `false_of_noSmallSep`: the separation argument used to find bridges.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} {G : SimpleGraph V}

/-! ### Index bookkeeping in `Fin 5` -/

theorem fin5_exists_third (a b : Fin 5) : ∃ c, c ≠ a ∧ c ≠ b := by
  revert a b; decide

theorem fin5_exists_two_ne (i : Fin 5) : ∃ j k, j ≠ k ∧ j ≠ i ∧ k ≠ i := by
  revert i; decide

theorem fin5_exists_rest (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ d e, d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ d ≠ e := by
  revert a b c; decide

/-- Splitting four labels into two pairs: a Boolean core checked by `decide`. -/
theorem pair_choice_bool : ∀ x0 x1 x2 x3 y0 y1 y2 y3 : Bool,
    (x0 || y0) = true → (x1 || y1) = true → (x2 || y2) = true → (x3 || y3) = true →
    ((x0 && x1) || (x0 && x2) || (x0 && x3) || (x1 && x2) || (x1 && x3) || (x2 && x3)) = true →
    ((y0 && y1) || (y0 && y2) || (y0 && y3) || (y1 && y2) || (y1 && y3) || (y2 && y3)) = true →
    ((x0 && x1 && y2 && y3) || (x0 && x2 && y1 && y3) || (x0 && x3 && y1 && y2) ||
      (x1 && x2 && y0 && y3) || (x1 && x3 && y0 && y2) || (x2 && x3 && y0 && y1)) = true := by
  decide

/-- If every one of four labels is good for `p` or for `q`, and each of `p`, `q` has two
good labels, then the labels split into two `p`-good and two `q`-good ones. -/
theorem pair_choice_fin4 (p q : Fin 4 → Prop) (hpq : ∀ k, p k ∨ q k)
    (hp : ∃ k l, k ≠ l ∧ p k ∧ p l) (hq : ∃ k l, k ≠ l ∧ q k ∧ q l) :
    ∃ a b c d, a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ p a ∧ p b ∧ q c ∧ q d := by
  classical
  have key := pair_choice_bool (decide (p 0)) (decide (p 1)) (decide (p 2)) (decide (p 3))
    (decide (q 0)) (decide (q 1)) (decide (q 2)) (decide (q 3))
    (by simpa using hpq 0) (by simpa using hpq 1) (by simpa using hpq 2) (by simpa using hpq 3)
    (by
      obtain ⟨k, l, hkl, hk, hl⟩ := hp
      fin_cases k <;> fin_cases l <;> simp_all)
    (by
      obtain ⟨k, l, hkl, hk, hl⟩ := hq
      fin_cases k <;> fin_cases l <;> simp_all)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at key
  rcases key with ((((⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) |
    ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide,
      h1, h2, h3, h4⟩
  · exact ⟨0, 2, 1, 3, by decide, by decide, by decide, by decide, by decide, by decide,
      h1, h2, h3, h4⟩
  · exact ⟨0, 3, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide,
      h1, h2, h3, h4⟩
  · exact ⟨1, 2, 0, 3, by decide, by decide, by decide, by decide, by decide, by decide,
      h1, h2, h3, h4⟩
  · exact ⟨1, 3, 0, 2, by decide, by decide, by decide, by decide, by decide, by decide,
      h1, h2, h3, h4⟩
  · exact ⟨2, 3, 0, 1, by decide, by decide, by decide, by decide, by decide, by decide,
      h1, h2, h3, h4⟩

/-- `pair_choice_fin4` for the four labels of `Fin 5` different from `i`. -/
theorem pair_choice_fin5 (i : Fin 5) (p q : Fin 5 → Prop) (hpq : ∀ k, k ≠ i → p k ∨ q k)
    (hp : ∃ k l, k ≠ l ∧ k ≠ i ∧ l ≠ i ∧ p k ∧ p l)
    (hq : ∃ k l, k ≠ l ∧ k ≠ i ∧ l ≠ i ∧ q k ∧ q l) :
    ∃ a b c d, a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      a ≠ i ∧ b ≠ i ∧ c ≠ i ∧ d ≠ i ∧ p a ∧ p b ∧ q c ∧ q d := by
  have conv : ∀ r : Fin 5 → Prop, (∃ k l, k ≠ l ∧ k ≠ i ∧ l ≠ i ∧ r k ∧ r l) →
      ∃ k l : Fin 4, k ≠ l ∧ r (i.succAbove k) ∧ r (i.succAbove l) := by
    rintro r ⟨k, l, hkl, hki, hli, hk, hl⟩
    obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hki
    obtain ⟨l', rfl⟩ := Fin.exists_succAbove_eq hli
    exact ⟨k', l', fun h => hkl (h ▸ rfl), hk, hl⟩
  obtain ⟨a, b, c, d, hab, hcd, hac, had, hbc, hbd, ha, hb, hc, hd⟩ :=
    pair_choice_fin4 (fun k => p (i.succAbove k)) (fun k => q (i.succAbove k))
      (fun k => hpq _ (Fin.succAbove_ne i k)) (conv p hp) (conv q hq)
  have inj := Fin.succAbove_right_injective (p := i)
  exact ⟨_, _, _, _, fun h => hab (inj h), fun h => hcd (inj h), fun h => hac (inj h),
    fun h => had (inj h), fun h => hbc (inj h), fun h => hbd (inj h), Fin.succAbove_ne i a,
    Fin.succAbove_ne i b, Fin.succAbove_ne i c, Fin.succAbove_ne i d, ha, hb, hc, hd⟩

/-! ### Size, replacement and minimal models -/

namespace CliqueMinorModel

/-- Total number of vertices used by a `K_k` model. -/
def size {k : ℕ} (M : CliqueMinorModel G k) : ℕ := ∑ i, (M.branch i).card

/-- Replace the branch set `i` by a connected subset still touching every other branch
set. -/
def replace {k : ℕ} (M : CliqueMinorModel G k) (i : Fin k) (B' : Finset V)
    (hc : ConnSet G ↑B') (hsub : B' ⊆ M.branch i)
    (ht : ∀ j, j ≠ i → Touch G B' (M.branch j)) : CliqueMinorModel G k :=
  CliqueMinorModel.ofConnSet (Function.update M.branch i B')
    (fun j => by
      by_cases hj : j = i
      · subst hj; simpa using hc
      · simpa [hj] using M.connSet j)
    (fun j l hjl => by
      by_cases hj : j = i
      · subst hj
        have hl : l ≠ j := fun h => hjl h.symm
        simpa [hl] using (M.branch_disjoint j l hjl).mono_left hsub
      · by_cases hl : l = i
        · subst hl
          simpa [hj] using (M.branch_disjoint j l hjl).mono_right hsub
        · simpa [hj, hl] using M.branch_disjoint j l hjl)
    (fun j l hjl => by
      by_cases hj : j = i
      · subst hj
        have hl : l ≠ j := fun h => hjl h.symm
        simpa [hl, Touch] using ht l hl
      · by_cases hl : l = i
        · subst hl
          obtain ⟨a, ha, b, hb, hab⟩ := ht j hj
          exact ⟨b, by simpa [hj] using hb, a, by simpa using ha, hab.symm⟩
        · simpa [hj, hl] using M.branch_adjacent j l hjl)

theorem size_replace_lt {k : ℕ} (M : CliqueMinorModel G k) (i : Fin k) (B' : Finset V)
    (hc : ConnSet G ↑B') (hsub : B' ⊆ M.branch i) (hne : B' ≠ M.branch i)
    (ht : ∀ j, j ≠ i → Touch G B' (M.branch j)) : (M.replace i B' hc hsub ht).size < M.size := by
  unfold size replace CliqueMinorModel.ofConnSet
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j = i
    · subst hj; simpa using Finset.card_le_card hsub
    · simp [hj]
  · exact ⟨i, Finset.mem_univ _, by
      simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)⟩

end CliqueMinorModel

/-- A `K_5` model of minimum total size. -/
def IsMinimalK5 (M : CliqueMinorModel G 5) : Prop := ∀ M' : CliqueMinorModel G 5, M.size ≤ M'.size

theorem exists_isMinimalK5 (h : Nonempty (CliqueMinorModel G 5)) :
    ∃ M : CliqueMinorModel G 5, IsMinimalK5 M := by
  classical
  have hex : ∃ n, ∃ M : CliqueMinorModel G 5, M.size = n := ⟨_, h.some, rfl⟩
  obtain ⟨M, hM⟩ := Nat.find_spec hex
  refine ⟨M, fun M' => ?_⟩
  rw [hM]
  exact Nat.find_min' hex ⟨M', rfl⟩

theorem IsMinimalK5.no_replace {M : CliqueMinorModel G 5} (hM : IsMinimalK5 M) (i : Fin 5)
    (B' : Finset V) (hc : ConnSet G ↑B') (hsub : B' ⊆ M.branch i) (hne : B' ≠ M.branch i)
    (ht : ∀ j, j ≠ i → Touch G B' (M.branch j)) : False := by
  have h1 := M.size_replace_lt i B' hc hsub hne ht
  have h2 := hM (M.replace i B' hc hsub ht)
  omega

/-! ### Splits and bridges -/

/-- **Split lemma.**  If the branch set `i` of a `K_5` model contains two disjoint touching
connected sets `X`, `Y`, each touching two further branch sets and together touching all
four others, then `G` has a `K_{3,3}` minor. -/
theorem isMinor_K33_of_split (M : CliqueMinorModel G 5) (i : Fin 5) (X Y : Finset V)
    (hX : X ⊆ M.branch i) (hY : Y ⊆ M.branch i) (hXY : Disjoint X Y)
    (cX : ConnSet G ↑X) (cY : ConnSet G ↑Y) (tXY : Touch G X Y)
    (hcov : ∀ j, j ≠ i → Touch G X (M.branch j) ∨ Touch G Y (M.branch j))
    (twoX : ∃ j k, j ≠ k ∧ j ≠ i ∧ k ≠ i ∧ Touch G X (M.branch j) ∧ Touch G X (M.branch k))
    (twoY : ∃ j k, j ≠ k ∧ j ≠ i ∧ k ≠ i ∧ Touch G Y (M.branch j) ∧ Touch G Y (M.branch k)) :
    IsMinor K33 G := by
  obtain ⟨a, b, c, d, hab, hcd, hac, had, hbc, hbd, hai, hbi, hci, hdi, ha, hb, hc, hd⟩ :=
    pair_choice_fin5 i _ _ hcov twoX twoY
  have D := M.branch_disjoint
  have T := M.branch_adjacent
  have tc : ∀ j l, j ≠ l → Touch G (M.branch j) (M.branch l) := fun j l h => T j l h
  -- left: X, B_c, B_d; right: Y, B_a, B_b
  exact isMinor_K33_of_six cX (M.connSet c) (M.connSet d) cY (M.connSet a) (M.connSet b)
    ((D i c hci.symm).mono_left hX) ((D i d hdi.symm).mono_left hX) (D c d hcd)
    ((D i a hai.symm).mono_left hY) ((D i b hbi.symm).mono_left hY) (D a b hab)
    hXY ((D i a hai.symm).mono_left hX) ((D i b hbi.symm).mono_left hX)
    ((D c i hci).mono_right hY) (D c a (Ne.symm hac)) (D c b (Ne.symm hbc))
    ((D d i hdi).mono_right hY) (D d a (Ne.symm had)) (D d b (Ne.symm hbd))
    tXY ha hb hc.symm (tc c a (Ne.symm hac)) (tc c b (Ne.symm hbc))
    hd.symm (tc d a (Ne.symm had)) (tc d b (Ne.symm hbd))

/-- **Bridge lemma.**  Let `a, b, c, d, e` be the five indices of a `K_5` model, and let
`Pa ⊆ B_a`, `Pb ⊆ B_b` be connected subsets still touching `B_d` and `B_e`.  A connected
set `C` disjoint from `Pa, Pb, B_c, B_d, B_e` touching `Pa`, `Pb` and `B_c` yields a
`K_{3,3}` minor with sides `{C, B_d, B_e}` and `{Pa, Pb, B_c}`. -/
theorem isMinor_K33_of_bridge (M : CliqueMinorModel G 5) {a b c d e : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (C Pa Pb : Finset V) (hPa : Pa ⊆ M.branch a) (hPb : Pb ⊆ M.branch b)
    (cC : ConnSet G ↑C) (cPa : ConnSet G ↑Pa) (cPb : ConnSet G ↑Pb)
    (dCa : Disjoint C Pa) (dCb : Disjoint C Pb) (dCc : Disjoint C (M.branch c))
    (dCd : Disjoint C (M.branch d)) (dCe : Disjoint C (M.branch e))
    (tCa : Touch G C Pa) (tCb : Touch G C Pb) (tCc : Touch G C (M.branch c))
    (tda : Touch G (M.branch d) Pa) (tdb : Touch G (M.branch d) Pb)
    (tea : Touch G (M.branch e) Pa) (teb : Touch G (M.branch e) Pb) : IsMinor K33 G := by
  have D := M.branch_disjoint
  have tc : ∀ j l, j ≠ l → Touch G (M.branch j) (M.branch l) := fun j l h => M.branch_adjacent j l h
  exact isMinor_K33_of_six cC (M.connSet d) (M.connSet e) cPa cPb (M.connSet c)
    dCd dCe (D d e hde) ((D a b hab).mono hPa hPb) ((D a c hac).mono_left hPa)
    ((D b c hbc).mono_left hPb) dCa dCb dCc ((D d a (Ne.symm had)).mono_right hPa)
    ((D d b (Ne.symm hbd)).mono_right hPb) (D d c (Ne.symm hcd))
    ((D e a (Ne.symm hae)).mono_right hPa) ((D e b (Ne.symm hbe)).mono_right hPb)
    (D e c (Ne.symm hce)) tCa tCb tCc tda tdb (tc d c (Ne.symm hcd)) tea teb
    (tc e c (Ne.symm hce))

/-- The separation argument: a nonempty set `Y ⊆ S` all of whose outside neighbours lie in a
set `N ⊆ S` of at most two vertices, with some vertex of `S` outside `Y ∪ N`, contradicts
`NoSmallSep`. -/
theorem false_of_noSmallSep [DecidableEq V] {S : Finset V} (hsep : NoSmallSep G S) (Y N : Finset V)
    (hYS : Y ⊆ S) (hNS : N ⊆ S) (hYN : Disjoint Y N) (hN : N.card ≤ 2) (hYne : Y.Nonempty)
    (hout : ∃ v ∈ S, v ∉ Y ∧ v ∉ N) (hnb : ∀ y ∈ Y, ∀ u, G.Adj y u → u ∈ Y ∨ u ∈ N) :
    False := by
  have hcov : (Y ∪ N) ∪ (S \ Y) = S := by
    ext v; constructor
    · intro hv
      rcases Finset.mem_union.1 hv with hv | hv
      · rcases Finset.mem_union.1 hv with hv | hv
        · exact hYS hv
        · exact hNS hv
      · exact (Finset.mem_sdiff.1 hv).1
    · intro hv
      by_cases hvY : v ∈ Y
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hvY)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hv, hvY⟩)
  have hint : (Y ∪ N) ∩ (S \ Y) ⊆ N := by
    intro v hv
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hv
    rcases Finset.mem_union.1 h1 with h | h
    · exact absurd h (Finset.mem_sdiff.1 h2).2
    · exact h
  rcases hsep (Y ∪ N) (S \ Y) hcov ((Finset.card_le_card hint).trans hN) (by
      intro u hu huB v hv hvA huv
      have huY : u ∈ Y := by
        rcases Finset.mem_union.1 hu with h | h
        · exact h
        · exact absurd (Finset.mem_sdiff.2 ⟨hNS h, Finset.disjoint_right.1 hYN h⟩) huB
      rcases hnb u huY v huv with h | h
      · exact (Finset.mem_sdiff.1 hv).2 h
      · exact hvA (Finset.mem_union_right _ h)) with h | h
  · obtain ⟨y, hy⟩ := hYne
    exact (Finset.mem_sdiff.1 (h (Finset.mem_union_left _ hy))).2 hy
  · obtain ⟨v, hvS, hvY, hvN⟩ := hout
    rcases Finset.mem_union.1 (h (Finset.mem_sdiff.2 ⟨hvS, hvY⟩)) with h' | h'
    · exact hvY h'
    · exact hvN h'

end LeanPool.K5MinorFreeChoosability
