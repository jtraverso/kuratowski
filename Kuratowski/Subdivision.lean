/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Kuratowski.Terminal

/-!
# Topological minors versus minors for `K₅` and `K₃,₃`

* `isTopologicalMinor_K33_of_isMinor`: a `K₃,₃` minor gives a `K₃,₃` subdivision (fix one
  connecting edge per edge of `K₃,₃`, symmetrically; in each branch set join the three endpoints
  to a centre by `exists_centre_three`; concatenate).
* `isTopologicalMinor_of_isMinor_K5`: a `K₅` minor gives a `K₅` or a `K₃,₃` subdivision (with
  `exists_centre_four` in every branch set: if all five are stars, a `K₅` subdivision; if the
  branch set of `w` has two centres `c ≠ d`, with `c` serving the neighbours `p, q` and `d` serving
  `r, s`, then `{c, r, s}` against `{d, p, q}` is a `K₃,₃` subdivision, using
  `exists_centre_three` in the branch sets of `p, q, r, s` with the three relevant terminals).
-/

@[expose] public section

open SimpleGraph

namespace Kuratowski

variable {V W : Type*}

/-- Assembling a subdivision from half-paths: for every ordered adjacent pair `(x, y)` a path
from the centre of `x` to an endpoint `m x y`, the endpoints `m x y` and `m y x` being adjacent;
two different half-paths meet only at a common centre. -/
theorem topologicalMinor_of_halfPaths {W' : Type*} {G : SimpleGraph V} {H : SimpleGraph W'}
    (ctr : W' → V) (hinj : Function.Injective ctr) (m : W' → W' → V)
    (hp : ∀ x y, H.Adj x y → G.Walk (ctr x) (m x y))
    (hpath : ∀ x y h, (hp x y h).IsPath)
    (hadj : ∀ x y, H.Adj x y → G.Adj (m x y) (m y x))
    (hmeet : ∀ x y h x' y' h', (x, y) ≠ (x', y') → ∀ v ∈ (hp x y h).support,
      v ∈ (hp x' y' h').support → x = x' ∧ v = ctr x)
    (hctr : ∀ x y h z, ctr z ∈ (hp x y h).support → z = x) :
    IsTopologicalMinor H G := by
  classical
  let path : ∀ x y, H.Adj x y → G.Walk (ctr x) (ctr y) := fun x y h =>
    (hp x y h).append (Walk.cons (hadj x y h) (hp y x h.symm).reverse)
  have hsupp : ∀ x y h, (path x y h).support =
      (hp x y h).support ++ (hp y x h.symm).support.reverse := by
    intro x y h
    simp only [path, Walk.support_append, Walk.support_cons, List.tail_cons,
      Walk.support_reverse]
  have hmem : ∀ x y h v, v ∈ (path x y h).support ↔
      v ∈ (hp x y h).support ∨ v ∈ (hp y x h.symm).support := by
    intro x y h v
    rw [hsupp, List.mem_append, List.mem_reverse]
  have hrange : ∀ a b (h : H.Adj a b) a' b' (h' : H.Adj a' b'), s(a, b) ≠ s(a', b') →
      ∀ v ∈ (hp a b h).support, v ∈ (hp a' b' h').support → v ∈ Set.range ctr := by
    intro a b h a' b' h' hs v hv hv'
    have hne : (a, b) ≠ (a', b') := by
      intro e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact hs rfl
    exact ⟨a, ((hmeet a b h a' b' h' hne v hv hv').2).symm⟩
  refine ⟨⟨⟨ctr, hinj⟩, path, ?_, ?_, ?_⟩⟩
  · intro x y h
    apply Walk.IsPath.mk'
    rw [hsupp, List.nodup_append]
    refine ⟨(hpath x y h).support_nodup, (List.nodup_reverse.mpr (hpath y x h.symm).support_nodup),
      ?_⟩
    intro a ha b hb hab
    subst hab
    rw [List.mem_reverse] at hb
    have hne : (x, y) ≠ (y, x) := by
      intro e
      simp only [Prod.mk.injEq] at e
      exact H.ne_of_adj h e.1
    exact H.ne_of_adj h (hmeet x y h y x h.symm hne a ha hb).1
  · intro x y h u hu
    rcases (hmem x y h _).1 hu with hu | hu
    · exact Or.inl (hctr x y h u hu)
    · exact Or.inr (hctr y x h.symm u hu)
  · intro x y h x' y' h' hs v hv hv'
    have hs1 : s(y, x) ≠ s(x', y') := by rwa [Sym2.eq_swap]
    have hs2 : s(x, y) ≠ s(y', x') := by rwa [Sym2.eq_swap (a := y')]
    have hs3 : s(y, x) ≠ s(y', x') := by rwa [Sym2.eq_swap, Sym2.eq_swap (a := y')]
    rcases (hmem x y h v).1 hv with hv | hv <;> rcases (hmem x' y' h' v).1 hv' with hv' | hv'
    · exact hrange _ _ _ _ _ _ hs v hv hv'
    · exact hrange _ _ _ _ _ _ hs2 v hv hv'
    · exact hrange _ _ _ _ _ _ hs1 v hv hv'
    · exact hrange _ _ _ _ _ _ hs3 v hv hv'

/-- Half-path assembly for `K₃,₃`, indexing the three half-paths at each vertex by `Fin 3`
(the index of the neighbour on the other side). -/
theorem topologicalMinor_K33_of_halfPaths {G : SimpleGraph V}
    (ctr : Fin 3 ⊕ Fin 3 → V) (m : Fin 3 ⊕ Fin 3 → Fin 3 → V)
    (hp : ∀ x j, G.Walk (ctr x) (m x j)) (hpath : ∀ x j, (hp x j).IsPath)
    (hadj : ∀ i j, G.Adj (m (Sum.inl i) j) (m (Sum.inr j) i))
    (hmeet : ∀ x j x' j', (x, j) ≠ (x', j') → ∀ v ∈ (hp x j).support,
      v ∈ (hp x' j').support → x = x' ∧ v = ctr x) :
    IsTopologicalMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G := by
  let idx : Fin 3 ⊕ Fin 3 → Fin 3 := Sum.elim id id
  refine topologicalMinor_of_halfPaths ctr ?_ (fun x y => m x (idx y))
    (fun x y _ => hp x (idx y)) (fun x y _ => hpath _ _) ?_ ?_ ?_
  · intro a b e
    by_contra hab
    have hne : (a, (0 : Fin 3)) ≠ (b, 0) := by simp [hab]
    exact hab (hmeet a 0 b 0 hne (ctr a) (Walk.start_mem_support _)
      (by rw [e]; exact Walk.start_mem_support _)).1
  · intro x y h
    rcases x with i | i <;> rcases y with j | j <;> simp at h
    · exact hadj i j
    · exact (hadj j i).symm
  · intro x y h x' y' h' hne
    apply hmeet
    intro e
    apply hne
    simp only [Prod.mk.injEq] at e ⊢
    obtain ⟨rfl, e⟩ := e
    refine ⟨rfl, ?_⟩
    rcases x with i | i <;> rcases y with j | j <;> rcases y' with k | k <;> simp_all [idx]
  · intro x y h z hz
    by_contra hzx
    have hne : (z, (0 : Fin 3)) ≠ (x, idx y) := by simp [hzx]
    exact hzx (hmeet z 0 x (idx y) hne (ctr z) (Walk.start_mem_support _) hz).1

/-- Symmetric choice of one connecting edge per edge of `H` in a minor model. -/
theorem MinorModel.exists_terminals [LinearOrder W] [Nonempty V] {G : SimpleGraph V}
    {H : SimpleGraph W} (M : MinorModel G H) :
    ∃ t : W → W → V, (∀ x y, H.Adj x y → t x y ∈ M.branch x) ∧
      ∀ x y, H.Adj x y → G.Adj (t x y) (t y x) := by
  classical
  choose u hu v hv huv using M.branch_adjacent
  refine ⟨fun x y => if h : H.Adj x y then (if x < y then u x y h else v y x h.symm)
    else Classical.arbitrary V, ?_, ?_⟩
  · intro x y h
    simp only [h, dite_true]
    split_ifs
    · exact hu x y h
    · exact hv y x h.symm
  · intro x y h
    simp only [h, h.symm, dite_true]
    rcases lt_or_gt_of_ne (H.ne_of_adj h) with hlt | hlt
    · simp only [hlt, ite_true, not_lt.mpr hlt.le, ite_false]
      exact huv x y h
    · simp only [hlt, ite_true, not_lt.mpr hlt.le, ite_false]
      exact (huv y x h.symm).symm

/-- List version of `topologicalMinor_K33_of_halfPaths`: the half-paths are only required to
exist, with prescribed supports. -/
theorem topologicalMinor_K33_of_supports {G : SimpleGraph V}
    (ctr : Fin 3 ⊕ Fin 3 → V) (m : Fin 3 ⊕ Fin 3 → Fin 3 → V) (L : Fin 3 ⊕ Fin 3 → Fin 3 → List V)
    (hex : ∀ x j, ∃ q : G.Walk (ctr x) (m x j), q.IsPath ∧ q.support = L x j)
    (hadj : ∀ i j, G.Adj (m (Sum.inl i) j) (m (Sum.inr j) i))
    (hmeet : ∀ x j x' j', (x, j) ≠ (x', j') → ∀ v ∈ L x j, v ∈ L x' j' → x = x' ∧ v = ctr x) :
    IsTopologicalMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G := by
  choose hp hpath hL using hex
  refine topologicalMinor_K33_of_halfPaths ctr m hp hpath hadj ?_
  intro x j x' j' hne v hv hv'
  rw [hL] at hv hv'
  exact hmeet x j x' j' hne v hv hv'

/-- The case of two centres in one branch set of a `K₅` minor gives a `K₃,₃` subdivision. -/
theorem topologicalMinor_K33_of_two_centres {G : SimpleGraph V}
    (M : MinorModel G (⊤ : SimpleGraph (Fin 5))) (t : Fin 5 → Fin 5 → V)
    (ht : ∀ x y, x ≠ y → t x y ∈ M.branch x) (hta : ∀ x y, x ≠ y → G.Adj (t x y) (t y x))
    (w P Q R S : Fin 5) (hwP : w ≠ P) (hwQ : w ≠ Q) (hwR : w ≠ R) (hwS : w ≠ S)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hPS : P ≠ S) (hQR : Q ≠ R) (hQS : Q ≠ S) (hRS : R ≠ S)
    {c d : V} (hcd : c ≠ d) (r : G.Walk c d) (hr : r.IsPath)
    (hrB : ∀ v ∈ r.support, v ∈ M.branch w)
    (pc : G.Walk c (t w P)) (qc : G.Walk c (t w Q)) (rd : G.Walk d (t w R))
    (sd : G.Walk d (t w S))
    (hpc : pc.IsPath) (hqc : qc.IsPath) (hrd : rd.IsPath) (hsd : sd.IsPath)
    (hpcB : ∀ v ∈ pc.support, v ∈ M.branch w) (hqcB : ∀ v ∈ qc.support, v ∈ M.branch w)
    (hrdB : ∀ v ∈ rd.support, v ∈ M.branch w) (hsdB : ∀ v ∈ sd.support, v ∈ M.branch w)
    (hpq : ∀ v ∈ pc.support, v ∈ qc.support → v = c)
    (hrs : ∀ v ∈ rd.support, v ∈ sd.support → v = d)
    (hpr : ∀ v ∈ pc.support, v ∉ rd.support) (hps : ∀ v ∈ pc.support, v ∉ sd.support)
    (hqr : ∀ v ∈ qc.support, v ∉ rd.support) (hqs : ∀ v ∈ qc.support, v ∉ sd.support)
    (hpcr : ∀ v ∈ pc.support, v ∈ r.support → v = c)
    (hqcr : ∀ v ∈ qc.support, v ∈ r.support → v = c)
    (hrdr : ∀ v ∈ rd.support, v ∈ r.support → v = d)
    (hsdr : ∀ v ∈ sd.support, v ∈ r.support → v = d) :
    IsTopologicalMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G := by
  classical
  have hPw := hwP.symm
  have hQw := hwQ.symm
  have hRw := hwR.symm
  have hSw := hwS.symm
  have hQP := hPQ.symm
  have hRP := hPR.symm
  have hSP := hPS.symm
  have hRQ := hQR.symm
  have hSQ := hQS.symm
  have hSR := hRS.symm
  obtain ⟨cP, hcP, PP, hPP, hPPB, hPPm⟩ := exists_centre_three (ι := Fin 3) (by simp)
    (M.branch_connected P) ![t P w, t P R, t P S]
    (by intro j; fin_cases j <;> exact ht _ _ (by assumption))
  obtain ⟨cQ, hcQ, PQ, hPQ', hPQB, hPQm⟩ := exists_centre_three (ι := Fin 3) (by simp)
    (M.branch_connected Q) ![t Q w, t Q R, t Q S]
    (by intro j; fin_cases j <;> exact ht _ _ (by assumption))
  obtain ⟨cR, hcR, PR, hPR', hPRB, hPRm⟩ := exists_centre_three (ι := Fin 3) (by simp)
    (M.branch_connected R) ![t R w, t R P, t R Q]
    (by intro j; fin_cases j <;> exact ht _ _ (by assumption))
  obtain ⟨cS, hcS, PS, hPS', hPSB, hPSm⟩ := exists_centre_three (ι := Fin 3) (by simp)
    (M.branch_connected S) ![t S w, t S P, t S Q]
    (by intro j; fin_cases j <;> exact ht _ _ (by assumption))
  have hnil : ¬ r.Nil := Walk.not_nil_of_ne hcd
  have htail : ∀ v ∈ r.tail.reverse.support, v ∈ r.support := by
    intro v hv
    rw [Walk.support_reverse, List.mem_reverse, Walk.support_tail_of_not_nil _ hnil] at hv
    exact List.mem_of_mem_tail hv
  have hctail : c ∉ r.tail.reverse.support := by
    intro hv
    rw [Walk.support_reverse, List.mem_reverse, Walk.support_tail_of_not_nil _ hnil] at hv
    have hnd := hr.support_nodup
    rw [← Walk.cons_tail_support] at hnd
    exact (List.nodup_cons.mp hnd).1 hv
  let ctr' : Fin 3 ⊕ Fin 3 → V := Sum.elim ![c, cR, cS] ![d, cP, cQ]
  let m' : Fin 3 ⊕ Fin 3 → Fin 3 → V :=
    Sum.elim ![![c, t w P, t w Q], ![t R w, t R P, t R Q], ![t S w, t S P, t S Q]]
      ![![r.snd, t w R, t w S], ![t P w, t P R, t P S], ![t Q w, t Q R, t Q S]]
  let L0 : Fin 3 → List V := ![[c], pc.support, qc.support]
  let LD : Fin 3 → List V := ![r.tail.reverse.support, rd.support, sd.support]
  let L : Fin 3 ⊕ Fin 3 → Fin 3 → List V :=
    Sum.elim ![L0, fun j => (PR j).support, fun j => (PS j).support]
      ![LD, fun j => (PP j).support, fun j => (PQ j).support]
  let reg : Fin 3 ⊕ Fin 3 → Fin 5 := Sum.elim ![w, R, S] ![w, P, Q]
  have hregL : ∀ x j, ∀ v ∈ L x j, v ∈ M.branch (reg x) := by
    intro x j v hv
    rcases x with i | i <;> fin_cases i
    · fin_cases j
      · obtain rfl := List.mem_singleton.mp hv
        exact hrB _ r.start_mem_support
      · exact hpcB v hv
      · exact hqcB v hv
    · exact hPRB j v hv
    · exact hPSB j v hv
    · fin_cases j
      · exact hrB v (htail v hv)
      · exact hrdB v hv
      · exact hsdB v hv
    · exact hPPB j v hv
    · exact hPQB j v hv
  have meetC : ∀ j j', j ≠ j' → ∀ v ∈ L0 j, v ∈ L0 j' → v = c := by
    intro j j' hj v hv hv'
    fin_cases j <;> fin_cases j'
    all_goals first
      | exact absurd rfl hj
      | exact List.mem_singleton.mp hv
      | exact List.mem_singleton.mp hv'
      | exact hpq v hv hv'
      | exact hpq v hv' hv
  have meetD : ∀ j j', j ≠ j' → ∀ v ∈ LD j, v ∈ LD j' → v = d := by
    intro j j' hj v hv hv'
    fin_cases j <;> fin_cases j'
    all_goals first
      | exact absurd rfl hj
      | exact hrdr v hv' (htail v hv)
      | exact hrdr v hv (htail v hv')
      | exact hsdr v hv' (htail v hv)
      | exact hsdr v hv (htail v hv')
      | exact hrs v hv hv'
      | exact hrs v hv' hv
  have disjCD : ∀ j j', ∀ v ∈ L0 j, v ∈ LD j' → False := by
    intro j j' v hv hv'
    fin_cases j <;> fin_cases j'
    · obtain rfl := List.mem_singleton.mp hv
      exact hctail hv'
    · obtain rfl := List.mem_singleton.mp hv
      exact hcd (hrdr _ hv' r.start_mem_support)
    · obtain rfl := List.mem_singleton.mp hv
      exact hcd (hsdr _ hv' r.start_mem_support)
    · have e := hpcr v hv (htail v hv')
      subst e
      exact hctail hv'
    · exact hpr v hv hv'
    · exact hps v hv hv'
    · have e := hqcr v hv (htail v hv')
      subst e
      exact hctail hv'
    · exact hqr v hv hv'
    · exact hqs v hv hv'
  refine topologicalMinor_K33_of_supports ctr' m' L ?_ ?_ ?_
  · intro x j
    rcases x with i | i <;> fin_cases i
    · fin_cases j
      · exact ⟨Walk.nil, Walk.IsPath.nil, rfl⟩
      · exact ⟨pc, hpc, rfl⟩
      · exact ⟨qc, hqc, rfl⟩
    · exact ⟨PR j, hPR' j, rfl⟩
    · exact ⟨PS j, hPS' j, rfl⟩
    · fin_cases j
      · exact ⟨r.tail.reverse, hr.tail.reverse, rfl⟩
      · exact ⟨rd, hrd, rfl⟩
      · exact ⟨sd, hsd, rfl⟩
    · exact ⟨PP j, hPP j, rfl⟩
    · exact ⟨PQ j, hPQ' j, rfl⟩
  · intro i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact Walk.adj_snd hnil
      | exact hta _ _ (by assumption)
  · intro x j x' j' hne v hv hv'
    by_cases hrr : reg x = reg x'
    swap
    · exact absurd (hregL x' j' v hv')
        (Finset.disjoint_left.mp (M.branch_disjoint _ _ hrr) (hregL x j v hv))
    have hj : x = x' → j ≠ j' := by rintro rfl rfl; exact hne rfl
    rcases x with i | i <;> rcases x' with i' | i' <;> fin_cases i <;> fin_cases i'
    all_goals try (simp [reg, hwP, hwQ, hwR, hwS, hPQ, hPR, hPS, hQR, hQS, hRS, hPw, hQw, hRw,
      hSw, hQP, hRP, hSP, hRQ, hSQ, hSR] at hrr; done)
    · exact ⟨rfl, meetC j j' (hj rfl) v hv hv'⟩
    · exact ⟨rfl, hPRm j j' (hj rfl) v hv hv'⟩
    · exact ⟨rfl, hPSm j j' (hj rfl) v hv hv'⟩
    · exact (disjCD j j' v hv hv').elim
    · exact (disjCD j' j v hv' hv).elim
    · exact ⟨rfl, meetD j j' (hj rfl) v hv hv'⟩
    · exact ⟨rfl, hPPm j j' (hj rfl) v hv hv'⟩
    · exact ⟨rfl, hPQm j j' (hj rfl) v hv hv'⟩

/-- A `K₃,₃` minor gives a `K₃,₃` subdivision. -/
theorem isTopologicalMinor_K33_of_isMinor {G : SimpleGraph V}
    (h : IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G) :
    IsTopologicalMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G := by
  classical
  obtain ⟨M⟩ := h
  have : Nonempty V := ⟨(M.branch_nonempty (Sum.inl 0)).choose⟩
  let _ : LinearOrder (Fin 3 ⊕ Fin 3) :=
    LinearOrder.lift' finSumFinEquiv finSumFinEquiv.injective
  obtain ⟨t, ht, hta⟩ := M.exists_terminals
  let opp : Fin 3 ⊕ Fin 3 → Fin 3 → Fin 3 ⊕ Fin 3 :=
    Sum.elim (fun _ j => Sum.inr j) (fun _ j => Sum.inl j)
  have hopp : ∀ x j, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj x (opp x j) := by
    intro x j; rcases x with i | i <;> simp [opp]
  choose c hc P hP hPB hPmeet using fun x => exists_centre_three (ι := Fin 3) (by simp)
    (M.branch_connected x) (fun j => t x (opp x j)) (fun j => ht _ _ (hopp x j))
  refine topologicalMinor_K33_of_halfPaths c (fun x j => t x (opp x j)) P hP ?_ ?_
  · intro i j
    exact hta (Sum.inl i) (Sum.inr j) (by simp)
  · intro x j x' j' hne v hv hv'
    by_cases hx : x = x'
    · subst hx
      have hj : j ≠ j' := by rintro rfl; exact hne rfl
      exact ⟨rfl, hPmeet x j j' hj v hv hv'⟩
    · exact absurd (hPB x' j' v hv')
        (Finset.disjoint_left.mp (M.branch_disjoint x x' hx) (hPB x j v hv))

/-- A `K₅` minor gives a `K₅` subdivision or a `K₃,₃` subdivision. -/
theorem isTopologicalMinor_of_isMinor_K5 {G : SimpleGraph V}
    (h : IsMinor (⊤ : SimpleGraph (Fin 5)) G) :
    IsTopologicalMinor (⊤ : SimpleGraph (Fin 5)) G ∨
      IsTopologicalMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G := by
  classical
  obtain ⟨M⟩ := h
  have : Nonempty V := ⟨(M.branch_nonempty 0).choose⟩
  obtain ⟨t, ht, hta⟩ := M.exists_terminals
  have ht' : ∀ x y, x ≠ y → t x y ∈ M.branch x := fun x y h => ht x y ((top_adj x y).mpr h)
  have hta' : ∀ x y, x ≠ y → G.Adj (t x y) (t y x) := fun x y h => hta x y ((top_adj x y).mpr h)
  have hdisj : ∀ a b, a ≠ b → ∀ v, v ∈ M.branch a → v ∈ M.branch b → False :=
    fun a b hab v ha hb => Finset.disjoint_left.mp (M.branch_disjoint a b hab) ha hb
  choose c hc d hd r ctr pp hr hrB hctr hcard hpp hppB hppm hppr using fun w : Fin 5 =>
    exists_centre_four (ι := {w' : Fin 5 // w' ≠ w}) (by simp) (M.branch_connected w)
      (fun i => t w i.1) (fun i => ht' w i.1 i.2.symm)
  by_cases hall : ∀ w, c w = d w
  · left
    have hcc : ∀ w i, ctr w i = c w :=
      fun w i => (hctr w i).elim id (fun h => h.trans (hall w).symm)
    refine topologicalMinor_of_halfPaths c ?_ t
      (fun x y h => (pp x ⟨y, ((top_adj _ _).mp h).symm⟩).copy (hcc _ _) rfl)
      (fun x y h => (Walk.isPath_copy _ _ _).mpr (hpp _ _)) hta ?_ ?_
    · intro a b e
      by_contra hab
      exact hdisj a b hab (c a) (hc a) (e ▸ hc b)
    · intro x y h x' y' h' hne v hv hv'
      rw [Walk.support_copy] at hv hv'
      by_cases hx : x = x'
      · subst hx
        have hy : (⟨y, ((top_adj _ _).mp h).symm⟩ : {w' : Fin 5 // w' ≠ x}) ≠
            ⟨y', ((top_adj _ _).mp h').symm⟩ := by
          intro e
          apply hne
          simp only [Subtype.mk.injEq] at e
          rw [e]
        exact ⟨rfl, ((hppm x _ _ hy v hv hv').1).trans (hcc _ _)⟩
      · exact (hdisj x x' hx v (hppB x _ v hv) (hppB x' _ v hv')).elim
    · intro x y h z hz
      rw [Walk.support_copy] at hz
      by_contra hzx
      exact hdisj z x hzx (c z) (hc z) (hppB x _ _ hz)
  · right
    push Not at hall
    obtain ⟨w, hw⟩ := hall
    obtain ⟨p1, p2, hp12, hf⟩ := Finset.card_eq_two.mp (hcard w hw)
    have hcomp : (Finset.univ.filter fun i => ¬ ctr w i = c w).card = 2 := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i => ctr w i = c w)
      rw [hcard w hw, Finset.card_univ] at this
      have h4 : Fintype.card {w' : Fin 5 // w' ≠ w} = 4 := by simp
      omega
    obtain ⟨r1, r2, hr12, hf'⟩ := Finset.card_eq_two.mp hcomp
    have hp1 : ctr w p1 = c w := by
      have : p1 ∈ Finset.univ.filter fun i => ctr w i = c w := by rw [hf]; simp
      simpa using this
    have hp2 : ctr w p2 = c w := by
      have : p2 ∈ Finset.univ.filter fun i => ctr w i = c w := by rw [hf]; simp
      simpa using this
    have hr1' : ctr w r1 ≠ c w := by
      have : r1 ∈ Finset.univ.filter fun i => ¬ ctr w i = c w := by rw [hf']; simp
      simpa using this
    have hr2' : ctr w r2 ≠ c w := by
      have : r2 ∈ Finset.univ.filter fun i => ¬ ctr w i = c w := by rw [hf']; simp
      simpa using this
    have hr1 : ctr w r1 = d w := (hctr w r1).resolve_left hr1'
    have hr2 : ctr w r2 = d w := (hctr w r2).resolve_left hr2'
    have hp1r1 : p1 ≠ r1 := fun e => hr1' (e ▸ hp1)
    have hp1r2 : p1 ≠ r2 := fun e => hr2' (e ▸ hp1)
    have hp2r1 : p2 ≠ r1 := fun e => hr1' (e ▸ hp2)
    have hp2r2 : p2 ≠ r2 := fun e => hr2' (e ▸ hp2)
    have hval : ∀ a b : {w' : Fin 5 // w' ≠ w}, a ≠ b → a.1 ≠ b.1 :=
      fun a b hab e => hab (Subtype.ext e)
    refine topologicalMinor_K33_of_two_centres M t ht' hta' w p1.1 p2.1 r1.1 r2.1
      p1.2.symm p2.2.symm r1.2.symm r2.2.symm (hval _ _ hp12) (hval _ _ hp1r1)
      (hval _ _ hp1r2) (hval _ _ hp2r1) (hval _ _ hp2r2) (hval _ _ hr12) hw (r w) (hr w)
      (hrB w) ((pp w p1).copy hp1 rfl) ((pp w p2).copy hp2 rfl) ((pp w r1).copy hr1 rfl)
      ((pp w r2).copy hr2 rfl) ((Walk.isPath_copy _ _ _).mpr (hpp _ _))
      ((Walk.isPath_copy _ _ _).mpr (hpp _ _)) ((Walk.isPath_copy _ _ _).mpr (hpp _ _))
      ((Walk.isPath_copy _ _ _).mpr (hpp _ _)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [Walk.support_copy]
    · exact hppB w p1
    · exact hppB w p2
    · exact hppB w r1
    · exact hppB w r2
    · intro v hv hv'
      exact (hppm w p1 p2 hp12 v hv hv').1.trans hp1
    · intro v hv hv'
      exact (hppm w r1 r2 hr12 v hv hv').1.trans hr1
    · intro v hv hv'
      exact hw (hp1.symm.trans ((hppm w p1 r1 hp1r1 v hv hv').2.trans hr1))
    · intro v hv hv'
      exact hw (hp1.symm.trans ((hppm w p1 r2 hp1r2 v hv hv').2.trans hr2))
    · intro v hv hv'
      exact hw (hp2.symm.trans ((hppm w p2 r1 hp2r1 v hv hv').2.trans hr1))
    · intro v hv hv'
      exact hw (hp2.symm.trans ((hppm w p2 r2 hp2r2 v hv hv').2.trans hr2))
    · intro v hv hv'
      exact (hppr w hw p1 v hv hv').trans hp1
    · intro v hv hv'
      exact (hppr w hw p2 v hv hv').trans hp2
    · intro v hv hv'
      exact (hppr w hw r1 v hv hv').trans hr1
    · intro v hv hv'
      exact (hppr w hw r2 v hv hv').trans hr2

end Kuratowski
