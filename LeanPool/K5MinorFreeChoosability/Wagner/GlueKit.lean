/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.EdgeAdd

/-!
# Hypermap lemmas for gluing plane maps

* the Euler defect is additive on disjoint unions of hypermaps (`eulerDefect_sumCongr`);
* `sameCycle_of_agree_until`: a permutation agreeing with another one along an orbit segment
  follows it to the end of the segment;
* counting lemmas for cycles after removing a dart and for unions of vertex sets.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

section Sum

variable {α β : Type*}

/-- A setoid on a sum that never relates the two sides has as many classes as its two
restrictions together. -/
theorem numClasses_sum [Finite α] [Finite β] (s : Setoid (α ⊕ β))
    (h : ∀ a b, ¬ s (Sum.inl a) (Sum.inr b)) :
    numClasses s = numClasses (s.comap Sum.inl) + numClasses (s.comap Sum.inr) := by
  unfold numClasses
  rw [← Nat.card_sum]
  let f : α ⊕ β → Quotient (s.comap Sum.inl) ⊕ Quotient (s.comap Sum.inr) :=
    Sum.elim (fun a => Sum.inl (Quotient.mk _ a)) (fun b => Sum.inr (Quotient.mk _ b))
  have hf : ∀ x y, s x y → f x = f y := by
    rintro (a | b) (a' | b') hxy
    · exact congrArg Sum.inl (Quotient.sound hxy)
    · exact absurd hxy (h a b')
    · exact absurd (s.symm hxy) (h a' b)
    · exact congrArg Sum.inr (Quotient.sound hxy)
  refine Nat.card_congr (Equiv.ofBijective (Quotient.lift f hf) ⟨?_, ?_⟩)
  · intro p q hpq
    induction p using Quotient.inductionOn with
    | h x =>
    induction q using Quotient.inductionOn with
    | h y =>
    apply Quotient.sound
    rcases x with a | b <;> rcases y with a' | b'
    · have hpq' : f (Sum.inl a) = f (Sum.inl a') := hpq
      have h3 : Quotient.mk (s.comap Sum.inl) a = Quotient.mk _ a' := Sum.inl.inj hpq'
      have h4 := Quotient.exact h3
      exact h4
    · exact absurd hpq (by simp [f])
    · exact absurd hpq (by simp [f])
    · have hpq' : f (Sum.inr b) = f (Sum.inr b') := hpq
      have h3 : Quotient.mk (s.comap Sum.inr) b = Quotient.mk _ b' := Sum.inr.inj hpq'
      have h4 := Quotient.exact h3
      exact h4
  · rintro (q | q)
    · induction q using Quotient.inductionOn with
      | h a => exact ⟨Quotient.mk _ (Sum.inl a), rfl⟩
    · induction q using Quotient.inductionOn with
      | h b => exact ⟨Quotient.mk _ (Sum.inr b), rfl⟩

theorem sumCongr_pow (σ : Perm α) (τ : Perm β) (n : ℕ) :
    (Perm.sumCongr σ τ) ^ n = Perm.sumCongr (σ ^ n) (τ ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Perm.sumCongr_mul, pow_succ, pow_succ]

theorem sumCongr_zpow (σ : Perm α) (τ : Perm β) (i : ℤ) :
    (Perm.sumCongr σ τ) ^ i = Perm.sumCongr (σ ^ i) (τ ^ i) := by
  rcases i with n | n
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact sumCongr_pow σ τ n
  · simp only [zpow_negSucc]
    rw [sumCongr_pow, Perm.sumCongr_inv]

theorem sameCycle_sumCongr_inl {σ : Perm α} {τ : Perm β} {a b : α} :
    SameCycle (Perm.sumCongr σ τ) (Sum.inl a) (Sum.inl b) ↔ SameCycle σ a b := by
  constructor
  · rintro ⟨i, hi⟩
    rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl] at hi
    exact ⟨i, Sum.inl.inj hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl, hi]⟩

theorem sameCycle_sumCongr_inr {σ : Perm α} {τ : Perm β} {a b : β} :
    SameCycle (Perm.sumCongr σ τ) (Sum.inr a) (Sum.inr b) ↔ SameCycle τ a b := by
  constructor
  · rintro ⟨i, hi⟩
    rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inr] at hi
    exact ⟨i, Sum.inr.inj hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inr, hi]⟩

theorem not_sameCycle_sumCongr {σ : Perm α} {τ : Perm β} (a : α) (b : β) :
    ¬ SameCycle (Perm.sumCongr σ τ) (Sum.inl a) (Sum.inr b) := by
  rintro ⟨i, hi⟩
  rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl] at hi
  exact Sum.inl_ne_inr hi

/-- The side map from a sum to the components of the two summands. -/
def sumSideComp (σ α' : Perm α) (τ β' : Perm β) :
    α ⊕ β → Quotient (compSetoid σ α') ⊕ Quotient (compSetoid τ β') :=
  Sum.elim (fun a => Sum.inl (Quotient.mk _ a)) (fun b => Sum.inr (Quotient.mk _ b))

theorem sumSideComp_of_compSetoid {σ α' : Perm α} {τ β' : Perm β} {x y : α ⊕ β}
    (h : compSetoid (Perm.sumCongr σ τ) (Perm.sumCongr α' β') x y) :
    sumSideComp σ α' τ β' x = sumSideComp σ α' τ β' y := by
  have key := compSetoid_le (Setoid.ker (sumSideComp σ α' τ β'))
    (fun z => by
      rw [Setoid.ker_def]
      rcases z with a | b
      · exact congrArg Sum.inl (Quotient.sound (compSetoid_left σ α' a))
      · exact congrArg Sum.inr (Quotient.sound (compSetoid_left τ β' b)))
    (fun z => by
      rw [Setoid.ker_def]
      rcases z with a | b
      · exact congrArg Sum.inl (Quotient.sound (compSetoid_right σ α' a))
      · exact congrArg Sum.inr (Quotient.sound (compSetoid_right τ β' b))) h
  rwa [Setoid.ker_def] at key

theorem compSetoid_sumCongr_inl {σ α' : Perm α} {τ β' : Perm β} {a b : α} :
    compSetoid (Perm.sumCongr σ τ) (Perm.sumCongr α' β') (Sum.inl a) (Sum.inl b) ↔
      compSetoid σ α' a b := by
  constructor
  · intro h
    exact Quotient.exact (Sum.inl.inj (sumSideComp_of_compSetoid h))
  · intro h
    have key := compSetoid_le
      (Setoid.comap Sum.inl (compSetoid (Perm.sumCongr σ τ) (Perm.sumCongr α' β')))
      (fun z => by
        rw [Setoid.comap_rel]
        exact compSetoid_left (Perm.sumCongr σ τ) (Perm.sumCongr α' β') (Sum.inl z))
      (fun z => by
        rw [Setoid.comap_rel]
        exact compSetoid_right (Perm.sumCongr σ τ) (Perm.sumCongr α' β') (Sum.inl z)) h
    rwa [Setoid.comap_rel] at key

theorem compSetoid_sumCongr_inr {σ α' : Perm α} {τ β' : Perm β} {a b : β} :
    compSetoid (Perm.sumCongr σ τ) (Perm.sumCongr α' β') (Sum.inr a) (Sum.inr b) ↔
      compSetoid τ β' a b := by
  constructor
  · intro h
    exact Quotient.exact (Sum.inr.inj (sumSideComp_of_compSetoid h))
  · intro h
    have key := compSetoid_le
      (Setoid.comap Sum.inr (compSetoid (Perm.sumCongr σ τ) (Perm.sumCongr α' β')))
      (fun z => by
        rw [Setoid.comap_rel]
        exact compSetoid_left (Perm.sumCongr σ τ) (Perm.sumCongr α' β') (Sum.inr z))
      (fun z => by
        rw [Setoid.comap_rel]
        exact compSetoid_right (Perm.sumCongr σ τ) (Perm.sumCongr α' β') (Sum.inr z)) h
    rwa [Setoid.comap_rel] at key

theorem not_compSetoid_sumCongr {σ α' : Perm α} {τ β' : Perm β} (a : α) (b : β) :
    ¬ compSetoid (Perm.sumCongr σ τ) (Perm.sumCongr α' β') (Sum.inl a) (Sum.inr b) := fun h =>
  Sum.inl_ne_inr (sumSideComp_of_compSetoid h)

theorem cycleCount_sumCongr [Finite α] [Finite β] (σ : Perm α) (τ : Perm β) :
    cycleCount (Perm.sumCongr σ τ) = cycleCount σ + cycleCount τ := by
  unfold cycleCount
  rw [numClasses_sum _ (fun a b => not_sameCycle_sumCongr a b)]
  congr 1
  · exact numClasses_congr fun a b => by
      rw [Setoid.comap_rel]; exact sameCycle_sumCongr_inl
  · exact numClasses_congr fun a b => by
      rw [Setoid.comap_rel]; exact sameCycle_sumCongr_inr

theorem numComponents_sumCongr [Finite α] [Finite β] (σ α' : Perm α) (τ β' : Perm β) :
    numComponents (Perm.sumCongr σ τ) (Perm.sumCongr α' β') =
      numComponents σ α' + numComponents τ β' := by
  unfold numComponents
  rw [numClasses_sum _ (fun a b => not_compSetoid_sumCongr a b)]
  congr 1
  · exact numClasses_congr fun a b => by
      rw [Setoid.comap_rel]; exact compSetoid_sumCongr_inl
  · exact numClasses_congr fun a b => by
      rw [Setoid.comap_rel]; exact compSetoid_sumCongr_inr

/-- The Euler defect is additive on disjoint unions. -/
theorem eulerDefect_sumCongr [Finite α] [Finite β] (σ α' : Perm α) (τ β' : Perm β) :
    eulerDefect (Perm.sumCongr σ τ) (Perm.sumCongr α' β') =
      eulerDefect σ α' + eulerDefect τ β' := by
  unfold eulerDefect
  rw [Perm.sumCongr_mul, Nat.card_sum, numComponents_sumCongr, cycleCount_sumCongr,
    cycleCount_sumCongr, cycleCount_sumCongr]
  push_cast
  ring

end Sum

/-- If `φ ∘ f = f ∘ π` away from `z0`, then `f` of a point of the `π`-cycle of `z0` reaches
`f z0` under `φ`. -/
theorem sameCycle_of_agree_until {X Y : Type*} [Finite X] {π : Perm X} {φ : Perm Y} (f : X → Y)
    {z0 : X} (hf : ∀ z, z ≠ z0 → φ (f z) = f (π z)) {a : X} (ha : SameCycle π a z0) :
    SameCycle φ (f a) (f z0) := by
  classical
  have := Fintype.ofFinite X
  have hex : ∃ n : ℕ, (π ^ n) a = z0 := by
    obtain ⟨i, -, hi⟩ := ha.exists_pow_eq'
    exact ⟨i, hi⟩
  let n := Nat.find hex
  have hn : (π ^ n) a = z0 := Nat.find_spec hex
  have hmin : ∀ j < n, (π ^ j) a ≠ z0 := fun j hj => Nat.find_min hex hj
  have key : ∀ j ≤ n, (φ ^ j) (f a) = f ((π ^ j) a) := by
    intro j
    induction j with
    | zero => intro; simp
    | succ j ih =>
      intro hj
      rw [pow_succ', Perm.mul_apply, ih (by omega), hf _ (hmin j (by omega)), pow_succ',
        Perm.mul_apply]
  exact ⟨n, by rw [zpow_natCast, key n le_rfl, hn]⟩

theorem cycleCount_removeFromCycle {X : Type*} [DecidableEq X] [Finite X] {π : Perm X} {z : X}
    (hz : π z ≠ z) : cycleCount (removeFromCycle π z) = cycleCount π + 1 := by
  have hz' : π⁻¹ z ≠ z := fun h => hz (by
    have := congrArg π h
    simp only [perm_apply_inv_self] at this
    exact this.symm)
  exact cycleCount_mul_swap_of_sameCycle hz' (sameCycle_inv_apply_self π z)

theorem mulSwap_preserves {X β : Type*} [DecidableEq X] (F : X → β) {π : Perm X}
    (hF : ∀ w, F (π w) = F w) {a b : X} (hab : F a = F b) (w : X) :
    F ((π * swap a b) w) = F w := by
  rw [Perm.mul_apply, hF]
  by_cases hwa : w = a
  · rw [hwa, swap_apply_left, hab]
  by_cases hwb : w = b
  · rw [hwb, swap_apply_right, hab]
  rw [swap_apply_of_ne_of_ne hwa hwb]

/-- Inclusion–exclusion for two predicates on a finite type. -/
theorem natCard_or_add_and {X : Type*} [Finite X] (P Q : X → Prop) :
    Nat.card {x // P x ∨ Q x} + Nat.card {x // P x ∧ Q x} =
      Nat.card {x // P x} + Nat.card {x // Q x} := by
  classical
  have := Fintype.ofFinite X
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.filter_or, Finset.filter_and, Finset.card_union_add_card_inter]

end LeanPool.K5MinorFreeChoosability
