/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Tactic

/-!
# A trichotomy for cyclic words over `{X, Y, B}`

Positions are natural numbers read modulo a period `k`.  Each position carries an `x`-mark
(`px`), a `y`-mark (`py`) or both.  In Thomassen's proof of Kuratowski's theorem the positions
are the neighbours of a contracted vertex in rotation order, and the marks record adjacency to
the two ends `x`, `y` of the contracted edge.  `cyclic_trichotomy` shows that, if every window
of `k - 1` consecutive positions after any position contains an `x`-mark, then

* three positions carry both marks (giving `K₅`), or
* four positions alternate `y, x, y, x` (giving `K₃,₃`), or
* the word is *good*: the `y`-only positions form one run `s+1, …, s+ℓ`, all other positions carry
  an `x`-mark, and `y`-marks outside the run occur only at its two flanks `s + ℓ + 1` and
  `s + k`.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

theorem periodic_add_mul {P : ℕ → Prop} {k : ℕ} (hP : ∀ i, P (i + k) ↔ P i) (i m : ℕ) :
    P (i + k * m) ↔ P i := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, ← add_assoc, hP, ih]

/-- **Cyclic trichotomy.** -/
theorem cyclic_trichotomy (k : ℕ) (px py : ℕ → Prop)
    (hper : ∀ i, (px (i + k) ↔ px i) ∧ (py (i + k) ↔ py i)) (hcov : ∀ i, px i ∨ py i)
    (h2 : ∀ s, ∃ t, 1 ≤ t ∧ t < k ∧ px (s + t)) :
    (∃ a b c, a < b ∧ b < c ∧ c < a + k ∧ (px a ∧ py a) ∧ (px b ∧ py b) ∧ (px c ∧ py c)) ∨
    (∃ a b c d, a < b ∧ b < c ∧ c < d ∧ d < a + k ∧ py a ∧ px b ∧ py c ∧ px d) ∨
    (∃ s ℓ, ℓ + 1 < k ∧ (∀ t, 1 ≤ t → t ≤ ℓ → py (s + t) ∧ ¬ px (s + t)) ∧
      (∀ t, ℓ + 1 ≤ t → t ≤ k → px (s + t) ∧ (py (s + t) → t = ℓ + 1 ∨ t = k))) := by
  classical
  have hk : 2 ≤ k := by
    obtain ⟨t, h1, h2, -⟩ := h2 0
    omega
  have hpx : ∀ i, px (i + k) ↔ px i := fun i => (hper i).1
  have hpy : ∀ i, py (i + k) ↔ py i := fun i => (hper i).2
  by_cases hA : ∃ s, px s ∧ ¬ px (s + 1)
  · -- a maximal run of `y`-only positions starts at `s + 1`
    obtain ⟨s, hs, hs1⟩ := hA
    have hexℓ : ∃ ℓ, px (s + 1 + ℓ) := ⟨k - 1, by
      rw [show s + 1 + (k - 1) = s + k by omega, hpx]; exact hs⟩
    set ℓ := Nat.find hexℓ with hℓ
    have hℓspec : px (s + 1 + ℓ) := Nat.find_spec hexℓ
    have hℓmin : ∀ t, t < ℓ → ¬ px (s + 1 + t) := fun t ht => Nat.find_min hexℓ ht
    have hℓpos : 1 ≤ ℓ := by
      by_contra h
      have : ℓ = 0 := by omega
      rw [this, add_zero] at hℓspec
      exact hs1 hℓspec
    have hℓk : ℓ + 1 ≤ k := by
      by_contra h
      exact hℓmin (k - 1) (by omega) (by
        rw [show s + 1 + (k - 1) = s + k by omega, hpx]; exact hs)
    have hrun : ∀ t, 1 ≤ t → t ≤ ℓ → py (s + t) ∧ ¬ px (s + t) := by
      intro t ht1 htℓ
      have hn : ¬ px (s + t) := by
        have := hℓmin (t - 1) (by omega)
        rwa [show s + 1 + (t - 1) = s + t by omega] at this
      exact ⟨(hcov _).resolve_left hn, hn⟩
    have hlt : ℓ + 1 < k := by
      by_contra h
      have hℓk' : ℓ + 1 = k := by omega
      obtain ⟨t, ht1, htk, ht⟩ := h2 s
      exact (hrun t ht1 (by omega)).2 ht
    have hflank : px (s + (ℓ + 1)) := by rwa [show s + (ℓ + 1) = s + 1 + ℓ by omega]
    have hlast : px (s + k) := by rw [hpx]; exact hs
    by_cases hbad : ∃ t, ℓ + 1 < t ∧ t < k ∧ py (s + t)
    · obtain ⟨t, ht1, ht2, ht⟩ := hbad
      right; left
      exact ⟨s + 1, s + (ℓ + 1), s + t, s + k, by omega, by omega, by omega, by omega,
        (hrun 1 le_rfl hℓpos).1, hflank, ht, hlast⟩
    · push Not at hbad
      right; right
      refine ⟨s, ℓ, hlt, hrun, fun t ht1 ht2 => ⟨?_, fun hy => ?_⟩⟩
      · rcases Nat.eq_or_lt_of_le ht1 with h | h
        · rw [← h]; exact hflank
        rcases Nat.eq_or_lt_of_le ht2 with h' | h'
        · rw [h']; exact hlast
        exact (hcov _).resolve_right (hbad t h h')
      · by_contra hne
        push Not at hne
        exact hbad t (by omega) (by omega) hy
  · -- every position carries an `x`-mark
    push Not at hA
    obtain ⟨t0, -, -, ht0⟩ := h2 0
    have hfwd : ∀ n, px (t0 + n) := by
      intro n
      induction n with
      | zero => simpa using ht0
      | succ n ih => exact hA _ ih
    have hall : ∀ i, px i := by
      intro i
      have := hfwd (i + k * t0 - t0)
      rw [show t0 + (i + k * t0 - t0) = i + k * t0 by
        have : t0 ≤ k * t0 := Nat.le_mul_of_pos_left t0 (by omega)
        omega] at this
      exact (periodic_add_mul hpx i t0).1 this
    by_cases hY : ∃ b, py b
    · obtain ⟨b, hb⟩ := hY
      by_cases hW : ∃ j, 1 ≤ j ∧ j < k ∧ py (b + j)
      · set j₁ := Nat.find hW with hj₁
        obtain ⟨hj1, hjk, hjy⟩ := Nat.find_spec hW
        have hjmin : ∀ j, j < j₁ → ¬ (1 ≤ j ∧ j < k ∧ py (b + j)) := fun j hj =>
          Nat.find_min hW hj
        by_cases h3 : ∃ j, j₁ < j ∧ j < k ∧ py (b + j)
        · obtain ⟨j, hj1', hjk', hjy'⟩ := h3
          left
          exact ⟨b, b + j₁, b + j, by omega, by omega, by omega, ⟨hall _, hb⟩, ⟨hall _, hjy⟩,
            ⟨hall _, hjy'⟩⟩
        · push Not at h3
          have honly : ∀ j, 1 ≤ j → j < k → py (b + j) → j = j₁ := by
            intro j hj1' hjk' hjy'
            by_contra hne
            rcases Nat.lt_or_gt_of_ne hne with h | h
            · exact hjmin j h ⟨hj1', hjk', hjy'⟩
            · exact h3 j h hjk' hjy'
          by_cases hj₁1 : j₁ = 1
          · right; right
            refine ⟨b, 0, by omega, fun t ht1 ht2 => by omega, fun t ht1 ht2 => ⟨hall _, ?_⟩⟩
            intro hy
            rcases Nat.eq_or_lt_of_le ht2 with h | h
            · exact Or.inr h
            · exact Or.inl (by have := honly t ht1 h hy; omega)
          · by_cases hj₁k : j₁ = k - 1
            · right; right
              refine ⟨b + j₁, 0, by omega, fun t ht1 ht2 => by omega,
                fun t ht1 ht2 => ⟨hall _, ?_⟩⟩
              intro hy
              rcases Nat.eq_or_lt_of_le ht2 with h | h
              · exact Or.inr h
              · rcases Nat.eq_or_lt_of_le ht1 with h' | h'
                · exact Or.inl h'.symm
                · exfalso
                  have e : b + j₁ + t = b + (t - 1) + k := by omega
                  rw [e, hpy] at hy
                  have := honly (t - 1) (by omega) (by omega) hy
                  omega
            · right; left
              exact ⟨b, b + 1, b + j₁, b + j₁ + 1, by omega, by omega, by omega, by omega, hb,
                hall _, hjy, hall _⟩
      · push Not at hW
        right; right
        refine ⟨b, 0, by omega, fun t ht1 ht2 => by omega, fun t ht1 ht2 => ⟨hall _, ?_⟩⟩
        intro hy
        rcases Nat.eq_or_lt_of_le ht2 with h | h
        · exact Or.inr h
        · exact absurd hy (hW t ht1 h)
    · push Not at hY
      right; right
      exact ⟨0, 0, by omega, fun t ht1 ht2 => by omega,
        fun t _ _ => ⟨hall _, fun hy => absurd hy (hY _)⟩⟩

end LeanPool.K5MinorFreeChoosability
