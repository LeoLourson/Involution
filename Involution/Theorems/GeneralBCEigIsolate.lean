module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Изоляция кластеров конечного множества (пакет G6, thm:eig (b))

Для конечного `A ⊂ ℂ` из не более чем `K` точек среди масштабов `ε / 4^i`, `i ≤ K²`, найдётся
такой, что ни одна пара различных точек `A` не лежит на расстоянии из кольца
`[ε/4^{i+1}, ε/4^i)`. -/

@[expose] public noncomputable section

namespace Involution
namespace GeneralBC

theorem exists_isolating_scale (A : Finset ℂ) (K : ℕ) (hA : A.card ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ i : ℕ, i ≤ K * K ∧ ∀ a ∈ A, ∀ a' ∈ A,
      ¬ (ε / 4 ^ (i + 1) ≤ ‖a - a'‖ ∧ ‖a - a'‖ < ε / 4 ^ i) := by
  by_contra hcon
  push Not at hcon
  choose a ha a' ha' hb using hcon
  -- пары `(a i, a' i)` при `i ≤ K*K` попарно различны
  let f : ℕ → ℂ × ℂ := fun i => if h : i ≤ K * K then (a i h, a' i h) else (0, 0)
  have hmaps : ∀ i ∈ Finset.range (K * K + 1), f i ∈ A ×ˢ A := by
    intro i hi
    have hi' : i ≤ K * K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    simp only [f, hi', ↓reduceDIte, Finset.mem_product]
    exact ⟨ha i hi', ha' i hi'⟩
  have hinj : Set.InjOn f ↑(Finset.range (K * K + 1)) := by
    have key : ∀ i j (hi : i ≤ K * K) (hj : j ≤ K * K), i < j →
        (a i hi, a' i hi) ≠ (a j hj, a' j hj) := by
      intro i j hi hj hij heq
      have e1 : a i hi = a j hj := congrArg Prod.fst heq
      have e2 : a' i hi = a' j hj := congrArg Prod.snd heq
      obtain ⟨h1, h2⟩ := hb i hi
      obtain ⟨h3, h4⟩ := hb j hj
      rw [e1, e2] at h1 h2
      have hpow : (4 : ℝ) ^ (i + 1) ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) hij
      have : ε / 4 ^ j ≤ ε / 4 ^ (i + 1) :=
        div_le_div_of_nonneg_left hε.le (by positivity) hpow
      linarith
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have hi' : i ≤ K * K := Nat.lt_succ_iff.1 hi
    have hj' : j ≤ K * K := Nat.lt_succ_iff.1 hj
    simp only [f, hi', ↓reduceDIte, hj', ↓reduceDIte] at hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i j hi' hj' h hij
    · exact key j i hj' hi' h hij.symm
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_range, Finset.card_product] at hcard
  have : A.card * A.card ≤ K * K := Nat.mul_le_mul hA hA
  omega

end GeneralBC
end Involution
