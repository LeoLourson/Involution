module

public import Mathlib.Order.Nat
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Find

/-! # Масштабы по слоям (пакет G6, thm:eig (b))

Для функции порогов `Tf` найдутся число `N` и невозрастающая последовательность масштабов
`e n ∈ (0, ε₁]`, стремящаяся к нулю, с `Tf (e n) ≤ N + n`. -/

@[expose] public noncomputable section

namespace Involution
namespace GeneralBC

theorem exists_levels (Tf : ℝ → ℝ) {ε₁ : ℝ} (hε₁ : 0 < ε₁) (B : ℝ) :
    ∃ (N : ℝ) (e : ℕ → ℝ), B ≤ N ∧ (∀ n, 0 < e n ∧ e n ≤ ε₁) ∧ Antitone e ∧
      (∀ ε' > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, e n < ε') ∧ ∀ n : ℕ, Tf (e n) ≤ N + n := by
  classical
  set c : ℕ → ℝ := fun p => ε₁ / 2 ^ p with hc
  have hcpos : ∀ p, 0 < c p := fun p => by simp only [hc]; positivity
  have hcanti : Antitone c := by
    intro p q hpq
    simp only [hc]
    exact div_le_div_of_nonneg_left hε₁.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) hpq)
  set Tm : ℕ → ℝ := fun q => (Finset.range (q + 1)).sup' ⟨0, by simp⟩ (fun p => Tf (c p)) with hTm
  have hTm_ge : ∀ p q, p ≤ q → Tf (c p) ≤ Tm q := fun p q h =>
    Finset.le_sup' (fun p => Tf (c p)) (Finset.mem_range.2 (Nat.lt_succ_of_le h))
  set N : ℝ := max B (Tm 0) with hN
  have hP0 : ∀ n : ℕ, Tm 0 ≤ N + n := fun n => by
    have := le_max_right B (Tm 0)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set qf : ℕ → ℕ := fun n => Nat.findGreatest (fun q => Tm q ≤ N + n) n with hqf
  have hqspec : ∀ n, Tm (qf n) ≤ N + n := fun n =>
    Nat.findGreatest_spec (P := fun q => Tm q ≤ N + n) (Nat.zero_le n) (hP0 n)
  have hqmono : Monotone qf := by
    intro m n hmn
    refine Nat.findGreatest_mono (fun q hq => ?_) hmn
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  refine ⟨N, fun n => c (qf n), le_max_left _ _, fun n => ⟨hcpos _, ?_⟩, ?_, ?_, ?_⟩
  · simp only [hc]
    exact div_le_self hε₁.le (one_le_pow₀ (by norm_num))
  · intro m n hmn
    exact hcanti (hqmono hmn)
  · intro ε' hε'
    obtain ⟨Q, hQ⟩ := exists_pow_lt_of_lt_one (show 0 < ε' / ε₁ by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have hQ' : c Q < ε' := by
      have h1 : c Q = ε₁ * (1 / 2) ^ Q := by
        simp [hc, div_eq_mul_inv, inv_pow]
      rw [h1]
      calc ε₁ * (1 / 2) ^ Q < ε₁ * (ε' / ε₁) := mul_lt_mul_of_pos_left hQ hε₁
        _ = ε' := by field_simp
    refine ⟨max Q ⌈Tm Q - N⌉₊, fun n hn => ?_⟩
    have hn1 : Q ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : Tm Q - N ≤ n :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hn)
    have : Q ≤ qf n := Nat.le_findGreatest (P := fun q => Tm q ≤ N + n) hn1 (by linarith)
    exact lt_of_le_of_lt (hcanti this) hQ'
  · intro n
    exact le_trans (hTm_ge _ _ le_rfl) (hqspec n)

end GeneralBC
end Involution
