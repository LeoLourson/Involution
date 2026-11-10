module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Complex.Basic

/-! # Возмущение определителя матрицы с двумя «взвешенными» строками (пакет G4)

Матрица `N(A, B, e)`: строки `0`, `1` — строки `A`, строки `2`, `3` — строки `B`, умноженные по
столбцам на `e`. Разложение определителя по перестановкам даёт в каждом слагаемом ровно два
множителя `e_c e_{c'}`, `c ≠ c'`; отсюда оценка возмущения (шаг 9 C24, формула (eq:eta1)). -/

@[expose] public noncomputable section

open Matrix

namespace Involution
namespace GeneralBC

/-- Матрица `N(A,B,e)`: строки `0`, `1` из `A`; строки `2`, `3` — строки `B` с множителем `e_c`
в столбце `c`. -/
def NmatW (A B : Matrix (Fin 4) (Fin 4) ℂ) (e : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i c => if (i : ℕ) < 2 then A i c else B i c * e c

/-- Слагаемое разложения без множителей `e`. -/
def PtermW (A B : Matrix (Fin 4) (Fin 4) ℂ) (σ : Equiv.Perm (Fin 4)) : ℂ :=
  A 0 (σ 0) * A 1 (σ 1) * (B 2 (σ 2) * B 3 (σ 3))

theorem det_NmatW (A B : Matrix (Fin 4) (Fin 4) ℂ) (e : Fin 4 → ℂ) :
    (NmatW A B e).det = ∑ σ : Equiv.Perm (Fin 4),
      ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * (PtermW A B σ * (e (σ 2) * e (σ 3))) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  simp [Fin.prod_univ_four, NmatW, PtermW, Matrix.transpose_apply]
  ring

theorem prod_sub_le {x y : Fin 4 → ℂ} {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hy : ∀ i, ‖y i‖ ≤ B) (hxy : ∀ i, ‖x i - y i‖ ≤ δ) :
    ‖x 0 * x 1 * (x 2 * x 3) - y 0 * y 1 * (y 2 * y 3)‖ ≤ 4 * (B + 1) ^ 3 * δ := by
  have hx : ∀ i, ‖x i‖ ≤ B + 1 := fun i => by
    have h2 := hxy i
    have h3 := hy i
    calc ‖x i‖ = ‖(x i - y i) + y i‖ := by ring_nf
      _ ≤ ‖x i - y i‖ + ‖y i‖ := norm_add_le _ _
      _ ≤ B + 1 := by linarith
  have e : x 0 * x 1 * (x 2 * x 3) - y 0 * y 1 * (y 2 * y 3) =
      (x 0 - y 0) * (x 1 * (x 2 * x 3)) + y 0 * ((x 1 - y 1) * (x 2 * x 3))
        + y 0 * y 1 * ((x 2 - y 2) * x 3) + y 0 * y 1 * (y 2 * (x 3 - y 3)) := by ring
  rw [e]
  have hB1 : 0 ≤ B + 1 := by linarith
  have t1 : ‖(x 0 - y 0) * (x 1 * (x 2 * x 3))‖ ≤ δ * (B + 1) ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul]
    calc _ ≤ δ * ((B + 1) * ((B + 1) * (B + 1))) := by
          gcongr
          · exact hxy 0
          · exact hx 1
          · exact hx 2
          · exact hx 3
      _ = _ := by ring
  have t2 : ‖y 0 * ((x 1 - y 1) * (x 2 * x 3))‖ ≤ δ * (B + 1) ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul]
    calc _ ≤ (B + 1) * (δ * ((B + 1) * (B + 1))) := by
          gcongr
          · exact (hy 0).trans (by linarith)
          · exact hxy 1
          · exact hx 2
          · exact hx 3
      _ = _ := by ring
  have t3 : ‖y 0 * y 1 * ((x 2 - y 2) * x 3)‖ ≤ δ * (B + 1) ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul]
    calc _ ≤ (B + 1) * (B + 1) * (δ * (B + 1)) := by
          gcongr
          · exact (hy 0).trans (by linarith)
          · exact (hy 1).trans (by linarith)
          · exact hxy 2
          · exact hx 3
      _ = _ := by ring
  have t4 : ‖y 0 * y 1 * (y 2 * (x 3 - y 3))‖ ≤ δ * (B + 1) ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul]
    calc _ ≤ (B + 1) * (B + 1) * ((B + 1) * δ) := by
          gcongr
          · exact (hy 0).trans (by linarith)
          · exact (hy 1).trans (by linarith)
          · exact (hy 2).trans (by linarith)
          · exact hxy 3
      _ = _ := by ring
  calc _ ≤ ‖(x 0 - y 0) * (x 1 * (x 2 * x 3))‖ + ‖y 0 * ((x 1 - y 1) * (x 2 * x 3))‖
        + ‖y 0 * y 1 * ((x 2 - y 2) * x 3)‖ + ‖y 0 * y 1 * (y 2 * (x 3 - y 3))‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 4 * (B + 1) ^ 3 * δ := by nlinarith

/-- Оценка возмущения: если элементы `A₀`, `B₀` ограничены числом `B`, элементы `A`, `B'`
отличаются от них не более чем на `δ ≤ 1`, а `‖e_c e_{c'}‖ ≤ Eb` при `c ≠ c'`, то
`‖det N(A,B',e) − det N(A₀,B₀,e)‖ ≤ 96 (B+1)³ δ Eb`. -/
theorem det_NmatW_sub_le {A B' A₀ B₀ : Matrix (Fin 4) (Fin 4) ℂ} {e : Fin 4 → ℂ}
    {Bd δ Eb : ℝ} (hBd : 0 ≤ Bd) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (he : ∀ c c', c ≠ c' → ‖e c * e c'‖ ≤ Eb)
    (hA₀ : ∀ i c, ‖A₀ i c‖ ≤ Bd) (hB₀ : ∀ i c, ‖B₀ i c‖ ≤ Bd)
    (hA : ∀ i c, ‖A i c - A₀ i c‖ ≤ δ) (hB : ∀ i c, ‖B' i c - B₀ i c‖ ≤ δ) :
    ‖(NmatW A B' e).det - (NmatW A₀ B₀ e).det‖ ≤ 96 * (Bd + 1) ^ 3 * δ * Eb := by
  rw [det_NmatW, det_NmatW, ← Finset.sum_sub_distrib]
  have hterm : ∀ σ : Equiv.Perm (Fin 4),
      ‖((Equiv.Perm.sign σ : ℤˣ) : ℂ) * (PtermW A B' σ * (e (σ 2) * e (σ 3))) -
        ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * (PtermW A₀ B₀ σ * (e (σ 2) * e (σ 3)))‖
        ≤ 4 * (Bd + 1) ^ 3 * δ * Eb := by
    intro σ
    have hs : ‖((Equiv.Perm.sign σ : ℤˣ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    have hne : σ 2 ≠ σ 3 := fun h => by
      have := σ.injective h
      simp at this
    have hp := prod_sub_le (x := ![A 0 (σ 0), A 1 (σ 1), B' 2 (σ 2), B' 3 (σ 3)])
      (y := ![A₀ 0 (σ 0), A₀ 1 (σ 1), B₀ 2 (σ 2), B₀ 3 (σ 3)]) hBd hδ hδ1
      (fun i => by fin_cases i <;> simp [hA₀, hB₀]) (fun i => by fin_cases i <;> simp [hA, hB])
    rw [← mul_sub, ← sub_mul, norm_mul, norm_mul, hs, one_mul]
    have hp' : ‖PtermW A B' σ - PtermW A₀ B₀ σ‖ ≤ 4 * (Bd + 1) ^ 3 * δ := by
      simpa [PtermW] using hp
    exact mul_le_mul hp' (he _ _ hne) (norm_nonneg _) (by positivity)
  calc _ ≤ ∑ σ : Equiv.Perm (Fin 4), 4 * (Bd + 1) ^ 3 * δ * Eb :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => hterm σ)
    _ = 96 * (Bd + 1) ^ 3 * δ * Eb := by
        simp [Finset.sum_const, Fintype.card_perm]
        norm_num [Nat.factorial]
        ring

/-- Оценка возмущения определителя: `‖det M − det N‖ ≤ 96 (B+1)³ δ`. -/
theorem det_sub_le {M N : Matrix (Fin 4) (Fin 4) ℂ} {Bd δ : ℝ} (hBd : 0 ≤ Bd) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hN : ∀ i j, ‖N i j‖ ≤ Bd) (hM : ∀ i j, ‖M i j - N i j‖ ≤ δ) :
    ‖M.det - N.det‖ ≤ 96 * (Bd + 1) ^ 3 * δ := by
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  have hterm : ∀ σ : Equiv.Perm (Fin 4),
      ‖((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ∏ i, M (σ i) i -
        ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ∏ i, N (σ i) i‖ ≤ 4 * (Bd + 1) ^ 3 * δ := by
    intro σ
    have hs : ‖((Equiv.Perm.sign σ : ℤˣ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    have hp := prod_sub_le (x := fun i => M (σ i) i) (y := fun i => N (σ i) i) hBd hδ hδ1
      (fun i => hN _ _) (fun i => hM _ _)
    rw [← mul_sub, norm_mul, hs, one_mul]
    simpa [Fin.prod_univ_four, mul_assoc] using hp
  calc _ ≤ ∑ σ : Equiv.Perm (Fin 4), 4 * (Bd + 1) ^ 3 * δ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => hterm σ)
    _ = 96 * (Bd + 1) ^ 3 * δ := by
        simp [Finset.sum_const, Fintype.card_perm]
        norm_num [Nat.factorial]
        ring

end GeneralBC
end Involution

end
