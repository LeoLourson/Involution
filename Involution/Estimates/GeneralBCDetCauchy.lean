module

public import Involution.Folding.GeneralBCFold
public import Involution.Folding.GeneralBCIntegrable
public import Involution.Folding.GeneralBCAsymptoticCoeffTransfer
public import Involution.Folding.GeneralBCFoldForward

/-! # Тождество (eq:detU) (пакет G4, лемма `lem:det`, C24 шаги 7, 9)

Решение `Y' = ρ K Y` в интегральной форме (`IsSol`) выражается через матрицу Коши:
`Y(x) = S_ρ Φ(x, ρ²) S_ρ⁻¹ Y(0)`, `S_ρ = diag(1,1,ρ⁻¹,ρ⁻¹)`. Отсюда
`det(Λ_ρ V₀ S_ρ⁻¹ Y(0) + Λ_ρ V₁ S_ρ⁻¹ Y(1)) = ρ^{1-κ₁-κ₂} Δ(ρ²) det Y(0)`;
нормировка строк `Λ_ρ V_j S_ρ⁻¹` вычисляется явно: `V₀` и `V1a + ρ⁻¹ V1b`. -/

@[expose] public noncomputable section

open MeasureTheory Set Matrix

namespace Involution
namespace GeneralBC

/-- `S_ρ⁻¹ = diag(1,1,ρ,ρ)`. -/
def Sinv (ρ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, 1, ρ, ρ]

/-- `S_ρ = diag(1,1,ρ⁻¹,ρ⁻¹)`. -/
def Smat (ρ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, 1, ρ⁻¹, ρ⁻¹]

theorem Smat_mul_Sinv {ρ : ℂ} (hρ : ρ ≠ 0) : Smat ρ * Sinv ρ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Smat, Sinv, hρ]

theorem Sinv_mul_Smat {ρ : ℂ} (hρ : ρ ≠ 0) : Sinv ρ * Smat ρ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Smat, Sinv, hρ]

theorem det_Sinv (ρ : ℂ) : (Sinv ρ).det = ρ ^ 2 := by
  simp [Sinv, Matrix.det_diagonal, Fin.prod_univ_four]; ring

/-- Сопряжение: `(A₀ + ρ² A₁) S⁻¹ = ρ S⁻¹ K`. -/
theorem fold_conj (a : ℝ → ℝ) (x : ℝ) (ρ : ℂ) :
    (foldA0 x + ρ ^ 2 • foldA1 a x) * Sinv ρ = ρ • (Sinv ρ * Kmat a x) := by
  rw [← foldA0_add_foldA1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [foldA0, foldA1, Sinv, Matrix.diagonal_apply, Matrix.mul_apply] <;>
    ring

theorem Sinv_mul_apply (ρ : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    (Sinv ρ * M) i j = (![1, 1, ρ, ρ] : Fin 4 → ℂ) i * M i j := by
  simp [Sinv, Matrix.diagonal_mul]

theorem isSol_continuousOn {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {ρ : ℂ}
    {Y : ℝ → Matrix (Fin 4) (Fin 4) ℂ} (hY : IsSol a ρ Y) (i j : Fin 4) :
    ContinuousOn (fun x => Y x i j) (Icc 0 1) := by
  have hK : ∀ i j, IntervalIntegrable (fun x => Kmat a x i j) volume 0 1 := fun i j =>
    (h.continuousOn_Kmat i j).intervalIntegrable_of_Icc zero_le_one
  have hI := isSol_integrable hK hY i j
  have hc := intervalIntegral.continuousOn_primitive_interval' hI
    (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
  rw [uIcc_of_le zero_le_one] at hc
  refine (hc.const_add (Y 0 i j)).congr (fun x hx => ?_)
  exact hY x hx i j

theorem Ycol_continuousOn {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {ρ : ℂ}
    {Y : ℝ → Matrix (Fin 4) (Fin 4) ℂ} (hY : IsSol a ρ Y) (j : Fin 4) :
    ContinuousOn (fun x => fun i => (Sinv ρ * Y x) i j) (Icc 0 1) := by
  refine continuousOn_pi.2 fun i => ?_
  simp only [Sinv_mul_apply]
  exact continuousOn_const.mul (isSol_continuousOn h hY i j)

theorem mulVec_col {a : ℝ → ℝ} (t : ℝ) (ρ : ℂ) (Y : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    ((foldA0 t + ρ ^ 2 • foldA1 a t) *ᵥ fun i => (Sinv ρ * Y) i j) i
      = (![1, 1, ρ, ρ] : Fin 4 → ℂ) i * (ρ • (Kmat a t * Y)) i j := by
  have e : ((foldA0 t + ρ ^ 2 • foldA1 a t) *ᵥ fun i => (Sinv ρ * Y) i j) i =
      ((foldA0 t + ρ ^ 2 • foldA1 a t) * (Sinv ρ * Y)) i j := rfl
  rw [e, ← Matrix.mul_assoc, fold_conj, Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_assoc,
    Sinv_mul_apply, smul_eq_mul, Matrix.smul_apply, smul_eq_mul]
  ring

/-- `Y(1) = S_ρ Φ(1, ρ²) S_ρ⁻¹ Y(0)` для решения `Y' = ρ K Y`, `ρ ≠ 0`. -/
theorem isSol_eq_cauchy {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {ρ : ℂ} (hρ : ρ ≠ 0)
    {Y : ℝ → Matrix (Fin 4) (Fin 4) ℂ} (hY : IsSol a ρ Y) :
    Y 1 = Smat ρ * foldPhi a 1 (ρ ^ 2) * Sinv ρ * Y 0 := by
  have hK : ∀ i j, IntervalIntegrable (fun x => Kmat a x i j) volume 0 1 := fun i j =>
    (h.continuousOn_Kmat i j).intervalIntegrable_of_Icc zero_le_one
  have hI := isSol_integrable hK hY
  have hA1 : ContinuousOn (foldA1 a) (Icc 0 1) := foldA1_continuousOn ⟨m, κ, h⟩
  have hB : ContinuousOn (fun t => foldA0 t + ρ ^ 2 • foldA1 a t) (Icc 0 1) :=
    continuousOn_const.add (hA1.const_smul (ρ ^ 2))
  have key : Sinv ρ * Y 1 = foldPhi a 1 (ρ ^ 2) * (Sinv ρ * Y 0) := by
    ext i j
    have hu := linearCauchy_unique (A₀ := foldA0) (A₁ := foldA1 a) continuousOn_const hA1 (ρ ^ 2)
      (X := fun x => fun i => (Sinv ρ * Y x) i j) (Ycol_continuousOn h hY j) (by
        intro x hx
        have hint : IntervalIntegrable
            (fun t => (foldA0 t + ρ ^ 2 • foldA1 a t) *ᵥ fun i => (Sinv ρ * Y t) i j) volume 0 x :=
          (LinearCauchy.continuousOn_mulVec hB (Ycol_continuousOn h hY j)).mono
            (by rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2) |>.intervalIntegrable
        ext i
        rw [Pi.add_apply, integral_apply_pi hint]
        simp only [mulVec_col]
        rw [intervalIntegral.integral_const_mul]
        have h1 := hY x hx i j
        have h2 : ∫ t in (0 : ℝ)..x, (ρ • (Kmat a t * Y t)) i j = Y x i j - Y 0 i j := by
          rw [h1]; ring
        rw [h2]
        simp only [Sinv_mul_apply]
        ring) 1 ⟨zero_le_one, le_rfl⟩
    exact congrFun hu i
  have hS := Smat_mul_Sinv hρ
  calc Y 1 = (Smat ρ * Sinv ρ) * Y 1 := by rw [hS, one_mul]
    _ = Smat ρ * (Sinv ρ * Y 1) := by rw [Matrix.mul_assoc]
    _ = _ := by rw [key]; simp only [Matrix.mul_assoc]

/-! ## Нормировка строк и определитель -/

/-- Строка `U¹_j = (β_{j0}, α_{j0}, 0, 0)` при `κ_j = 1`, нуль при `κ_j = 0`. -/
def U1row (U : Forms) (j : Fin 2) : Fin 4 → ℂ := by
  classical
  exact if U.HasDeriv j then ![U.β j 0, U.α j 0, 0, 0] else 0

/-- Матрица строк `U⁰_j` (строки `2`, `3`; строки `0`, `1` нулевые). -/
def V1a (U : Forms) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![0, 0, U0row U 0, U0row U 1]

/-- Матрица строк `U¹_j` (строки `2`, `3`; строки `0`, `1` нулевые). -/
def V1b (U : Forms) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![0, 0, U1row U 0, U1row U 1]

/-- `Λ_ρ = diag(1, ρ⁻¹, ρ^{-κ₁}, ρ^{-κ₂})`. -/
def Lrho (U : Forms) (ρ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, ρ⁻¹, (ρ⁻¹) ^ U.ord 0, (ρ⁻¹) ^ U.ord 1]

theorem det_Lrho (U : Forms) (ρ : ℂ) :
    (Lrho U ρ).det = ρ⁻¹ * ((ρ⁻¹) ^ U.ord 0 * (ρ⁻¹) ^ U.ord 1) := by
  simp [Lrho, Matrix.det_diagonal, Fin.prod_univ_four, mul_assoc]

theorem Lrho_V0_Sinv {ρ : ℂ} (hρ : ρ ≠ 0) (U : Forms) :
    Lrho U ρ * foldV0 * Sinv ρ = foldV0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lrho, foldV0, Sinv, Matrix.diagonal_mul, Matrix.mul_diagonal, hρ]

theorem Lrho_V1_Sinv {ρ : ℂ} (hρ : ρ ≠ 0) (U : Forms) :
    Lrho U ρ * foldV1 U * Sinv ρ = V1a U + ρ⁻¹ • V1b U := by
  have key : ∀ j : Fin 2, ∀ c : Fin 4,
      ((ρ⁻¹) ^ U.ord j * (![U.β j 0, U.α j 0, U.β j 1, -U.α j 1] c *
        (![1, 1, ρ, ρ] : Fin 4 → ℂ) c))
      = U0row U j c + ρ⁻¹ * U1row U j c := by
    intro j c
    by_cases hd : U.HasDeriv j
    · have ho : U.ord j = 1 := by simp [Forms.ord, hd]
      simp only [U0row, U1row, hd, ho, ite_true]
      fin_cases c <;> simp <;> field_simp
    · have ho : U.ord j = 0 := by simp [Forms.ord, hd]
      have h1 : U.α j 1 = 0 := by
        by_contra h'; exact hd (Or.inl h')
      have h2 : U.β j 1 = 0 := by
        by_contra h'; exact hd (Or.inr h')
      simp only [U0row, U1row, hd, ho, ite_false]
      fin_cases c <;> simp [h1, h2]
  ext i c
  fin_cases i
  · simp [Lrho, foldV1, V1a, V1b, Sinv, Matrix.diagonal_mul, Matrix.mul_diagonal]
  · simp [Lrho, foldV1, V1a, V1b, Sinv, Matrix.diagonal_mul, Matrix.mul_diagonal]
  · simp only [Lrho, foldV1, V1a, V1b, Sinv, Matrix.diagonal_mul, Matrix.mul_diagonal]
    simpa [mul_assoc] using key 0 c
  · simp only [Lrho, foldV1, V1a, V1b, Sinv, Matrix.diagonal_mul, Matrix.mul_diagonal]
    simpa [mul_assoc] using key 1 c

/-- Матрица условий в переменных `Y`: `𝔘_a(ρ) = V₀ Y(0) + (V1a + ρ⁻¹ V1b) Y(1)`. -/
def UA (U : Forms) (ρ : ℂ) (Y : ℝ → Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  foldV0 * Y 0 + (V1a U + ρ⁻¹ • V1b U) * Y 1

/-- Формула (eq:detU), первая часть: `𝔘_a = Λ_ρ (V₀ + V₁ Φ(1,ρ²)) S_ρ⁻¹ Y(0)`. -/
theorem UA_eq {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms) {ρ : ℂ} (hρ : ρ ≠ 0)
    {Y : ℝ → Matrix (Fin 4) (Fin 4) ℂ} (hY : IsSol a ρ Y) :
    UA U ρ Y = Lrho U ρ * foldMat a U (ρ ^ 2) * Sinv ρ * Y 0 := by
  have h1 := isSol_eq_cauchy h hρ hY
  have hSS := Sinv_mul_Smat hρ
  have e1 := Lrho_V0_Sinv hρ U
  have e2 := Lrho_V1_Sinv hρ U
  unfold UA
  rw [← e1, ← e2, h1]
  unfold foldMat
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  congr 2
  rw [← Matrix.mul_assoc (Sinv ρ), hSS, Matrix.one_mul]

/-- Формула (eq:detU), вторая часть: `det 𝔘_a = ρ^{1-κ₁-κ₂} Δ(ρ²) det Y(0)`. -/
theorem det_UA {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms) {ρ : ℂ} (hρ : ρ ≠ 0)
    {Y : ℝ → Matrix (Fin 4) (Fin 4) ℂ} (hY : IsSol a ρ Y) :
    (UA U ρ Y).det = ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) * (Y 0).det := by
  rw [UA_eq h U hρ hY]
  simp only [Matrix.det_mul, det_Lrho, det_Sinv, Delta]
  have : ρ ^ (1 - (kappaSum U : ℤ)) = ρ⁻¹ * ((ρ⁻¹) ^ U.ord 0 * (ρ⁻¹) ^ U.ord 1) * ρ ^ 2 := by
    rw [zpow_sub₀ hρ, zpow_one, zpow_natCast, kappaSum, pow_add, inv_pow, inv_pow]
    field_simp
  rw [this]
  ring

end GeneralBC
end Involution

end
