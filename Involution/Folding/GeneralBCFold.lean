module

public import Involution.Folding.GeneralBCSystem
public import Involution.Setup.LinearCauchyUnique

/-! # Складывание: характеристический определитель `Δ` (лемма `lem:fold`, C24 шаги 2–3)

Система `X' = (A₀ + λ A₁) X`, `X = (w, w')`, `w(x) = (y(x), y(-x))`, с
`A₀ = [[0, I], [0, 0]]`, `A₁(x) = [[0, 0], [-M⁻¹(x), 0]]`, так что `A₀ + A₁(x) = K(x)`
(`Kmat`); матрицы `V₀`, `V₁` из статьи; `Δ(λ) = det (V₀ + V₁ Φ(1, λ))`, `Φ = linearCauchy`.
Здесь определения, непрерывность коэффициентов и целость `Δ`. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution
namespace GeneralBC

/-- `M⁻¹`-множитель `1/(1 - a(x)a(-x))` как комплексное число (как в `Kmat`). -/
def qfun (a : ℝ → ℝ) (x : ℝ) : ℂ := ((1 - a x * a (-x))⁻¹ : ℝ)

/-- Постоянная часть `A₀ = [[0, I], [0, 0]]`. -/
def foldA0 (_x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]]

/-- Коэффициент при `λ`: `A₁(x) = [[0, 0], [-M⁻¹(x), 0]]`. -/
def foldA1 (a : ℝ → ℝ) (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![0, 0, 0, 0], ![0, 0, 0, 0],
    ![-qfun a x, qfun a x * (a x : ℂ), 0, 0], ![qfun a x * (a (-x) : ℂ), -qfun a x, 0, 0]]

/-- Матрица Коши `Φ(x, λ)` системы `X' = (A₀ + λ A₁) X`, `Φ(0, λ) = I`. -/
def foldPhi (a : ℝ → ℝ) (x : ℝ) (lam : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  linearCauchy foldA0 (foldA1 a) x lam

/-- Строки `V₀`: условия склейки `w₁(0) = w₂(0)`, `w₁'(0) + w₂'(0) = 0`. -/
def foldV0 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![1, -1, 0, 0], ![0, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]]

/-- Строки `V₁`: формы `U_j` через `w(1)`: `(β_{j0}, α_{j0}, β_{j1}, -α_{j1})`. -/
def foldV1 (U : Forms) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![0, 0,
    ![U.β 0 0, U.α 0 0, U.β 0 1, -U.α 0 1], ![U.β 1 0, U.α 1 0, U.β 1 1, -U.α 1 1]]

/-- Матрица `V₀ + V₁ Φ(1, λ)`. -/
def foldMat (a : ℝ → ℝ) (U : Forms) (lam : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  foldV0 + foldV1 U * foldPhi a 1 lam

/-- Характеристический определитель `Δ(λ) = det (V₀ + V₁ Φ(1, λ))`. -/
def Delta (a : ℝ → ℝ) (U : Forms) (lam : ℂ) : ℂ := (foldMat a U lam).det

theorem foldA0_add_foldA1 (a : ℝ → ℝ) (x : ℝ) : foldA0 x + foldA1 a x = Kmat a x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [foldA0, foldA1, Kmat, qfun]

/-- `Δ` — целая функция. Доказана без (H); вне (H) относится к формальной матрице Коши с
нулевым `A₁`, смысл характеристического определителя задачи имеет только при (H). -/
theorem Delta_differentiable (a : ℝ → ℝ) (U : Forms) : Differentiable ℂ (Delta a U) := by
  unfold Delta foldMat
  simp only [Matrix.det_apply']
  refine Differentiable.fun_sum (fun σ _ => ?_)
  refine Differentiable.const_mul ?_ _
  refine Differentiable.fun_finsetProd (fun k _ => ?_)
  simp only [Matrix.add_apply, Matrix.mul_apply]
  refine Differentiable.const_add _ (Differentiable.fun_sum (fun j _ => ?_))
  exact (differentiable_linearCauchy _ _ _ _ _).const_mul _

theorem foldA0_continuous : Continuous foldA0 := continuous_const

/-- Непрерывность `A₁` на `[0,1]` при (H). -/
theorem foldA1_continuousOn {a : ℝ → ℝ} (h : Hyp a) : ContinuousOn (foldA1 a) (Icc 0 1) := by
  obtain ⟨m, κ, hh⟩ := h
  have hac : ContinuousOn a (Icc (-1) 1) := hh.ac.continuousOn.mono (by
    rw [uIcc_of_le (by norm_num)])
  have ha1 : ContinuousOn a (Icc 0 1) := hac.mono (Icc_subset_Icc (by norm_num) le_rfl)
  have ha2 : ContinuousOn (fun x => a (-x)) (Icc 0 1) :=
    hac.comp continuous_neg.continuousOn (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have hq : ContinuousOn (qfun a) (Icc 0 1) := by
    unfold qfun
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.inv₀ (continuousOn_const.sub (ha1.mul ha2)) (fun x hx => ?_)
    have := hh.upper x ⟨by linarith [hx.1], hx.2⟩
    have := hh.kappa_lt
    linarith
  have hA1 : ContinuousOn (fun x => (a x : ℂ)) (Icc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn ha1
  have hA2 : ContinuousOn (fun x => (a (-x) : ℂ)) (Icc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn ha2
  unfold foldA1
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.reduceFinMk, Matrix.of_apply, Fin.isValue, Matrix.cons_val', Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.zero_eta, Matrix.cons_val_zero,
      Matrix.cons_val_two] <;>
    first | exact continuousOn_const | exact hq.neg | exact hq.mul hA1 | exact hq.mul hA2

end GeneralBC
end Involution
