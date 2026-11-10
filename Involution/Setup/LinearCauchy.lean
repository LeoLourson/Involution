module

public import Involution.Setup.LinearCauchySeries
public import Mathlib.Analysis.Matrix.Normed

/-! Матрица Коши `Φ(x, λ)` линейной системы `X' = (A₀(x) + λ A₁(x)) X`, `Φ(0, λ) = I`,
с непрерывными на `[0,1]` коэффициентами: построение рядом Пикара. Утверждения
о `Φ` записаны поэлементно, без нормы на матрицах. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator

namespace Involution

variable {n : ℕ}

/-- Непрерывные отображения `[0,1] → Mat` с топологией нормы `ℓ∞`-оператора (она
совпадает с топологией поэлементной сходимости). -/
abbrev LinearCauchy.CMat (n : ℕ) : Type :=
  @ContinuousMap (Icc (0 : ℝ) 1) (Matrix (Fin n) (Fin n) ℂ) _
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace

open scoped Classical in
/-- Коэффициент как непрерывное отображение `[0,1] → Mat`; вне класса непрерывных
функций значение фиктивное (`0`). -/
def LinearCauchy.coeff (A : ℝ → Matrix (Fin n) (Fin n) ℂ) :
    LinearCauchy.CMat n :=
  if h : ContinuousOn A (Icc 0 1) then ⟨fun x => A x, h.domRestrict⟩ else 0

/-- Матрица Коши `Φ(x, λ)` системы `X' = (A₀ + λ A₁) X`, `Φ(0, λ) = I`; определена на
`[0,1]` (вне отрезка продолжена константой), сумма ряда Пикара. -/
def linearCauchy (A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ) (x : ℝ) (l : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  LinearCauchy.psi (LinearCauchy.coeff A₀) (LinearCauchy.coeff A₁) l
    (projIcc 0 1 zero_le_one x)

namespace LinearCauchy

lemma ext_coeff {A : ℝ → Matrix (Fin n) (Fin n) ℂ} (hA : ContinuousOn A (Icc 0 1)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ext (coeff A) t = A t := by
  rw [ext_of_mem _ ht]
  simp [coeff, hA]
  rfl

lemma linearCauchy_eq_ext (A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ) (x : ℝ) (l : ℂ) :
    linearCauchy A₀ A₁ x l = ext (psi (coeff A₀) (coeff A₁) l) x := rfl

/-- Интегральное уравнение для `Φ` (матричная форма, норма — оператор `ℓ∞`). -/
theorem linearCauchy_integral {A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hA₀ : ContinuousOn A₀ (Icc 0 1)) (hA₁ : ContinuousOn A₁ (Icc 0 1)) (l : ℂ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    linearCauchy A₀ A₁ x l
      = 1 + ∫ t in (0 : ℝ)..x, (A₀ t + l • A₁ t) * linearCauchy A₀ A₁ t l := by
  have h := psi_apply (coeff A₀) (coeff A₁) l ⟨x, hx⟩
  rw [linearCauchy_eq_ext, ext_of_mem _ hx, h]
  congr 1
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le hx.1] at ht
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
  simp only [ext_coeff hA₀ ht1, ext_coeff hA₁ ht1, linearCauchy_eq_ext]

/-- Линейное отображение коммутирует с интегралом (конечномерная область). -/
lemma integral_linear_comm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E]
    [CompleteSpace F] (φ : E →ₗ[ℂ] F) {f : ℝ → E} {a b : ℝ} (hf : Continuous f) :
    ∫ t in a..b, φ (f t) = φ (∫ t in a..b, f t) :=
  (φ.toContinuousLinearMap).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

/-- Подынтегральная функция в расширенной форме: непрерывна на `ℝ`. -/
lemma continuous_integrand (A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Continuous fun t => (ext (coeff A₀) t + l • ext (coeff A₁) t)
      * ext (psi (coeff A₀) (coeff A₁) l) t := by
  have h0 := continuous_ext (coeff A₀)
  have h1 := continuous_ext (coeff A₁)
  have h2 := continuous_ext (psi (coeff A₀) (coeff A₁) l)
  fun_prop

/-- Поэлементная форма интегрального уравнения. -/
lemma entry_integral (A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (i j : Fin n) :
    linearCauchy A₀ A₁ x l i j = (1 : Matrix (Fin n) (Fin n) ℂ) i j
      + ∫ t in (0 : ℝ)..x, ((ext (coeff A₀) t + l • ext (coeff A₁) t)
          * ext (psi (coeff A₀) (coeff A₁) l) t) i j := by
  have h := psi_apply (coeff A₀) (coeff A₁) l ⟨x, hx⟩
  have h2 := integral_linear_comm (Matrix.entryLinearMap ℂ ℂ i j) (a := 0) (b := x)
    (continuous_integrand A₀ A₁ l)
  rw [linearCauchy_eq_ext, ext_of_mem _ hx, h]
  simp only [Matrix.entryLinearMap_apply] at h2
  simp only [Matrix.add_apply]
  rw [h2]

end LinearCauchy

/-- `Φ(0, λ) = I`. -/
theorem linearCauchy_zero (A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    linearCauchy A₀ A₁ 0 l = 1 := by
  ext i j
  rw [LinearCauchy.entry_integral A₀ A₁ l ⟨le_rfl, zero_le_one⟩ i j]
  simp

/-- Элементы `Φ(·, λ)` непрерывны по `x`. -/
theorem continuous_linearCauchy (A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ) (l : ℂ)
    (i j : Fin n) : Continuous fun x => linearCauchy A₀ A₁ x l i j := by
  have h := ((Matrix.entryLinearMap ℂ ℂ i j).continuous_of_finiteDimensional).comp
    (LinearCauchy.continuous_ext (LinearCauchy.psi (LinearCauchy.coeff A₀)
      (LinearCauchy.coeff A₁) l))
  exact h

/-- Дифференциальное уравнение `∂ₓΦ = (A₀ + λ A₁) Φ` на `[0,1]` (поэлементно). -/
theorem linearCauchy_hasDerivWithinAt {A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hA₀ : ContinuousOn A₀ (Icc 0 1)) (hA₁ : ContinuousOn A₁ (Icc 0 1)) (l : ℂ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (i j : Fin n) :
    HasDerivWithinAt (fun s => linearCauchy A₀ A₁ s l i j)
      (((A₀ x + l • A₁ x) * linearCauchy A₀ A₁ x l) i j) (Icc 0 1) x := by
  have hc : Continuous fun t => ((LinearCauchy.ext (LinearCauchy.coeff A₀) t
      + l • LinearCauchy.ext (LinearCauchy.coeff A₁) t)
      * LinearCauchy.ext (LinearCauchy.psi (LinearCauchy.coeff A₀)
        (LinearCauchy.coeff A₁) l) t) i j :=
    ((Matrix.entryLinearMap ℂ ℂ i j).continuous_of_finiteDimensional).comp
      (LinearCauchy.continuous_integrand A₀ A₁ l)
  have hd := (hc.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add
    ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
  have hd2 := hd.hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  have hx' : ((LinearCauchy.ext (LinearCauchy.coeff A₀) x
      + l • LinearCauchy.ext (LinearCauchy.coeff A₁) x)
      * LinearCauchy.ext (LinearCauchy.psi (LinearCauchy.coeff A₀)
        (LinearCauchy.coeff A₁) l) x) i j
      = ((A₀ x + l • A₁ x) * linearCauchy A₀ A₁ x l) i j := by
    rw [LinearCauchy.ext_coeff hA₀ hx, LinearCauchy.ext_coeff hA₁ hx]
    rfl
  rw [hx'] at hd2
  refine hd2.congr (fun y hy => ?_) ?_
  · rw [LinearCauchy.entry_integral A₀ A₁ l hy i j]
  · rw [LinearCauchy.entry_integral A₀ A₁ l hx i j]

/-- Целость по `λ`: каждый элемент `Φ(x, ·)` — целая функция. -/
theorem differentiable_linearCauchy (A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ) (x : ℝ)
    (i j : Fin n) : Differentiable ℂ fun l => linearCauchy A₀ A₁ x l i j := by
  exact LinearCauchy.differentiable_psi_apply (LinearCauchy.coeff A₀) (LinearCauchy.coeff A₁)
    (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap (projIcc 0 1 zero_le_one x)

/-- Определитель `det Φ(x, ·)` — целая функция. -/
theorem differentiable_linearCauchy_det (A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ) (x : ℝ) :
    Differentiable ℂ fun l => (linearCauchy A₀ A₁ x l).det := by
  simp only [Matrix.det_apply']
  refine Differentiable.fun_sum (fun σ _ => ?_)
  refine Differentiable.const_mul ?_ _
  exact Differentiable.fun_finsetProd (fun k _ => differentiable_linearCauchy A₀ A₁ x _ _)

end Involution

end
