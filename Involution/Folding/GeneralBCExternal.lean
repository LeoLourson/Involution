module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Diagonal

/-! # Внешние входы линии G: теоремы S50, S51, S54

Три теоремы об асимптотической фундаментальной матрице системы `y' − A y = ζ B y` с большим
параметром не доказываются; каждая записана определением-высказыванием `Prop` в той
специализации (`n = 4`, чисто мнимая диагональ, нулевая или суммируемая матрица `B`), в которой
её применяют записи C24 (шаг 6), C25 (шаг 1), C26 (шаги 2–3). Решения — интегральные
(поэлементные интегралы), как у суммируемых коэффициентов. Входят гипотезами итоговых теорем.
Карточки: `claims/S50-*.md`, `claims/S51-*.md`, `claims/S54-*.md`. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution
namespace GeneralBC

/-- `Y' = Mx(t) Y` на `[0,1]` в интегральной форме (поэлементные интегралы). -/
def IsMatSol (Mx Y : ℝ → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, Y x i j = Y 0 i j + ∫ t in (0 : ℝ)..x, (Mx t * Y t) i j

/-- Остаток `R` равномерно мал на множестве `S` параметров при `‖ζ‖ → ∞`:
`∀ ε > 0 ∃ r ∀ ζ ∈ S, r ≤ ‖ζ‖ → ∀ x ∈ [0,1], ‖R_{ij}(x,ζ)‖ ≤ ε`. -/
def UniformlySmall (R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ) (S : Set ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, ∀ ζ ∈ S, r ≤ ‖ζ‖ →
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, ‖R x ζ i j‖ ≤ ε

/-- Теорема 1 S50, с. 797 (`n = 4`, `s = 2`, `A` с нулевой диагональю, поэтому `M = I`).
Пусть `B = diag b` непрерывна, `b` после перестановки координат упорядочена как в (4):
`b₁ < b₂ < 0 < b₃ < b₄` на `[0,1]`; элементы `A` суммируемы. Тогда для любого `h ∈ ℝ`
в полуплоскости `s Re ζ ≥ s h` (`Re ζ ≥ h` при `s = 1`, `Re ζ ≤ h` при `s = −1`)
существует фундаментальная матрица `(I + R)E`, `E = diag e^{ζ ∫ b_j}`,
`R → 0` равномерно по `x`. (Перестановка координат — сопряжение матрицей перестановки, не меняет
ни нулевой диагонали, ни суммируемости.) Фундаментальность: `R` мала, поэтому `I + R(0)`
обратима при больших `‖ζ‖`. -/
def S50Theorem1 : Prop :=
  ∀ (b : Fin 4 → ℝ → ℝ) (A : ℝ → Matrix (Fin 4) (Fin 4) ℂ),
    (∀ j, ContinuousOn (b j) (Icc (0 : ℝ) 1)) →
    (∃ σ : Equiv.Perm (Fin 4), ∀ x ∈ Icc (0 : ℝ) 1,
      b (σ 0) x < b (σ 1) x ∧ b (σ 1) x < 0 ∧ 0 < b (σ 2) x ∧ b (σ 2) x < b (σ 3) x) →
    (∀ i j, IntervalIntegrable (fun x => A x i j) volume 0 1) →
    (∀ x j, A x j j = 0) →
    ∀ s h : ℝ, (s = 1 ∨ s = -1) →
      ∃ R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ,
        UniformlySmall R {ζ | s * h ≤ s * ζ.re} ∧
        ∃ r₀ : ℝ, ∀ ζ : ℂ, s * h ≤ s * ζ.re → r₀ ≤ ‖ζ‖ →
          IsMatSol (fun x => A x + ζ • Matrix.diagonal fun j => (b j x : ℂ))
            (fun x => (1 + R x ζ) *
              Matrix.diagonal fun j => Complex.exp (ζ * ((∫ t in (0 : ℝ)..x, b j t : ℝ) : ℂ)))

/-- Теорема 1.5 S51, с. 270–271 (`n = 4`, `C = 0`, `A = diag(i c_j)`, `c_j` непрерывны и
попарно различны на `[0,1]`, поэтому (1.10) выполнено с `θ_{jk} ∈ {π/2, 3π/2}`;
`B` суммируема). При фиксированном `h = κ ≥ 0` в каждой из полуплоскостей `s Im ρ ≥ −h`
(сектор Λ_j^κ) существует фундаментальная матрица `M (I + R) E`, `M = diag e^{∫ b_{jj}}`,
`E = diag e^{ρ ∫ i c_j}`, `R → 0` равномерно по `x`. -/
def S51Theorem15 : Prop :=
  ∀ (c : Fin 4 → ℝ → ℝ) (B : ℝ → Matrix (Fin 4) (Fin 4) ℂ),
    (∀ j, ContinuousOn (c j) (Icc (0 : ℝ) 1)) →
    (∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, i ≠ j → c i x ≠ c j x) →
    (∀ i j, IntervalIntegrable (fun x => B x i j) volume 0 1) →
    ∀ s h : ℝ, (s = 1 ∨ s = -1) → 0 ≤ h →
      ∃ R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ,
        UniformlySmall R {ρ | -h ≤ s * ρ.im} ∧
        ∃ r₀ : ℝ, ∀ ρ : ℂ, -h ≤ s * ρ.im → r₀ ≤ ‖ρ‖ →
          IsMatSol
            (fun x => B x + ρ • Matrix.diagonal fun j => Complex.I * (c j x : ℂ))
            (fun x =>
              Matrix.diagonal (fun j => Complex.exp (∫ t in (0 : ℝ)..x, B t j j)) *
              (1 + R x ρ) *
              Matrix.diagonal fun j =>
                Complex.exp (ρ * (Complex.I * ((∫ t in (0 : ℝ)..x, c j t : ℝ) : ℂ))))

/-- Теорема 1.2 S54, с. 927–928, при `m = 1`, `B₁ = 0`, `C = 0` в виде следствия карточки S54
(«Следствие, которое берётся в проект»; формулировка проекта, не авторов): `A = diag(i c_j)`,
`c_j ∈ W¹₁` (абсолютно непрерывны) попарно различны на `[0,1]`; `B = B₀` имеет суммируемую
диагональ и недиагональные элементы из `W¹₁`. Тогда для каждого `h ≥ 0` в полуплоскости
`Im(sρ) ≥ −h` существуют `C`, `r₁` и фундаментальная матрица `M (I + 𝓔) E` с
`sup_x |𝓔| ≤ C / |ρ|` при `|ρ| ≥ r₁`. -/
def S54Theorem12 : Prop :=
  ∀ (c : Fin 4 → ℝ → ℝ) (B : ℝ → Matrix (Fin 4) (Fin 4) ℂ),
    (∀ j, AbsolutelyContinuousOnInterval (c j) 0 1) →
    (∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, i ≠ j → c i x ≠ c j x) →
    (∀ i, IntervalIntegrable (fun x => B x i i) volume 0 1) →
    (∀ i j, i ≠ j → AbsolutelyContinuousOnInterval (fun x => B x i j) 0 1) →
    ∀ s h : ℝ, (s = 1 ∨ s = -1) → 0 ≤ h →
      ∃ (C r₁ : ℝ) (𝓔 : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ),
        ∀ ρ : ℂ, -h ≤ s * ρ.im → r₁ ≤ ‖ρ‖ →
          (∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, ‖𝓔 x ρ i j‖ ≤ C / ‖ρ‖) ∧
          IsMatSol
            (fun x => B x + ρ • Matrix.diagonal fun j => Complex.I * (c j x : ℂ))
            (fun x =>
              Matrix.diagonal (fun j => Complex.exp (∫ t in (0 : ℝ)..x, B t j j)) *
              (1 + 𝓔 x ρ) *
              Matrix.diagonal fun j =>
                Complex.exp (ρ * (Complex.I * ((∫ t in (0 : ℝ)..x, c j t : ℝ) : ℂ))))

end GeneralBC
end Involution
