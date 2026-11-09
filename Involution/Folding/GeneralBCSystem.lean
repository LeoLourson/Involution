module

public import Involution.Folding.GeneralBC
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Сложенная система первого порядка (C24, шаги 4–7)

Матрицы `K`, `W` (столбцы `g_{±,s}`), `D`, `E`, строки `U⁰_j` и матрица `𝔘⁰(ρ)`.
Столбцы нумеруются `0,1,2,3 = (+,+),(+,−),(−,+),(−,−)` (порядок C24 шаг 5): канал столбца
`c` есть `+` при `c < 2`, знак `s` равен `+1` при чётном `c`.
Матрица Коши `Φ`, `Δ` — пакет G1; здесь их нет. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution
namespace GeneralBC

/-- Канал `±1` столбца `c ∈ Fin 4`. -/
def chan (c : Fin 4) : ℝ := if (c : ℕ) < 2 then 1 else -1

/-- Знак `s = ±1` столбца `c ∈ Fin 4`. -/
def sgn (c : Fin 4) : ℝ := if (c : ℕ) % 2 = 0 then 1 else -1

/-- Матрица `K = [[0, I], [−M⁻¹, 0]]`, `M(x) = [[1, a(x)], [a(−x), 1]]`;
`M⁻¹ = (1 − p)⁻¹ [[1, −a(x)], [−a(−x), 1]]`, `p = a(x)a(−x)` (явная запись обратной). -/
def Kmat (a : ℝ → ℝ) (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let q : ℂ := ((1 - a x * a (-x))⁻¹ : ℝ)
  Matrix.of ![![0, 0, 1, 0], ![0, 0, 0, 1],
    ![-q, q * (a x : ℂ), 0, 0], ![q * (a (-x) : ℂ), -q, 0, 0]]

/-- Решение `Y' = ρ K Y` в интегральной форме на `[0,1]`
(поэлементные интегралы). -/
def IsSol (a : ℝ → ℝ) (ρ : ℂ) (Y : ℝ → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ∀ i j,
    Y x i j = Y 0 i j + ∫ t in (0 : ℝ)..x, (ρ • (Kmat a t * Y t)) i j

/-- Собственный вектор `g_{±,s}(x) = (e_±, i s τ_± e_±)`, `e_± = (1, ±k)`, столбец `c`. -/
def gvec (a : ℝ → ℝ) (c : Fin 4) (x : ℝ) : Fin 4 → ℂ :=
  ![1, ((chan c * kfun a x : ℝ) : ℂ), Complex.I * (sgn c : ℂ) * (tau a (chan c) x : ℂ),
    Complex.I * (sgn c : ℂ) * (tau a (chan c) x : ℂ) * ((chan c * kfun a x : ℝ) : ℂ)]

/-- Матрица `W(x)` со столбцами `g_{+,+}, g_{+,−}, g_{−,+}, g_{−,−}`. -/
def Wmat (a : ℝ → ℝ) (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun r c => gvec a c x r

/-- Амплитуда `D_s(x) = (τ_s(0) / (|k(x)| τ_s(x)))^{1/2}`. -/
def Damp (a : ℝ → ℝ) (s : ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (tau0 a s / (|kfun a x| * tau a s x))

/-- `𝐃 = diag(D_+, D_+, D_−, D_−)`. -/
def Dmat (a : ℝ → ℝ) (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun c => (Damp a (chan c) x : ℂ)

/-- `E(x,ρ) = diag(e^{isρ t_±(x)})`. -/
def Emat (a : ℝ → ℝ) (x : ℝ) (ρ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun c =>
    Complex.exp (Complex.I * (sgn c : ℂ) * ρ * (tPhase a (chan c) x : ℂ))

/-- Строка `U⁰_j` главной части формы `U_j` в переменных `Y = (w, w'/ρ)`
(C24 шаг 4): `(0,0,β_{j1},−α_{j1})` при `κ_j = 1`, `(β_{j0},α_{j0},0,0)` при `κ_j = 0`. -/
def U0row (U : Forms) (j : Fin 2) : Fin 4 → ℂ := by
  classical
  exact if U.HasDeriv j then ![0, 0, U.β j 1, -U.α j 1] else ![U.β j 0, U.α j 0, 0, 0]

/-- Главная часть столбца `c` при `x`: `D g e^{isρ t}`. -/
def colv (a : ℝ → ℝ) (c : Fin 4) (ρ : ℂ) (x : ℝ) : Fin 4 → ℂ :=
  fun i => (Damp a (chan c) x : ℂ) *
    Complex.exp (Complex.I * (sgn c : ℂ) * ρ * (tPhase a (chan c) x : ℂ)) * gvec a c x i

/-- Матрица `𝔘⁰(ρ)` (C24 шаг 7): строки 1, 2 — формы `Y₁ − Y₂`, `Y₃ + Y₄` на `g(0)`,
строки `2+j` — `U⁰_j` на `D(1) g(1) e^{isρℓ}`. -/
def Ufrak0 (a : ℝ → ℝ) (U : Forms) (ρ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![fun c => colv a c ρ 0 0 - colv a c ρ 0 1,
    fun c => colv a c ρ 0 2 + colv a c ρ 0 3,
    fun c => ∑ i, U0row U 0 i * colv a c ρ 1 i,
    fun c => ∑ i, U0row U 1 i * colv a c ρ 1 i]

/-- `c_U = D_+(1) D_−(1) · 4 i ε τ_ε(0) · γ_U` (C24 формула (7), C25 формула (1)). -/
def cU (a : ℝ → ℝ) (U : Forms) : ℂ :=
  (Damp a 1 1 : ℂ) * (Damp a (-1) 1 : ℂ) * 4 * Complex.I * (eps a : ℂ) *
    (tau0 a (eps a) : ℂ) * gammaU a U

/-- `c_∗ = i ε γ_U τ⁰_ε / (4 |ϰ| √(ω_+ ω_- τ⁰_+ τ⁰_-))` (C24 утверждение 2). -/
def cStar (a : ℝ → ℝ) (U : Forms) : ℂ :=
  Complex.I * (eps a : ℂ) * gammaU a U * (tau0 a (eps a) : ℂ) /
    (4 * ((|varkappa a| : ℝ) : ℂ) *
      (Real.sqrt (omega a 1 * omega a (-1) * tau0 a 1 * tau0 a (-1)) : ℂ))

end GeneralBC
end Involution
