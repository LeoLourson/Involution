module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Matrix.Basic

/-! # Общие двухточечные условия: постановка линии G

Определения записей C24–C26 и экспозиции `paper/exposition-G.tex`: гипотеза (H) на
коэффициент `a`, краевые формы (2), собственное значение задачи (1), (2), величины
`ε, σ±, τ±, t±, ℓ±, L, d, ϰ, P, Q, 𝒜, ℬ`, главная часть `F`, коэффициенты `θ`, регулярность
и сильная регулярность.

Знак `s = ±1` каналов `±` передаётся вещественным параметром `s` (`s = 1` — канал `+`).
Номера форм `j = 1, 2` статьи — `Fin 2` (`0`, `1`), порядок производной `0, 1` — `Fin 2`.
Матрицы Коши и `Δ` здесь нет: их строит пакет G1. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution
namespace GeneralBC

/-! ## Гипотеза (H) -/

/-- Гипотеза (H) C24: `a` вещественна, `a ∈ W¹₁(-1,1)`, `|a| ≥ m > 0`, `a(x)a(-x) ≤ κ < 1`.
`W¹₁(-1,1)` кодируется абсолютной непрерывностью на `[-1,1]` (непрерывный представитель);
оценки `|a| ≥ m`, `a(x)a(-x) ≤ κ` — для всех `x ∈ [-1,1]`. -/
structure HypH (a : ℝ → ℝ) (m κ : ℝ) : Prop where
  ac : AbsolutelyContinuousOnInterval a (-1) 1
  m_pos : 0 < m
  lower : ∀ x ∈ Icc (-1 : ℝ) 1, m ≤ |a x|
  kappa_lt : κ < 1
  upper : ∀ x ∈ Icc (-1 : ℝ) 1, a x * a (-x) ≤ κ

/-- Гипотеза (H) с некоторыми постоянными `m`, `κ`. -/
def Hyp (a : ℝ → ℝ) : Prop := ∃ m κ : ℝ, HypH a m κ

/-- `a ∈ W²₁(-1,1)` : `a` и её (почти всюду) производная `a'` абсолютно непрерывны. -/
def IsW21 (a : ℝ → ℝ) : Prop :=
  ∃ a' : ℝ → ℝ, AbsolutelyContinuousOnInterval a (-1) 1 ∧
    AbsolutelyContinuousOnInterval a' (-1) 1 ∧
    ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt a (a' x) x

/-! ## Краевые формы (2) -/

/-- Коэффициенты форм `U_j(y) = α_{j1} y'(-1) + α_{j0} y(-1) + β_{j1} y'(1) + β_{j0} y(1)`:
`α j i`, `β j i` — коэффициент при `y^{(i)}(∓1)`, форма с номером `j ∈ Fin 2`. -/
structure Forms where
  α : Fin 2 → Fin 2 → ℂ
  β : Fin 2 → Fin 2 → ℂ

namespace Forms

/-- Значение формы `U_j` на паре `(y, y')`. -/
def eval (U : Forms) (j : Fin 2) (y y' : ℝ → ℂ) : ℂ :=
  U.α j 1 * y' (-1) + U.α j 0 * y (-1) + U.β j 1 * y' 1 + U.β j 0 * y 1

/-- Строка коэффициентов `(α_{j0}, α_{j1}, β_{j0}, β_{j1})`. -/
def row (U : Forms) (j : Fin 2) : Fin 4 → ℂ :=
  ![U.α j 0, U.α j 1, U.β j 0, U.β j 1]

/-- Форма `U_j` содержит производную: коэффициент при `y'(±1)` отличен от нуля. -/
def HasDeriv (U : Forms) (j : Fin 2) : Prop := U.α j 1 ≠ 0 ∨ U.β j 1 ≠ 0

open Classical in
/-- Порядок `κ_j ∈ {0,1}` формы `U_j`: наибольший порядок производной с ненулевым коэффициентом. -/
def ord (U : Forms) (j : Fin 2) : ℕ := if U.HasDeriv j then 1 else 0

/-- Линейные комбинации `(cU)_j = ∑_l c_{jl} U_l`. -/
def combo (U : Forms) (c : Matrix (Fin 2) (Fin 2) ℂ) : Forms where
  α j i := ∑ l, c j l * U.α l i
  β j i := ∑ l, c j l * U.β l i

/-- Линейная независимость форм `U_1, U_2` (как векторов `ℂ⁴`). -/
def LinIndep (U : Forms) : Prop := LinearIndependent ℂ U.row

/-- Нормированность в смысле S48, с. 645: сумма порядков `κ_1 + κ_2` не понижается при переходе
к другому базису `cU`, `det c ≠ 0`, линейной оболочки форм. -/
def IsNormalized (U : Forms) : Prop :=
  ∀ c : Matrix (Fin 2) (Fin 2) ℂ, IsUnit c.det →
    U.ord 0 + U.ord 1 ≤ (U.combo c).ord 0 + (U.combo c).ord 1

/-- Расстановка форм: `κ_1 ≥ κ_2`. Условия C24 «с точностью до перестановки» принимают вид
`(κ_1,κ_2) ∈ {(0,0),(1,1),(1,0)}` при этой расстановке. -/
def IsOrdered (U : Forms) : Prop := U.ord 1 ≤ U.ord 0

/-- Вид `(κ_1, κ_2)` пары форм. -/
inductive Kind
  | k00
  | k11
  | k10
  deriving DecidableEq

open Classical in
/-- Вид пары форм; значение `(κ_1,κ_2) = (0,1)` (не встречается при `IsOrdered`)
отнесено к `k10`. -/
def kind (U : Forms) : Kind :=
  if ¬ U.HasDeriv 0 ∧ ¬ U.HasDeriv 1 then Kind.k00
  else if U.HasDeriv 0 ∧ U.HasDeriv 1 then Kind.k11 else Kind.k10

/-- Миноры `J_0 = α_{10}β_{20} − β_{10}α_{20}` и `J_1 = β_{11}α_{21} − α_{11}β_{21}`. -/
def J0 (U : Forms) : ℂ := U.α 0 0 * U.β 1 0 - U.β 0 0 * U.α 1 0

def J1 (U : Forms) : ℂ := U.β 0 1 * U.α 1 1 - U.α 0 1 * U.β 1 1

end Forms

/-- Формы Дирихле `U_1 = y(-1)`, `U_2 = y(1)`. -/
def dirichletForms : Forms where
  α j i := if j = 0 ∧ i = 0 then 1 else 0
  β j i := if j = 1 ∧ i = 0 then 1 else 0

/-- Формы (E) C24 / prop:refl: `U_1 = y'(1) + y'(-1)`, `U_2 = y(1) − y(-1)`. -/
def reflForms : Forms where
  α j i := if j = 0 ∧ i = 1 then 1 else if j = 1 ∧ i = 0 then -1 else 0
  β j i := if j = 0 ∧ i = 1 then 1 else if j = 1 ∧ i = 0 then 1 else 0

/-! ## Собственное значение задачи (1), (2) -/

/-- `y` — собственная функция задачи (1), (2) при `lam`, с первой и второй производными `y'`, `y''`:
`y ∈ W²₁(-1,1)` кодируется абсолютной непрерывностью `y` и `y'` на `[-1,1]` с
`y' = (y)'`, `y'' = (y')'` почти всюду; (1) — почти всюду; (2) — для непрерывных представителей
`y`, `y'`; `y ≢ 0`. -/
structure IsEigenpair (a : ℝ → ℝ) (U : Forms) (lam : ℂ) (y y' y'' : ℝ → ℂ) : Prop where
  ac_y : AbsolutelyContinuousOnInterval y (-1) 1
  ac_y' : AbsolutelyContinuousOnInterval y' (-1) 1
  deriv_y : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt y (y' x) x
  deriv_y' : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt y' (y'' x) x
  eqn : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → -y'' x - (a x : ℂ) * y'' (-x) = lam * y x
  bc : ∀ j, U.eval j y y' = 0
  nontrivial : ∃ x ∈ Icc (-1 : ℝ) 1, y x ≠ 0

/-- Собственное значение задачи (1), (2). -/
def IsEigenvalue (a : ℝ → ℝ) (U : Forms) (lam : ℂ) : Prop :=
  ∃ y y' y'' : ℝ → ℂ, IsEigenpair a U lam y y' y''

/-! ## Величины на `[0,1]` -/

/-- `ε = sign a` (при (H) `a` знакопостоянна; берём знак `a(0)`). -/
def eps (a : ℝ → ℝ) : ℝ := if 0 < a 0 then 1 else -1

/-- `σ_s(x) = 1 + s √(a(x)a(-x))`, `s = ±1`. -/
def sigma (a : ℝ → ℝ) (s : ℝ) (x : ℝ) : ℝ := 1 + s * Real.sqrt (a x * a (-x))

/-- `τ_s = σ_s^{-1/2}`. -/
def tau (a : ℝ → ℝ) (s : ℝ) (x : ℝ) : ℝ := (Real.sqrt (sigma a s x))⁻¹

/-- Фаза `t_s(x) = ∫₀ˣ τ_s`. -/
def tPhase (a : ℝ → ℝ) (s : ℝ) (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..x, tau a s u

/-- `ℓ_s = t_s(1)`. -/
def ell (a : ℝ → ℝ) (s : ℝ) : ℝ := tPhase a s 1

/-- `L = ℓ_+ + ℓ_-`. -/
def Ltot (a : ℝ → ℝ) : ℝ := ell a 1 + ell a (-1)

/-- `d = ℓ_+ − ℓ_-`. -/
def dlt (a : ℝ → ℝ) : ℝ := ell a 1 - ell a (-1)

/-- `ω_s = τ_s(1)`. -/
def omega (a : ℝ → ℝ) (s : ℝ) : ℝ := tau a s 1

/-- `τ_s(0)`. -/
def tau0 (a : ℝ → ℝ) (s : ℝ) : ℝ := tau a s 0

/-- `k(x) = ε √(a(-x)/a(x))`. -/
def kfun (a : ℝ → ℝ) (x : ℝ) : ℝ := eps a * Real.sqrt (a (-x) / a x)

/-- `ϰ = k(1)`. -/
def varkappa (a : ℝ → ℝ) : ℝ := kfun a 1

/-- `P_j^{±} = β_{j1} ∓ ϰ α_{j1}`; параметр `s = ±1` — верхний знак. -/
def Pc (a : ℝ → ℝ) (U : Forms) (j : Fin 2) (s : ℝ) : ℂ :=
  U.β j 1 - ((s * varkappa a : ℝ) : ℂ) * U.α j 1

/-- `Q_j^{±} = β_{j0} ± ϰ α_{j0}`. -/
def Qc (a : ℝ → ℝ) (U : Forms) (j : Fin 2) (s : ℝ) : ℂ :=
  U.β j 0 + ((s * varkappa a : ℝ) : ℂ) * U.α j 0

/-- `𝒜 = ω_+ P_1^+ Q_2^-`. -/
def calA (a : ℝ → ℝ) (U : Forms) : ℂ := (omega a 1 : ℂ) * Pc a U 0 1 * Qc a U 1 (-1)

/-- `ℬ = ω_- P_1^- Q_2^+`. -/
def calB (a : ℝ → ℝ) (U : Forms) : ℂ := (omega a (-1) : ℂ) * Pc a U 0 (-1) * Qc a U 1 1

/-! ## Главная часть `F`, коэффициенты `θ`, регулярность -/

/-- Главная часть `F(ρ)` по таблице C24 (вид форм и знак `ε`). -/
def Fchar (a : ℝ → ℝ) (U : Forms) (ρ : ℂ) : ℂ :=
  let cp := Complex.cos (ρ * ell a 1)
  let sp := Complex.sin (ρ * ell a 1)
  let cm := Complex.cos (ρ * ell a (-1))
  let sm := Complex.sin (ρ * ell a (-1))
  if 0 < a 0 then
    match U.kind with
    | Forms.Kind.k00 => cp * sm
    | Forms.Kind.k11 => sp * cm
    | Forms.Kind.k10 => calA a U * sp * sm + calB a U * cp * cm
  else
    match U.kind with
    | Forms.Kind.k00 => sp * cm
    | Forms.Kind.k11 => cp * sm
    | Forms.Kind.k10 => calA a U * cp * cm + calB a U * sp * sm

/-- `θ_+` — коэффициент при `e^{iρL}`. -/
def thetaPlus (a : ℝ → ℝ) (U : Forms) : ℂ :=
  match U.kind with
  | Forms.Kind.k00 => -Complex.I / 4
  | Forms.Kind.k11 => -Complex.I / 4
  | Forms.Kind.k10 => (eps a : ℂ) * (calB a U - calA a U) / 4

/-- `θ_-` — коэффициент при `e^{-iρL}`. -/
def thetaMinus (a : ℝ → ℝ) (U : Forms) : ℂ :=
  match U.kind with
  | Forms.Kind.k00 => Complex.I / 4
  | Forms.Kind.k11 => Complex.I / 4
  | Forms.Kind.k10 => (eps a : ℂ) * (calB a U - calA a U) / 4

/-- Знак перед `sin ρd` в видах `(0,0)`, `(1,1)`: `F = ½(sin ρL + sd · sin ρd)`. -/
def sinSign (a : ℝ → ℝ) (U : Forms) : ℝ :=
  match U.kind with
  | Forms.Kind.k00 => -eps a
  | Forms.Kind.k11 => eps a
  | Forms.Kind.k10 => 0

/-- `θ_d^+` — коэффициент при `e^{iρd}`. -/
def thetaDPlus (a : ℝ → ℝ) (U : Forms) : ℂ :=
  match U.kind with
  | Forms.Kind.k10 => (calA a U + calB a U) / 4
  | _ => (sinSign a U : ℂ) * (-Complex.I / 4)

/-- `θ_d^-` — коэффициент при `e^{-iρd}`. -/
def thetaDMinus (a : ℝ → ℝ) (U : Forms) : ℂ :=
  match U.kind with
  | Forms.Kind.k10 => (calA a U + calB a U) / 4
  | _ => (sinSign a U : ℂ) * (Complex.I / 4)

/-- `θ = θ_+`. -/
def theta (a : ℝ → ℝ) (U : Forms) : ℂ := thetaPlus a U

/-- Задача (1), (2) при (H) **регулярна**, если `θ ≠ 0`. -/
def Regular (a : ℝ → ℝ) (U : Forms) : Prop := theta a U ≠ 0

/-- Нули `F` отделены в полуплоскости `Re ρ ≥ 0` : `inf |ρ⁰ − ρ⁰'| > 0` по парам различных нулей. -/
def ZerosSeparated (a : ℝ → ℝ) (U : Forms) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ρ ρ' : ℂ, 0 ≤ ρ.re → 0 ≤ ρ'.re → Fchar a U ρ = 0 → Fchar a U ρ' = 0 →
    ρ ≠ ρ' → δ ≤ ‖ρ - ρ'‖

/-- Все нули `F` с `Re ρ ≥ 0`, кроме конечного числа, простые (кратность — `analyticOrderAt`;
`F` целая). -/
def ZerosEventuallySimple (a : ℝ → ℝ) (U : Forms) : Prop :=
  {ρ : ℂ | 0 ≤ ρ.re ∧ Fchar a U ρ = 0 ∧ analyticOrderAt (Fchar a U) ρ ≠ 1}.Finite

/-- **Усиленно (сильно) регулярна**: регулярна, нули `F` отделены и все, кроме конечного числа,
просты. -/
def StronglyRegular (a : ℝ → ℝ) (U : Forms) : Prop :=
  Regular a U ∧ ZerosSeparated a U ∧ ZerosEventuallySimple a U

/-! ## Остальные величины утверждений -/

/-- `γ_U` по таблице C24. -/
def gammaU (a : ℝ → ℝ) (U : Forms) : ℂ :=
  match U.kind with
  | Forms.Kind.k00 => -8 * Complex.I * (varkappa a : ℂ) * U.J0
  | Forms.Kind.k11 =>
      8 * Complex.I * (omega a 1 : ℂ) * (omega a (-1) : ℂ) * (varkappa a : ℂ) * U.J1
  | Forms.Kind.k10 => 4 * Complex.I * (eps a : ℂ)

/-- Показатель `κ_1 + κ_2`. -/
def kappaSum (U : Forms) : ℕ := U.ord 0 + U.ord 1

/-- `G(ρ²) = ρ^{κ_1+κ_2−1} F(ρ)` как функция `λ`: при `λ ≠ 0` берётся корень `ρ = λ^{1/2}`
(правая часть чётна по `ρ`); значение в `0` — по виду форм: `F'(0)` для `(0,0)`, `0` для
`(1,1)`, `F(0)` для `(1,0)`. Что `G` целая — утверждение `Gfun_differentiable`
в `Statements.lean`. -/
def Gfun (a : ℝ → ℝ) (U : Forms) (lam : ℂ) : ℂ :=
  if lam = 0 then
    match U.kind with
    | Forms.Kind.k00 => deriv (Fchar a U) 0
    | Forms.Kind.k11 => 0
    | Forms.Kind.k10 => Fchar a U 0
  else
    match U.kind with
    | Forms.Kind.k00 => Fchar a U (lam ^ (1 / 2 : ℂ)) / lam ^ (1 / 2 : ℂ)
    | Forms.Kind.k11 => lam ^ (1 / 2 : ℂ) * Fchar a U (lam ^ (1 / 2 : ℂ))
    | Forms.Kind.k10 => Fchar a U (lam ^ (1 / 2 : ℂ))

end GeneralBC
end Involution
