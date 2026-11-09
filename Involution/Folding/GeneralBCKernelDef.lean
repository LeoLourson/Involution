module

public import Involution.Folding.GeneralBCKernel

/-! # Лемма `lem:kernel`: определения (C24 шаги 7–8, C25 шаг 9; статья, `lem:kernel`)

Функции `χ_±` и их производные по аргументу (`χ_+ = cos`, `χ_- = sin` при `ε = 1`;
`χ_+ = sin`, `χ_- = cos` при `ε = -1`), вектор `c(ξ,ζ)` координат главных частей, главная
часть `y⁰(x)` решения и матрица `𝔐(ρ)` размера `2×2` (формула (M) статьи).

Нормировка. Статья берёт `D(1) = 1`, Lean — `D(0) = 1` (запись C24). Поэтому `Mmat` — матрица
статьи (без множителей `D_±(1)`); в Lean `𝔘⁰(ρ) c(ξ,ζ) = (0, 0, 𝔐(ρ)(D_+(1)ξ, D_-(1)ζ))`. -/

@[expose] public noncomputable section

namespace Involution
namespace GeneralBC

/-- `χ_+`: `cos` при `a(0) > 0` (`ε = 1`), иначе `sin`. -/
def chiP (a : ℝ → ℝ) (z : ℂ) : ℂ := if 0 < a 0 then Complex.cos z else Complex.sin z

/-- `χ_+'`: производная `χ_+` по аргументу. -/
def chiP' (a : ℝ → ℝ) (z : ℂ) : ℂ := if 0 < a 0 then -Complex.sin z else Complex.cos z

/-- `χ_-`: `sin` при `a(0) > 0`, иначе `cos`. -/
def chiM (a : ℝ → ℝ) (z : ℂ) : ℂ := if 0 < a 0 then Complex.sin z else Complex.cos z

/-- `χ_-'`: производная `χ_-` по аргументу. -/
def chiM' (a : ℝ → ℝ) (z : ℂ) : ℂ := if 0 < a 0 then Complex.cos z else -Complex.sin z

/-- Вектор `c(ξ,ζ)` формул Эйлера (лемма `lem:kernel`): координаты решения из главных частей
в базисе столбцов `W 𝐃 E`. -/
def cvec (a : ℝ → ℝ) (ξ ζ : ℂ) : Fin 4 → ℂ :=
  if 0 < a 0 then ![ξ / 2, ξ / 2, -(Complex.I * ζ / 2), Complex.I * ζ / 2]
  else ![-(Complex.I * ξ / 2), Complex.I * ξ / 2, ζ / 2, ζ / 2]

/-- Пара главных частей `𝐲⁰(x)` (формула `(Ψ)` статьи) с амплитудами `D_±(x)` нормировки Lean:
`(ξ D_+ χ_+ u_+ + ζ D_- χ_- u_-, ξ D_+ τ_+ χ_+' u_+ + ζ D_- τ_- χ_-' u_-)`, `u_± = (1, ±k)`. -/
def yPrin (a : ℝ → ℝ) (ξ ζ ρ : ℂ) (x : ℝ) : Fin 4 → ℂ :=
  let k : ℂ := (kfun a x : ℝ)
  let fp : ℂ := ξ * (Damp a 1 x : ℂ) * chiP a (ρ * (tPhase a 1 x : ℂ))
  let fm : ℂ := ζ * (Damp a (-1) x : ℂ) * chiM a (ρ * (tPhase a (-1) x : ℂ))
  let gp : ℂ := ξ * (Damp a 1 x : ℂ) * (tau a 1 x : ℂ) * chiP' a (ρ * (tPhase a 1 x : ℂ))
  let gm : ℂ := ζ * (Damp a (-1) x : ℂ) * (tau a (-1) x : ℂ) * chiM' a (ρ * (tPhase a (-1) x : ℂ))
  ![fp + fm, k * (fp - fm), gp + gm, k * (gp - gm)]

open Classical in
/-- Матрица `𝔐(ρ)` (формула (M) статьи, `ν(1) = ϰ`, `τ_±(1) = ω_±`). Строка `j`:
`(Q_j^+ χ_+, Q_j^- χ_-)` при `κ_j = 0`, `(ω_+ P_j^+ χ_+', ω_- P_j^- χ_-')` при `κ_j = 1`. -/
def Mmat (a : ℝ → ℝ) (U : Forms) (ρ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun j c =>
    if U.HasDeriv j then
      (if c = 0 then (omega a 1 : ℂ) * Pc a U j 1 * chiP' a (ρ * (ell a 1 : ℂ))
       else (omega a (-1) : ℂ) * Pc a U j (-1) * chiM' a (ρ * (ell a (-1) : ℂ)))
    else
      (if c = 0 then Qc a U j 1 * chiP a (ρ * (ell a 1 : ℂ))
       else Qc a U j (-1) * chiM a (ρ * (ell a (-1) : ℂ)))

/-- Постоянная `J_U` статьи (нормировка `D(1) = 1`): `2ϰ J_0`, `−2 ω_+ ω_- ϰ J_1`, `−ε`. -/
def JU (a : ℝ → ℝ) (U : Forms) : ℂ :=
  match U.kind with
  | Forms.Kind.k00 => 2 * (varkappa a : ℂ) * U.J0
  | Forms.Kind.k11 => -2 * (omega a 1 : ℂ) * (omega a (-1) : ℂ) * (varkappa a : ℂ) * U.J1
  | Forms.Kind.k10 => -(eps a : ℂ)

/-- `c_U` статьи (нормировка `D(1) = 1`): `16 ε τ_ε(0) D_+(0) D_-(0) J_U`, где
`D_±(0)_{статьи} = 1 / D_±(1)_{Lean}`; равна `cU / (D_+(1) D_-(1))²`. -/
def cUpaper (a : ℝ → ℝ) (U : Forms) : ℂ :=
  16 * (eps a : ℂ) * (tau0 a (eps a) : ℂ) *
    ((Damp a 1 1 : ℂ) * (Damp a (-1) 1 : ℂ))⁻¹ * JU a U

end GeneralBC
end Involution

