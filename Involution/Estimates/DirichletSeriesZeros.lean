module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Нули функций задачи Дирихле: серии и кратности.
* `dirCS a b ρ = cos(ρ a) sin(ρ b)` и `dirSC a b ρ = sin(ρ a) cos(ρ b)` (вид `F` при `ε = ±1`).
* Нули — объединение двух серий вещественных точек (предложение `prop:dir` статьи).
* Нуль кратности не 1 — это общий нуль обоих сомножителей (`analyticOrderAt`). -/

@[expose] public noncomputable section

namespace Involution

/-- Функция `ρ ↦ cos(ρ a) sin(ρ b)`. -/
def dirCS (a b : ℝ) (ρ : ℂ) : ℂ := Complex.cos (ρ * a) * Complex.sin (ρ * b)

/-- Функция `ρ ↦ sin(ρ a) cos(ρ b)`. -/
def dirSC (a b : ℝ) (ρ : ℂ) : ℂ := Complex.sin (ρ * a) * Complex.cos (ρ * b)

lemma dirSC_eq_dirCS (a b : ℝ) : dirSC a b = dirCS b a := by
  funext ρ; simp [dirSC, dirCS, mul_comm]

/-- Порядок нуля `ρ ↦ cos(ρ a)`: единица в нуле, иначе нуль. -/
lemma analyticOrderAt_cos_mul (a : ℝ) (ha : a ≠ 0) (ρ : ℂ) :
    analyticOrderAt (fun z : ℂ => Complex.cos (z * a)) ρ =
      if Complex.cos (ρ * a) = 0 then 1 else 0 := by
  have hf : AnalyticAt ℂ (fun z : ℂ => Complex.cos (z * a)) ρ := by fun_prop
  split_ifs with h
  · apply hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h
    have : deriv (fun z : ℂ => Complex.cos (z * a)) ρ = -Complex.sin (ρ * a) * a := by
      have h1 : HasDerivAt (fun z : ℂ => z * (a : ℂ)) (a : ℂ) ρ := by
        simpa using (hasDerivAt_id ρ).mul_const (a : ℂ)
      have := ((Complex.hasDerivAt_cos (ρ * a)).comp ρ h1).deriv
      simp at this
      simp [mul_comm]
    rw [this]
    have hs : Complex.sin (ρ * a) ≠ 0 := by
      intro hs
      have := Complex.sin_sq_add_cos_sq (ρ * a)
      rw [hs, h] at this; simp at this
    simp [hs, ha]
  · exact hf.analyticOrderAt_eq_zero.mpr h

/-- Порядок нуля `ρ ↦ sin(ρ b)`. -/
lemma analyticOrderAt_sin_mul (b : ℝ) (hb : b ≠ 0) (ρ : ℂ) :
    analyticOrderAt (fun z : ℂ => Complex.sin (z * b)) ρ =
      if Complex.sin (ρ * b) = 0 then 1 else 0 := by
  have hf : AnalyticAt ℂ (fun z : ℂ => Complex.sin (z * b)) ρ := by fun_prop
  split_ifs with h
  · apply hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h
    have : deriv (fun z : ℂ => Complex.sin (z * b)) ρ = Complex.cos (ρ * b) * b := by
      have h1 : HasDerivAt (fun z : ℂ => z * (b : ℂ)) (b : ℂ) ρ := by
        simpa using (hasDerivAt_id ρ).mul_const (b : ℂ)
      have := ((Complex.hasDerivAt_sin (ρ * b)).comp ρ h1).deriv
      simp [mul_comm] at this
      simp [mul_comm]
    rw [this]
    have hs : Complex.cos (ρ * b) ≠ 0 := by
      intro hs
      have := Complex.sin_sq_add_cos_sq (ρ * b)
      rw [hs, h] at this; simp at this
    simp [hs, hb]
  · exact hf.analyticOrderAt_eq_zero.mpr h

/-- В нуле `dirCS` кратность не равна 1 тогда и только тогда, когда обращаются в нуль оба
сомножителя. -/
lemma dirCS_order_ne_one_iff (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (ρ : ℂ)
    (hF : dirCS a b ρ = 0) :
    analyticOrderAt (dirCS a b) ρ ≠ 1 ↔
      Complex.cos (ρ * a) = 0 ∧ Complex.sin (ρ * b) = 0 := by
  have hm : dirCS a b = (fun z : ℂ => Complex.cos (z * a)) * (fun z : ℂ => Complex.sin (z * b)) :=
    rfl
  have h1 : AnalyticAt ℂ (fun z : ℂ => Complex.cos (z * a)) ρ := by fun_prop
  have h2 : AnalyticAt ℂ (fun z : ℂ => Complex.sin (z * b)) ρ := by fun_prop
  rw [hm, analyticOrderAt_mul h1 h2, analyticOrderAt_cos_mul a ha, analyticOrderAt_sin_mul b hb]
  have hF' : Complex.cos (ρ * a) = 0 ∨ Complex.sin (ρ * b) = 0 := mul_eq_zero.mp hF
  by_cases hc : Complex.cos (ρ * a) = 0 <;> by_cases hs : Complex.sin (ρ * b) = 0 <;>
    simp_all

/-- Нули `dirCS a b` при `a, b ≠ 0`: серии `(2k+1)π/(2a)` и `jπ/b`. -/
theorem dirCS_eq_zero_iff (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (ρ : ℂ) :
    dirCS a b ρ = 0 ↔ (∃ k : ℤ, ρ = (((2 * k + 1) * Real.pi / (2 * a) : ℝ) : ℂ)) ∨
      (∃ j : ℤ, ρ = ((j * Real.pi / b : ℝ) : ℂ)) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold dirCS
  rw [mul_eq_zero, Complex.cos_eq_zero_iff, Complex.sin_eq_zero_iff]
  constructor
  · rintro (⟨k, hk⟩ | ⟨j, hj⟩)
    · left; refine ⟨k, ?_⟩
      push_cast; rw [eq_div_iff (by simp [ha'])]; linear_combination 2 * hk
    · right; refine ⟨j, ?_⟩
      push_cast; rw [eq_div_iff hb']; linear_combination hj
  · rintro (⟨k, hk⟩ | ⟨j, hj⟩)
    · left; refine ⟨k, ?_⟩
      rw [hk]; push_cast; field_simp
    · right; refine ⟨j, ?_⟩
      rw [hj]; push_cast; field_simp

end Involution
