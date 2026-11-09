module

public import Involution.Estimates.GeneralBCRegularityBridge
public import Involution.Estimates.GeneralBCRegularityEntire
public import Involution.Folding.GeneralBCFoldMain
public import Involution.Folding.GeneralBCKernelMain

/-! # Теорема thm:eig, часть 1: `Δ ≢ 0` и локализация собственных значений (пакет G6)

Вывод леммы lem:det введён предикатом `DetPrincipalPart` (гипотеза, её доказывает пакет G4).
Здесь: `cStar ≠ 0`, оценка `Δ(ρ²) ≠ 0` вне полосы `|Im ρ| < h₀` для больших `|ρ|`,
`Δ ≢ 0` (шаг 1 доказательства) и утверждение (a) теоремы thm:eig.

Ветвь корня: `lam ^ (1/2 : ℂ)` (главная, `Re ≥ 0`); `|Im √λ|` от выбора знака корня не зависит. -/

@[expose] public noncomputable section

open Set

namespace Involution
namespace GeneralBC

/-- Вывод леммы lem:det: `ρ^{1-κ₁-κ₂} Δ(ρ²) = c_∗ (F(ρ) + η(ρ))`, где `η` голоморфна при
`ρ ≠ 0` и `|η(ρ)| e^{-L|Im ρ|} → 0`. -/
def DetPrincipalPart (a : ℝ → ℝ) (U : Forms) : Prop :=
  ∃ η : ℂ → ℂ, DifferentiableOn ℂ η {0}ᶜ ∧
    (∀ ρ : ℂ, ρ ≠ 0 →
      ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) = cStar a U * (Fchar a U ρ + η ρ)) ∧
    ∀ ε > 0, ∃ r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ → ‖η ρ‖ * Real.exp (-(Ltot a) * |ρ.im|) ≤ ε

/-- `c_∗ ≠ 0`. -/
theorem cStar_ne_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) : cStar a U ≠ 0 := by
  rw [cStar_eq_cU h]
  have t1 : (tau0 a 1 : ℂ) ≠ 0 := by
    exact_mod_cast (tau0_pos h 1 (Or.inl rfl)).ne'
  have t2 : (tau0 a (-1) : ℂ) ≠ 0 := by
    exact_mod_cast (tau0_pos h (-1) (Or.inr rfl)).ne'
  exact div_ne_zero (cU_ne_zero h hU) (mul_ne_zero (mul_ne_zero (by norm_num) t1) t2)

/-- Для больших `|ρ|` вне полосы `|Im ρ| < h₀` имеем `Δ(ρ²) ≠ 0`. -/
theorem delta_sq_ne_zero_far {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (hreg : Regular a U) (hdet : DetPrincipalPart a U) :
    ∃ h₀ r : ℝ, 1 ≤ h₀ ∧ 0 < r ∧ ∀ ρ : ℂ, r ≤ ‖ρ‖ → h₀ ≤ |ρ.im| → Delta a U (ρ ^ 2) ≠ 0 := by
  obtain ⟨h₀, h1, hlow, -⟩ := lem_F_ac ⟨m, κ, h⟩ hreg
  obtain ⟨η, -, hη, hsmall⟩ := hdet
  have hE : 0 < ‖theta a U‖ := norm_pos_iff.2 hreg
  obtain ⟨r₀, hr₀⟩ := hsmall (‖theta a U‖ / 4) (by positivity)
  refine ⟨h₀, max r₀ 1, h1, by positivity, fun ρ hρ him hz => ?_⟩
  have hρ0 : ρ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hρ
    exact absurd (le_trans (le_max_right _ _) hρ) (by norm_num)
  have h2 := hη ρ hρ0
  rw [hz, mul_zero] at h2
  have hc := cStar_ne_zero h hU
  have h3 : Fchar a U ρ + η ρ = 0 := by
    rcases mul_eq_zero.1 h2.symm with h | h
    · exact absurd h hc
    · exact h
  have hF : ‖Fchar a U ρ‖ = ‖η ρ‖ := by
    have : Fchar a U ρ = -η ρ := eq_neg_of_add_eq_zero_left h3
    rw [this, norm_neg]
  have hlo := hlow ρ him
  have hsm := hr₀ ρ (le_trans (le_max_left _ _) hρ)
  set E := Real.exp (Ltot a * |ρ.im|) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hexp : Real.exp (-(Ltot a) * |ρ.im|) * E = 1 := by
    rw [hEdef, ← Real.exp_add]; simp
  have : ‖η ρ‖ ≤ ‖theta a U‖ / 4 * E := by
    have h5 : ‖η ρ‖ = ‖η ρ‖ * Real.exp (-(Ltot a) * |ρ.im|) * E := by
      rw [mul_assoc, mul_comm (Real.exp _) E, ← mul_assoc]
      have := hexp
      calc ‖η ρ‖ = ‖η ρ‖ * (Real.exp (-(Ltot a) * |ρ.im|) * E) := by rw [this, mul_one]
        _ = _ := by ring
    rw [h5]
    exact mul_le_mul_of_nonneg_right hsm hEpos.le
  rw [← hF] at this
  nlinarith [mul_pos hE hEpos]

/-- Шаг 1 доказательства thm:eig: `Δ` не равна тождественно нулю. -/
theorem delta_not_identically_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (hreg : Regular a U) (hdet : DetPrincipalPart a U) :
    ∃ lam : ℂ, Delta a U lam ≠ 0 := by
  obtain ⟨h₀, r, h1, hr, H⟩ := delta_sq_ne_zero_far h hU hreg hdet
  set X : ℝ := max r h₀ with hX
  refine ⟨((X : ℂ) * Complex.I) ^ 2, H _ ?_ ?_⟩
  · simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    exact le_trans (le_max_left _ _) (le_abs_self _)
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    exact le_trans (le_max_right _ _) (le_abs_self _)

/-- thm:eig (a): существуют `h > 0` и `R`, при которых каждое собственное значение `λ` с
`‖λ‖ ≥ R` удовлетворяет `|Im λ^{1/2}| ≤ h`. -/
theorem thm_eig_a {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (hreg : Regular a U) (hdet : DetPrincipalPart a U) :
    ∃ h' R : ℝ, 0 < h' ∧ ∀ lam : ℂ, IsEigenvalue a U lam → R ≤ ‖lam‖ →
      |(lam ^ (1 / 2 : ℂ)).im| ≤ h' := by
  obtain ⟨h₀, r, h1, hr, H⟩ := delta_sq_ne_zero_far h hU hreg hdet
  refine ⟨h₀, r ^ 2, by linarith, fun lam hev hlam => ?_⟩
  have hz : Delta a U lam = 0 := (isEigenvalue_iff_Delta_eq_zero ⟨m, κ, h⟩).1 hev
  by_contra hcon
  rw [not_le] at hcon
  apply H (lam ^ (1 / 2 : ℂ))
  · have hn : ‖lam ^ (1 / 2 : ℂ)‖ ^ 2 = ‖lam‖ := by
      rw [← norm_pow, cpow_half_sq]
    by_contra hlt
    rw [not_le] at hlt
    have : ‖lam‖ < r ^ 2 := by
      rw [← hn]; exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
    linarith
  · exact hcon.le
  · rw [cpow_half_sq]; exact hz

end GeneralBC
end Involution
