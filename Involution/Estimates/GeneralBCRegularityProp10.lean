module

public import Involution.Estimates.GeneralBCRegularityBridge
public import Involution.Estimates.ReflectionZerosMain
public import Involution.Folding.GeneralBCAdmissible

/-! # `prop:10` в терминах задачи (пакет G5)

Для вида `(1,0)` при `𝒜 ≠ ℬ`: `F = ε(ℬ−𝒜)/2 · H`, `H(ρ) = cos ρL + γ cos ρd`,
`γ = ε(𝒜+ℬ)/(ℬ−𝒜)`. Из W6 (`reflH_zeros`) следуют: все нули `F` лежат в кругах радиуса `r`
вокруг `π(n − 1/2)/L`, в каждом круге ровно один нуль, каждый нуль простой, нули вещественны
при `γ ∈ ℝ`, `StronglyRegular a U`. -/

@[expose] public noncomputable section

open Set Metric

namespace Involution
namespace GeneralBC

variable {a : ℝ → ℝ} {U : Forms}

/-- Параметр `γ` предложения `prop:10`. -/
def gam10 (a : ℝ → ℝ) (U : Forms) : ℂ :=
  (eps a : ℂ) * (calA a U + calB a U) / (calB a U - calA a U)

/-- Множитель `ε(ℬ−𝒜)/2`. -/
def coef10 (a : ℝ → ℝ) (U : Forms) : ℂ := (eps a : ℂ) * (calB a U - calA a U) / 2

theorem coef10_ne_zero (hne : calA a U ≠ calB a U) : coef10 a U ≠ 0 := by
  have : (eps a : ℂ) ≠ 0 := by exact_mod_cast eps_ne_zero a
  exact div_ne_zero (mul_ne_zero this (sub_ne_zero.2 hne.symm)) two_ne_zero

/-- Мост: для вида `(1,0)` и `𝒜 ≠ ℬ` имеем `F = ε(ℬ−𝒜)/2 · H`. -/
theorem Fchar_k10_eq (a : ℝ → ℝ) (U : Forms) (hk : U.kind = Forms.Kind.k10)
    (hne : calA a U ≠ calB a U) (ρ : ℂ) :
    Fchar a U ρ = ((eps a : ℂ) * (calB a U - calA a U) / 2) *
      reflH (Ltot a) (dlt a) ((eps a : ℂ) * (calA a U + calB a U) / (calB a U - calA a U)) ρ := by
  have hBA : calB a U - calA a U ≠ 0 := sub_ne_zero.2 hne.symm
  have hL : ρ * (Ltot a : ℂ) = ρ * (ell a 1 : ℂ) + ρ * (ell a (-1) : ℂ) := by
    simp only [Ltot]; push_cast; ring
  have hd : ρ * (dlt a : ℂ) = ρ * (ell a 1 : ℂ) - ρ * (ell a (-1) : ℂ) := by
    simp only [dlt]; push_cast; ring
  have h1 : Complex.cos (ρ * (ell a 1 : ℂ)) * Complex.cos (ρ * (ell a (-1) : ℂ)) =
      (Complex.cos (ρ * (Ltot a : ℂ)) + Complex.cos (ρ * (dlt a : ℂ))) / 2 := by
    rw [hL, hd, Complex.cos_add, Complex.cos_sub]; ring
  have h2 : Complex.sin (ρ * (ell a 1 : ℂ)) * Complex.sin (ρ * (ell a (-1) : ℂ)) =
      (Complex.cos (ρ * (dlt a : ℂ)) - Complex.cos (ρ * (Ltot a : ℂ))) / 2 := by
    rw [hL, hd, Complex.cos_add, Complex.cos_sub]; ring
  unfold Fchar reflH
  by_cases hε : 0 < a 0
  · have he : eps a = 1 := by simp [eps, hε]
    simp only [hε, ite_true, hk, he]
    rw [mul_assoc, mul_assoc, h2, h1]; push_cast; field_simp; ring
  · have he : eps a = -1 := by simp [eps, hε]
    simp only [hε, ite_false, hk, he]
    rw [mul_assoc, mul_assoc, h2, h1]; push_cast; field_simp; ring

theorem Fchar_eq_coef_mul (hk : U.kind = Forms.Kind.k10) (hne : calA a U ≠ calB a U) :
    Fchar a U = fun ρ => coef10 a U * reflH (Ltot a) (dlt a) (gam10 a U) ρ :=
  funext (Fchar_k10_eq a U hk hne)

theorem Fchar_zero_iff (hk : U.kind = Forms.Kind.k10) (hne : calA a U ≠ calB a U) (ρ : ℂ) :
    Fchar a U ρ = 0 ↔ reflH (Ltot a) (dlt a) (gam10 a U) ρ = 0 := by
  rw [Fchar_eq_coef_mul hk hne]
  exact mul_eq_zero.trans (or_iff_right (coef10_ne_zero hne))

theorem order_Fchar_eq (hk : U.kind = Forms.Kind.k10) (hne : calA a U ≠ calB a U) (z : ℂ) :
    analyticOrderAt (Fchar a U) z = analyticOrderAt (reflH (Ltot a) (dlt a) (gam10 a U)) z := by
  have hH : AnalyticAt ℂ (reflH (Ltot a) (dlt a) (gam10 a U)) z := by
    unfold reflH; fun_prop
  have h3 : analyticOrderAt (fun _ : ℂ => coef10 a U) z = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.2 (coef10_ne_zero hne)
  have := analyticOrderAt_mul (𝕜 := ℂ) (f := fun _ : ℂ => coef10 a U)
    (g := reflH (Ltot a) (dlt a) (gam10 a U)) (z₀ := z) analyticAt_const hH
  rw [Fchar_eq_coef_mul hk hne]
  have e : (fun ρ => coef10 a U * reflH (Ltot a) (dlt a) (gam10 a U) ρ) =
      (fun _ : ℂ => coef10 a U) * reflH (Ltot a) (dlt a) (gam10 a U) := rfl
  rw [e]; simpa [h3] using this

/-- Условие `prop:10` на радиус `r`. -/
def Prop10Cond (a : ℝ → ℝ) (U : Forms) (r : ℝ) : Prop :=
  0 < r ∧ r < Real.pi / (2 * Ltot a) ∧
    ‖gam10 a U‖ * Real.cosh (|dlt a| * r) < Real.sin (Ltot a * r)

variable {m κ : ℝ}

/-- prop:10 (i): каждый нуль `F` лежит в одном из кругов. -/
theorem prop10_zeros_in_balls (h : HypH a m κ) (_hU : AdmissibleForms U)
    (hk : U.kind = Forms.Kind.k10) (hne : calA a U ≠ calB a U) {r : ℝ}
    (hr : Prop10Cond a U r) :
    ∀ ρ : ℂ, Fchar a U ρ = 0 → ∃ n : ℤ,
      ‖ρ - ((Real.pi * (n - 1 / 2) / Ltot a : ℝ) : ℂ)‖ < r := by
  intro ρ hρ
  obtain ⟨n, hn⟩ := (reflH_zeros (Ltot_pos h) (abs_dlt_lt_Ltot h) hr.1 hr.2.1 hr.2.2).1 ρ
    ((Fchar_zero_iff hk hne ρ).1 hρ)
  exact ⟨n, by simpa [mem_ball, dist_eq_norm, reflCenter] using hn⟩

/-- prop:10 (ii): в каждом круге ровно один нуль `F`. -/
theorem prop10_unique_zero (h : HypH a m κ) (_hU : AdmissibleForms U)
    (hk : U.kind = Forms.Kind.k10) (hne : calA a U ≠ calB a U) {r : ℝ}
    (hr : Prop10Cond a U r) (n : ℤ) :
    ∃! ρ : ℂ, Fchar a U ρ = 0 ∧ ‖ρ - ((Real.pi * (n - 1 / 2) / Ltot a : ℝ) : ℂ)‖ < r := by
  obtain ⟨w, hw, hw0, -, hu⟩ :=
    (reflH_zeros (Ltot_pos h) (abs_dlt_lt_Ltot h) hr.1 hr.2.1 hr.2.2).2.1 n
  have hc : ∀ z : ℂ, z ∈ ball (reflCenter (Ltot a) n : ℂ) r ↔
      ‖z - ((Real.pi * (n - 1 / 2) / Ltot a : ℝ) : ℂ)‖ < r := fun z => by
    simp [mem_ball, dist_eq_norm, reflCenter]
  refine ⟨w, ⟨(Fchar_zero_iff hk hne w).2 hw0, (hc w).1 hw⟩, fun z hz => ?_⟩
  exact hu z ((hc z).2 hz.2) ((Fchar_zero_iff hk hne z).1 hz.1)

/-- prop:10 (iii): каждый нуль `F` в круге простой. -/
theorem prop10_simple_in_ball (h : HypH a m κ) (_hU : AdmissibleForms U)
    (hk : U.kind = Forms.Kind.k10) (hne : calA a U ≠ calB a U) {r : ℝ}
    (hr : Prop10Cond a U r) (n : ℤ) (ρ : ℂ) (hρ : Fchar a U ρ = 0)
    (_hb : ‖ρ - ((Real.pi * (n - 1 / 2) / Ltot a : ℝ) : ℂ)‖ < r) :
    analyticOrderAt (Fchar a U) ρ = 1 := by
  rw [order_Fchar_eq hk hne]
  exact reflH_zero_order_one (Ltot_pos h) (abs_dlt_lt_Ltot h).le hr.1 hr.2.1.le hr.2.2
    ((Fchar_zero_iff hk hne ρ).1 hρ)

/-- prop:10: все нули `F` простые. -/
theorem prop10_all_simple (h : HypH a m κ) (_hU : AdmissibleForms U)
    (hk : U.kind = Forms.Kind.k10) (hne : calA a U ≠ calB a U) {r : ℝ}
    (hr : Prop10Cond a U r) (ρ : ℂ) (hρ : Fchar a U ρ = 0) :
    analyticOrderAt (Fchar a U) ρ = 1 := by
  obtain ⟨n, hn⟩ := prop10_zeros_in_balls h _hU hk hne hr ρ hρ
  exact prop10_simple_in_ball h _hU hk hne hr n ρ hρ hn

/-- prop:10: задача сильно регулярна. -/
theorem prop10_stronglyRegular (h : HypH a m κ) (_hU : AdmissibleForms U)
    (hk : U.kind = Forms.Kind.k10) (hne : calA a U ≠ calB a U) {r : ℝ}
    (hr : Prop10Cond a U r) : StronglyRegular a U := by
  have hF := Fchar_k10_eq a U hk hne
  exact ⟨(regular_iff_of_k10 a U hk).2 hne,
    scaled_separated (Ltot_pos h) (abs_dlt_lt_Ltot h) hr.1 hr.2.1 hr.2.2 (coef10_ne_zero hne) hF,
    scaled_eventually_simple (Ltot_pos h) (abs_dlt_lt_Ltot h) hr.1 hr.2.1 hr.2.2
      (coef10_ne_zero hne) hF⟩

/-- prop:10, вещественный случай. -/
theorem prop10_real (h : HypH a m κ) (_hU : AdmissibleForms U)
    (hk : U.kind = Forms.Kind.k10) (hne : calA a U ≠ calB a U) {r : ℝ}
    (hr : Prop10Cond a U r) (hreal : (gam10 a U).im = 0) (ρ : ℂ) (hρ : Fchar a U ρ = 0) :
    ρ.im = 0 :=
  reflH_zero_real (Ltot_pos h) (abs_dlt_lt_Ltot h).le hr.1 hr.2.1.le hr.2.2 hreal
    ((Fchar_zero_iff hk hne ρ).1 hρ)

/-- prop:10, достаточное условие существования `r`. -/
theorem prop10_exists_radius (h : HypH a m κ) (_hU : AdmissibleForms U)
    (_hk : U.kind = Forms.Kind.k10) (_hne : calA a U ≠ calB a U)
    (hγ : ‖gam10 a U‖ * Real.cosh (Real.pi * |dlt a| / (2 * Ltot a)) < 1) :
    ∃ r : ℝ, Prop10Cond a U r := by
  obtain ⟨r, h1, h2, h3⟩ := exists_radius (Ltot_pos h) hγ
  exact ⟨r, h1, h2, h3⟩

end GeneralBC
end Involution
