module

public import Involution.Estimates.GeneralBCRegularityBridge

/-! # Единственность коэффициентов экспоненциального многочлена (пакет G5)

Для `L > 0`, `|d| < L` частоты `±L` отличны друг от друга и от `±d`. Коэффициенты при `e^{±iρL}`
определены однозначно всегда; при `d ≠ 0` однозначны и коэффициенты при `e^{±iρd}`, при
`d = 0` частоты `±d` сливаются и определена лишь сумма `θ_d⁺ + θ_d⁻`.
Следствие: `Regular a U` равносильно ненулевому коэффициенту при `e^{iρL}` в любом
представлении `Fchar a U`. -/

@[expose] public noncomputable section

open Complex Filter Topology

namespace Involution

theorem expPoly_neg (θp θm θdp θdm : ℂ) (L d : ℝ) (ρ : ℂ) :
    expPoly θp θm θdp θdm L d (-ρ) = expPoly θm θp θdm θdp L d ρ := by
  unfold expPoly
  have e1 : ∀ c : ℝ, I * -ρ * c = -(I * ρ * c) := fun c => by ring
  have e2 : ∀ c : ℝ, -(I * -ρ * c) = I * ρ * c := fun c => by ring
  simp only [e1, neg_neg]; ring

/-- Старший коэффициент равен нулю, если `F ≡ 0`. -/
theorem coeff_plus_eq_zero {θp θm θdp θdm : ℂ} {L d : ℝ} (hL : 0 < L) (hd : |d| < L)
    (h : ∀ ρ, expPoly θp θm θdp θdm L d ρ = 0) : θp = 0 := by
  set S := ‖θm‖ + ‖θdp‖ + ‖θdm‖ with hS
  set ε := L - |d| with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have key : ∀ t : ℝ, 0 ≤ t → ‖θp‖ ≤ S * Real.exp (-ε * t) := by
    intro t ht
    set ρ : ℂ := -((t : ℂ) * I) with hρ
    have him : ρ.im = -t := by simp [hρ]
    have h0 := h ρ
    unfold expPoly at h0
    have e : θp * cexp (I * ρ * L) = -(θm * cexp (-(I * ρ * L)) + θdp * cexp (I * ρ * d) +
        θdm * cexp (-(I * ρ * d))) := by linear_combination h0
    have hn := congrArg norm e
    rw [norm_neg, norm_mul, norm_cexp_I_mul, him] at hn
    have n3 := norm_add₃_le (a := θm * cexp (-(I * ρ * L))) (b := θdp * cexp (I * ρ * d))
      (c := θdm * cexp (-(I * ρ * d)))
    rw [norm_mul, norm_mul, norm_mul, norm_cexp_neg_I_mul, norm_cexp_I_mul,
      norm_cexp_neg_I_mul, him] at n3
    have b1 : Real.exp (L * -t) ≤ Real.exp (|d| * t) := Real.exp_le_exp.2 (by
      have := mul_nonneg hL.le ht; have := mul_nonneg (abs_nonneg d) ht; linarith)
    have b2 : Real.exp (-(d * -t)) ≤ Real.exp (|d| * t) :=
      Real.exp_le_exp.2 (by nlinarith [le_abs_self d, neg_abs_le d])
    have b3 : Real.exp (d * -t) ≤ Real.exp (|d| * t) :=
      Real.exp_le_exp.2 (by nlinarith [le_abs_self d, neg_abs_le d])
    have b0 : Real.exp (-(L * -t)) = Real.exp (L * t) := by congr 1; ring
    rw [b0] at hn
    have hm : ‖θp‖ * Real.exp (L * t) ≤ S * Real.exp (|d| * t) := by
      rw [hS]
      have := mul_le_mul_of_nonneg_left b1 (norm_nonneg θm)
      have := mul_le_mul_of_nonneg_left b2 (norm_nonneg θdp)
      have := mul_le_mul_of_nonneg_left b3 (norm_nonneg θdm)
      nlinarith
    have hpos := Real.exp_pos (L * t)
    have e2 : Real.exp (|d| * t) = Real.exp (L * t) * Real.exp (-ε * t) := by
      rw [← Real.exp_add]; congr 1; rw [hε]; ring
    rw [e2] at hm
    nlinarith
  have hlim : Tendsto (fun t : ℝ => S * Real.exp (-ε * t)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => Real.exp (-ε * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    simpa using this.const_mul S
  have := ge_of_tendsto hlim (eventually_atTop.2 ⟨0, fun t ht => key t ht⟩)
  exact norm_le_zero_iff.1 this

/-- Единственность коэффициентов при `e^{±iρL}` и суммы `θ_d⁺ + θ_d⁻`. -/
theorem expPoly_coeff_unique {θp θm θdp θdm θp' θm' θdp' θdm' : ℂ} {L d : ℝ} (hL : 0 < L)
    (hd : |d| < L)
    (h : ∀ ρ, expPoly θp θm θdp θdm L d ρ = expPoly θp' θm' θdp' θdm' L d ρ) :
    θp = θp' ∧ θm = θm' ∧ θdp + θdm = θdp' + θdm' := by
  have h0 : ∀ ρ, expPoly (θp - θp') (θm - θm') (θdp - θdp') (θdm - θdm') L d ρ = 0 := by
    intro ρ; rw [← expPoly_sub, h ρ, sub_self]
  have h1 := coeff_plus_eq_zero hL hd h0
  have h2 : θm - θm' = 0 := by
    refine coeff_plus_eq_zero (θp := θm - θm') (θm := θp - θp') (θdp := θdm - θdm')
      (θdm := θdp - θdp') hL hd (fun ρ => ?_)
    rw [← expPoly_neg]; exact h0 _
  have h3 := h0 0
  unfold expPoly at h3
  simp only [mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at h3
  refine ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2, ?_⟩
  rw [h1, h2] at h3
  linear_combination h3

/-- При `d ≠ 0` однозначны и `θ_d⁺`, `θ_d⁻`. -/
theorem expPoly_coeff_unique_d {θp θm θdp θdm θp' θm' θdp' θdm' : ℂ} {L d : ℝ} (hL : 0 < L)
    (hd : |d| < L) (hd0 : d ≠ 0)
    (h : ∀ ρ, expPoly θp θm θdp θdm L d ρ = expPoly θp' θm' θdp' θdm' L d ρ) :
    θp = θp' ∧ θm = θm' ∧ θdp = θdp' ∧ θdm = θdm' := by
  obtain ⟨h1, h2, h3⟩ := expPoly_coeff_unique hL hd h
  refine ⟨h1, h2, ?_⟩
  have h0 := h (-I)
  subst h1 h2
  unfold expPoly at h0
  have e1 : I * -I * (d : ℂ) = d := by simp
  have e2 : -(I * -I * (d : ℂ)) = -d := by simp
  have e3 : ∀ c : ℝ, cexp (I * -I * (c : ℂ)) = (Real.exp c : ℂ) := by
    intro c; rw [Complex.ofReal_exp]; congr 1; simp
  have e4 : ∀ c : ℝ, cexp (-(I * -I * (c : ℂ))) = (Real.exp (-c) : ℂ) := by
    intro c; rw [Complex.ofReal_exp]; congr 1; simp
  rw [e3, e4, e3, e4] at h0
  have hne : (Real.exp d : ℂ) - (Real.exp (-d) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact_mod_cast sub_ne_zero.2 (fun e => hd0 (by
      have := Real.exp_injective e; linarith))
  have hc : (θdp - θdp') * ((Real.exp d : ℂ) - (Real.exp (-d) : ℂ)) = 0 := by
    linear_combination h0 - (Real.exp (-d) : ℂ) * h3
  have hdp : θdp = θdp' := sub_eq_zero.1 ((mul_eq_zero.1 hc).resolve_right hne)
  exact ⟨hdp, by rw [hdp] at h3; linear_combination h3⟩

end Involution

namespace Involution
namespace GeneralBC

variable {a : ℝ → ℝ} {U : Forms}

/-- Единственность коэффициентов `Fchar`: любое представление экспоненциальным многочленом
с частотами `±L`, `±d` имеет коэффициенты `θ_+`, `θ_-` задачи. -/
theorem Fchar_coeff_unique (h : Hyp a) {θp θm θdp θdm : ℂ}
    (hF : ∀ ρ, Fchar a U ρ = expPoly θp θm θdp θdm (Ltot a) (dlt a) ρ) :
    θp = thetaPlus a U ∧ θm = thetaMinus a U ∧ θdp + θdm = thetaDPlus a U + thetaDMinus a U := by
  obtain ⟨hL, hd⟩ := Ltot_dlt h
  have := expPoly_coeff_unique (θp := θp) (θm := θm) (θdp := θdp) (θdm := θdm)
    (θp' := thetaPlus a U) (θm' := thetaMinus a U) (θdp' := thetaDPlus a U)
    (θdm' := thetaDMinus a U) hL hd (fun ρ => by
      rw [← hF, Fchar_eq_expSum]; rfl)
  exact this

/-- При `d ≠ 0` однозначны и `θ_d^±`. -/
theorem Fchar_coeff_unique_d (h : Hyp a) (hd0 : dlt a ≠ 0) {θp θm θdp θdm : ℂ}
    (hF : ∀ ρ, Fchar a U ρ = expPoly θp θm θdp θdm (Ltot a) (dlt a) ρ) :
    θp = thetaPlus a U ∧ θm = thetaMinus a U ∧ θdp = thetaDPlus a U ∧
      θdm = thetaDMinus a U := by
  obtain ⟨hL, hd⟩ := Ltot_dlt h
  exact expPoly_coeff_unique_d (θp := θp) (θm := θm) (θdp := θdp) (θdm := θdm)
    (θp' := thetaPlus a U) (θm' := thetaMinus a U) (θdp' := thetaDPlus a U)
    (θdm' := thetaDMinus a U) hL hd hd0 (fun ρ => by
      rw [← hF, Fchar_eq_expSum]; rfl)

/-- Под (H) `d ≠ 0`, поэтому однозначны все четыре коэффициента. -/
theorem Fchar_coeff_unique_full {m κ : ℝ} (h : HypH a m κ) {θp θm θdp θdm : ℂ}
    (hF : ∀ ρ, Fchar a U ρ = expPoly θp θm θdp θdm (Ltot a) (dlt a) ρ) :
    θp = thetaPlus a U ∧ θm = thetaMinus a U ∧ θdp = thetaDPlus a U ∧
      θdm = thetaDMinus a U :=
  Fchar_coeff_unique_d ⟨m, κ, h⟩ (dlt_ne_zero h) hF

/-- `Regular a U` равносильно ненулевому коэффициенту при `e^{iρL}` в `Fchar`. -/
theorem regular_iff_coeff_ne_zero (h : Hyp a) {θp θm θdp θdm : ℂ}
    (hF : ∀ ρ, Fchar a U ρ = expPoly θp θm θdp θdm (Ltot a) (dlt a) ρ) :
    Regular a U ↔ θp ≠ 0 := by
  rw [(Fchar_coeff_unique h hF).1]; rfl

end GeneralBC
end Involution
