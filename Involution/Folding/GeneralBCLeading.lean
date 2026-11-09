module

public import Involution.Folding.GeneralBC

/-! # Главная часть `F`: разложение по экспонентам и критерий регулярности (C24 шаги 8, 17)

Доказано без ОДУ: для всех `ρ`
`F(ρ) = θ_+ e^{iρL} + θ_- e^{-iρL} + θ_d^+ e^{iρd} + θ_d^- e^{-iρd}`, `θ_- = ±θ_+`,
регулярность по видам форм, формулы `𝒜`, `ℬ` и критерий `a(1) ≠ a(-1)` для форм (E). -/

@[expose] public noncomputable section

open Set

namespace Involution
namespace GeneralBC

private theorem exp_cos_sin (z : ℂ) :
    Complex.cos z = (Complex.exp (z * Complex.I) + (Complex.exp (z * Complex.I))⁻¹) / 2 ∧
    Complex.sin z = ((Complex.exp (z * Complex.I))⁻¹ - Complex.exp (z * Complex.I)) *
      Complex.I / 2 := by
  constructor
  · rw [Complex.cos, ← Complex.exp_neg, neg_mul]
  · rw [Complex.sin, ← Complex.exp_neg, neg_mul]

/-- Разложение шага 8 C24: `F` есть экспоненциальный многочлен с коэффициентами `θ`. -/
theorem Fchar_eq_expSum (a : ℝ → ℝ) (U : Forms) (ρ : ℂ) :
    Fchar a U ρ =
      thetaPlus a U * Complex.exp (Complex.I * ρ * (Ltot a : ℂ)) +
      thetaMinus a U * Complex.exp (-(Complex.I * ρ * (Ltot a : ℂ))) +
      thetaDPlus a U * Complex.exp (Complex.I * ρ * (dlt a : ℂ)) +
      thetaDMinus a U * Complex.exp (-(Complex.I * ρ * (dlt a : ℂ))) := by
  have hL : Complex.I * ρ * (Ltot a : ℂ) =
      (ρ * (ell a 1 : ℂ)) * Complex.I + (ρ * (ell a (-1) : ℂ)) * Complex.I := by
    simp only [Ltot, Complex.ofReal_add]; ring
  have hd : Complex.I * ρ * (dlt a : ℂ) =
      (ρ * (ell a 1 : ℂ)) * Complex.I - (ρ * (ell a (-1) : ℂ)) * Complex.I := by
    simp only [dlt, Complex.ofReal_sub]; ring
  rw [hL, hd]
  obtain ⟨hc1, hs1⟩ := exp_cos_sin (ρ * (ell a 1 : ℂ))
  obtain ⟨hc2, hs2⟩ := exp_cos_sin (ρ * (ell a (-1) : ℂ))
  have hX : Complex.exp ((ρ * (ell a 1 : ℂ)) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hY : Complex.exp ((ρ * (ell a (-1) : ℂ)) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  simp only [Complex.exp_add, Complex.exp_sub, Complex.exp_neg, neg_add, neg_sub]
  generalize Complex.exp ((ρ * (ell a 1 : ℂ)) * Complex.I) = X at *
  generalize Complex.exp ((ρ * (ell a (-1) : ℂ)) * Complex.I) = Y at *
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold Fchar thetaPlus thetaMinus thetaDPlus thetaDMinus sinSign
  by_cases hε : 0 < a 0
  · have he : eps a = 1 := by simp [eps, hε]
    cases hk : U.kind
    all_goals
      simp only [hε, ite_true, he, hc1, hs1, hc2, hs2]
      push_cast
      field_simp
      ring_nf
      try (simp only [hI]; ring)
  · have he : eps a = -1 := by simp [eps, hε]
    cases hk : U.kind
    all_goals
      simp only [hε, ite_false, he, hc1, hs1, hc2, hs2]
      push_cast
      field_simp
      ring_nf
      try (simp only [hI]; ring)

/-- Шаг 8 C24: `θ_- = ±θ_+` (знак `+` для вида `(1,0)`, `−` для `(0,0)`, `(1,1)`). -/
theorem thetaMinus_eq (a : ℝ → ℝ) (U : Forms) :
    thetaMinus a U = thetaPlus a U ∨ thetaMinus a U = -thetaPlus a U := by
  unfold thetaMinus thetaPlus
  cases U.kind
  · right; ring
  · right; ring
  · left; rfl

theorem eps_ne_zero (a : ℝ → ℝ) : eps a ≠ 0 := by
  unfold eps; split_ifs <;> norm_num

/-- Критерий регулярности по видам (C24 утверждение 2, последняя фраза): для видов `(0,0)`,
`(1,1)` — всегда, для вида `(1,0)` — равносильно `𝒜 ≠ ℬ`. -/
theorem regular_iff (a : ℝ → ℝ) (U : Forms) :
    Regular a U ↔ (U.kind = Forms.Kind.k10 → calA a U ≠ calB a U) := by
  have he : (eps a : ℂ) ≠ 0 := by exact_mod_cast eps_ne_zero a
  unfold Regular theta thetaPlus
  cases hk : U.kind
  · simp [Complex.I_ne_zero]
  · simp [Complex.I_ne_zero]
  · simp only [forall_const, ne_eq, div_eq_zero_iff, mul_eq_zero, he, false_or,
      OfNat.ofNat_ne_zero, or_false]
    rw [sub_eq_zero]
    exact not_congr eq_comm

theorem regular_of_k00 (a : ℝ → ℝ) (U : Forms) (hk : U.kind = Forms.Kind.k00) :
    Regular a U :=
  (regular_iff a U).2 fun h => absurd h (by rw [hk]; decide)

theorem regular_of_k11 (a : ℝ → ℝ) (U : Forms) (hk : U.kind = Forms.Kind.k11) :
    Regular a U :=
  (regular_iff a U).2 fun h => absurd h (by rw [hk]; decide)

theorem regular_iff_of_k10 (a : ℝ → ℝ) (U : Forms) (hk : U.kind = Forms.Kind.k10) :
    Regular a U ↔ calA a U ≠ calB a U :=
  ⟨fun h => (regular_iff a U).1 h hk, fun h => (regular_iff a U).2 fun _ => h⟩


/-! ## Формы (E): prop:refl -/

theorem reflForms_kind : reflForms.kind = Forms.Kind.k10 := by
  have h0 : reflForms.HasDeriv 0 := Or.inl (by simp [reflForms])
  have h1 : ¬ reflForms.HasDeriv 1 := by simp [Forms.HasDeriv, reflForms]
  simp [Forms.kind, h0, h1]

theorem calA_reflForms (a : ℝ → ℝ) :
    calA a reflForms = (omega a 1 : ℂ) * (1 - (varkappa a : ℂ) ^ 2) := by
  simp only [calA, Pc, Qc, reflForms]
  push_cast
  simp
  ring

theorem calB_reflForms (a : ℝ → ℝ) :
    calB a reflForms = (omega a (-1) : ℂ) * (1 - (varkappa a : ℂ) ^ 2) := by
  simp only [calB, Pc, Qc, reflForms]
  push_cast
  simp
  ring

/-- Из (H) следует, что `a(1)` и `a(-1)` одного знака (`a` непрерывна и не обращается в нуль). -/
theorem HypH.prod_pos {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) : 0 < a 1 * a (-1) := by
  have hc : ContinuousOn a (Set.uIcc (-1) 1) := h.ac.continuousOn
  have h1 : a 1 ≠ 0 := fun h0 => by
    have := h.lower 1 (by simp); rw [h0] at this; simp at this; linarith [h.m_pos]
  have h2 : a (-1) ≠ 0 := fun h0 => by
    have := h.lower (-1) (by simp); rw [h0] at this; simp at this; linarith [h.m_pos]
  by_contra hneg
  have hlt : a 1 * a (-1) < 0 := lt_of_le_of_ne (not_lt.1 hneg) (mul_ne_zero h1 h2)
  have hz : (0 : ℝ) ∈ Set.uIcc (a (-1)) (a 1) := by
    rcases lt_or_gt_of_ne h1 with hp | hp
    · have : 0 < a (-1) := by nlinarith
      rw [Set.mem_uIcc]; right; exact ⟨hp.le, this.le⟩
    · have : a (-1) < 0 := by nlinarith
      rw [Set.mem_uIcc]; left; exact ⟨this.le, hp.le⟩
  obtain ⟨x, hx, hx0⟩ := intermediate_value_uIcc hc hz
  rw [Set.uIcc_of_le (by norm_num)] at hx
  have := h.lower x hx
  rw [hx0] at this; simp at this; linarith [h.m_pos]

/-- prop:refl: для форм (E) при (H) задача регулярна тогда и только тогда, когда
`a(1) ≠ a(-1)`. -/
theorem regular_reflForms_iff {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) :
    Regular a reflForms ↔ a 1 ≠ a (-1) := by
  have hp := h.prod_pos
  have hpk := h.upper 1 (by simp)
  have h1 : a 1 ≠ 0 := fun h0 => by simp [h0] at hp
  -- ω_+ < ω_-
  have hq0 : 0 < Real.sqrt (a 1 * a (-1)) := Real.sqrt_pos.2 hp
  have hq1 : Real.sqrt (a 1 * a (-1)) < 1 := by
    rw [Real.sqrt_lt' one_pos]; linarith [h.kappa_lt]
  have hw : omega a 1 < omega a (-1) := by
    simp only [omega, tau, sigma]
    simp only [one_mul, neg_one_mul]
    apply inv_strictAnti₀ (Real.sqrt_pos.2 (by linarith))
    apply Real.sqrt_lt_sqrt (by linarith)
    linarith
  -- ϰ² = a(-1)/a(1)
  have hr : 0 ≤ a (-1) / a 1 := by
    have : 0 < a (-1) / a 1 := by
      have : a (-1) / a 1 = (a 1 * a (-1)) / (a 1) ^ 2 := by field_simp
      rw [this]; exact div_pos hp (by positivity)
    exact this.le
  have hk2 : varkappa a ^ 2 = a (-1) / a 1 := by
    have he : eps a ^ 2 = 1 := by unfold eps; split_ifs <;> norm_num
    simp only [varkappa, kfun, mul_pow, Real.sq_sqrt hr, he, one_mul]
  rw [regular_iff_of_k10 a _ reflForms_kind, calA_reflForms, calB_reflForms]
  have key : (1 - varkappa a ^ 2) = 0 ↔ a 1 = a (-1) := by
    rw [hk2, sub_eq_zero, eq_comm, div_eq_one_iff_eq h1]
    exact eq_comm
  have hwc : (omega a 1 : ℂ) ≠ omega a (-1) := by exact_mod_cast hw.ne
  constructor
  · intro hne heq
    apply hne
    have : (1 - varkappa a ^ 2) = 0 := key.2 heq
    have h' : (1 - (varkappa a : ℂ) ^ 2) = 0 := by exact_mod_cast this
    rw [h']; simp
  · intro hne heq
    have h2 : ((omega a 1 : ℂ) - omega a (-1)) * (1 - (varkappa a : ℂ) ^ 2) = 0 := by
      rw [sub_mul, heq]; ring
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact hwc (sub_eq_zero.1 h3)
    · apply hne
      apply key.1
      exact_mod_cast h3

end GeneralBC
end Involution
