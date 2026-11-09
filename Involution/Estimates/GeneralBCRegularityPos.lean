module

public import Involution.Folding.GeneralBCLeading
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Положительность `ℓ_±`, `L`, `ω_±` при (H) (пакет G5)

При (H) `σ_± = 1 ± √(a(x)a(-x)) > 0` на `[-1,1]`, поэтому `τ_± > 0`, `ℓ_± = ∫₀¹ τ_± > 0`,
`0 < L`, `|d| < L`, `ω_± > 0`; кроме того `ϰ ≠ 0`. -/

@[expose] public noncomputable section

open Set MeasureTheory

namespace Involution
namespace GeneralBC

variable {a : ℝ → ℝ} {m κ : ℝ}

/-- `σ_s > 0` на `[-1,1]` при (H), `s = ±1`. -/
theorem regularity_sigma_pos (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : 0 < sigma a s x := by
  unfold sigma
  rcases hs with rfl | rfl
  · have := Real.sqrt_nonneg (a x * a (-x)); linarith
  · have hq : Real.sqrt (a x * a (-x)) < 1 := by
      rw [Real.sqrt_lt' one_pos]; linarith [h.upper x hx, h.kappa_lt]
    linarith

theorem regularity_tau_pos (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : 0 < tau a s x :=
  inv_pos.2 (Real.sqrt_pos.2 (regularity_sigma_pos h hx hs))

theorem continuousOn_tau (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ContinuousOn (tau a s) (Icc (0 : ℝ) 1) := by
  have hc : ContinuousOn a (Icc (-1 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] using h.ac.continuousOn
  have h1 : ContinuousOn a (Icc (0 : ℝ) 1) := hc.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  have h2 : ContinuousOn (fun x => a (-x)) (Icc (0 : ℝ) 1) :=
    hc.comp continuousOn_neg (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  unfold tau sigma
  refine ContinuousOn.inv₀ ?_ (fun x hx => ?_)
  · exact (continuousOn_const.add (continuousOn_const.mul (h1.mul h2).sqrt)).sqrt
  · exact (Real.sqrt_pos.2 (regularity_sigma_pos h ⟨by linarith [hx.1], hx.2⟩ hs)).ne'

/-- `ℓ_s > 0` при (H), `s = ±1`. -/
theorem ell_pos (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) : 0 < ell a s := by
  unfold ell tPhase
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (continuousOn_tau h hs).intervalIntegrable_of_Icc zero_le_one
  · intro x hx
    exact regularity_tau_pos h ⟨by linarith [hx.1], by linarith [hx.2]⟩ hs
  · exact zero_lt_one

theorem Ltot_pos (h : HypH a m κ) : 0 < Ltot a :=
  add_pos (ell_pos h (Or.inl rfl)) (ell_pos h (Or.inr rfl))

/-- При (H) `ℓ₊ < ℓ₋`, то есть `d < 0`. -/
theorem dlt_neg (h : HypH a m κ) : dlt a < 0 := by
  have hlt : ell a 1 < ell a (-1) := by
    unfold ell tPhase
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one
      (continuousOn_tau h (Or.inl rfl)) (continuousOn_tau h (Or.inr rfl))
    · intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
      have h1 := regularity_sigma_pos h hx' (Or.inl rfl)
      have h2 := regularity_sigma_pos h hx' (Or.inr rfl)
      have hs := Real.sqrt_nonneg (a x * a (-x))
      unfold tau
      apply inv_anti₀ (Real.sqrt_pos.2 h2)
      apply Real.sqrt_le_sqrt
      unfold sigma; linarith
    · refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
      have hx' : (0:ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      have h1 := regularity_sigma_pos h hx' (Or.inl rfl)
      have h2 := regularity_sigma_pos h hx' (Or.inr rfl)
      have ha : 0 < a 0 * a (-0) := by
        have := h.lower 0 hx'
        have h0 : 0 < |a 0| := lt_of_lt_of_le h.m_pos this
        rw [neg_zero, ← sq, ← sq_abs]; positivity
      have hs := Real.sqrt_pos.2 ha
      unfold tau
      apply inv_strictAnti₀ (Real.sqrt_pos.2 h2)
      apply Real.sqrt_lt_sqrt h2.le
      unfold sigma; linarith
  unfold dlt; linarith

theorem dlt_ne_zero (h : HypH a m κ) : dlt a ≠ 0 := (dlt_neg h).ne

theorem abs_dlt_lt_Ltot (h : HypH a m κ) : |dlt a| < Ltot a := by
  have h1 := ell_pos h (Or.inl rfl)
  have h2 := ell_pos h (Or.inr rfl)
  rw [abs_lt]; unfold dlt Ltot; constructor <;> linarith

theorem regularity_omega_pos (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) : 0 < omega a s :=
  regularity_tau_pos h ⟨by norm_num, le_refl _⟩ hs

theorem regularity_varkappa_ne_zero (h : HypH a m κ) : varkappa a ≠ 0 := by
  have hp := h.prod_pos
  have h1 : a 1 ≠ 0 := fun h0 => by simp [h0] at hp
  have hr : 0 < a (-1) / a 1 := by
    have : a (-1) / a 1 = (a 1 * a (-1)) / (a 1) ^ 2 := by field_simp
    rw [this]; exact div_pos hp (by positivity)
  unfold varkappa kfun
  exact mul_ne_zero (eps_ne_zero a) (Real.sqrt_pos.2 hr).ne'

end GeneralBC
end Involution
