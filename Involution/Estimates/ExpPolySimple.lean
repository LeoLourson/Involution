module

public import Involution.Estimates.ExpPolyLower
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Лемма `lem:simple`: при сильной регулярности вблизи далёкого нуля `ρ⁰` функции `F`
выполнено `|F(ρ)| ≥ c₁ |ρ-ρ⁰| e^{L|Im ρ|}` и `|F'(ρ⁰)| ≥ c₁`. Сильная
регулярность входит гипотезами: нули с `Re ≥ 0` попарно отделены числом `δ_s`, и все такие
нули, кроме конечного числа, просты. Доказательство: `g = dslope F ρ⁰` не имеет нулей в
круге, на окружности `|g| ≥ c_δ/δ` по `expPoly_lower_dist`, принцип минимума модуля —
максимум для `1/g`. -/

@[expose] public noncomputable section

open Complex Real Filter Topology Metric

namespace Involution

theorem differentiable_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ (dslope f a) := by
  intro b
  by_cases hb : b = a
  · subst hb
    obtain ⟨p, hp⟩ := (hf.analyticAt b)
    exact hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt
  · exact (differentiableAt_dslope_of_ne hb).2 (hf b)

theorem deriv_ne_zero_of_order_one {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℂ} (h0 : f a = 0)
    (h1 : analyticOrderAt f a = 1) : deriv f a ≠ 0 := by
  have := (hf.analyticAt a : AnalyticAt ℂ f a).analyticOrderAt_deriv_add_one
  have e : analyticOrderAt (fun z => f z - f a) a = 1 := by simpa [h0] using h1
  rw [e] at this
  have h2 : analyticOrderAt (deriv f) a = 0 := by
    by_contra hne
    have h3 : 1 ≤ analyticOrderAt (deriv f) a := Order.one_le_iff_ne_zero.2 hne
    have h4 := add_le_add_left h3 1
    rw [this] at h4
    norm_num at h4
  have hd : AnalyticAt ℂ (deriv f) a := (hf.analyticAt a : AnalyticAt ℂ f a).deriv
  exact (hd.analyticOrderAt_eq_zero).1 h2

/-- Принцип минимума модуля: нижняя оценка на окружности переносится на круг, если `g` без
нулей в круге. -/
theorem norm_ge_on_ball {g : ℂ → ℂ} (hg : Differentiable ℂ g) {z₀ : ℂ} {r m : ℝ} (hr : 0 < r)
    (hm : 0 < m) (hne : ∀ z ∈ closedBall z₀ r, g z ≠ 0)
    (hs : ∀ z ∈ sphere z₀ r, m ≤ ‖g z‖) : ∀ z ∈ closedBall z₀ r, m ≤ ‖g z‖ := by
  intro z hz
  have hd : DifferentiableOn ℂ (fun z => (g z)⁻¹) (closedBall z₀ r) := fun z hz =>
    ((hg z).inv (hne z hz)).differentiableWithinAt
  have hd' : DifferentiableOn ℂ (fun z => (g z)⁻¹) (closure (ball z₀ r)) := by
    rw [closure_ball _ hr.ne']; exact hd
  have hbd := Complex.norm_le_of_forall_mem_frontier_norm_le (f := fun z => (g z)⁻¹)
    (U := ball z₀ r) isBounded_ball hd'.diffContOnCl (C := m⁻¹) (by
      intro w hw
      rw [frontier_ball _ hr.ne'] at hw
      rw [norm_inv]
      exact inv_anti₀ hm (hs w hw)) (z := z) (by rwa [closure_ball _ hr.ne'])
  rw [norm_inv] at hbd
  have hgpos : 0 < ‖g z‖ := norm_pos_iff.2 (hne z hz)
  exact (inv_le_inv₀ hgpos hm).1 hbd

/-- Лемма `lem:simple`. Гипотезы сильной регулярности: нули `F` с `Re ≥ 0` попарно отделены
числом `δ_s`, и все такие нули, кроме конечного числа, просты. -/
theorem expPoly_simple_zero {θp θm θdp θdm : ℂ} {L d : ℝ} (hL : 0 < L) (hd : |d| < L)
    (hp : θp ≠ 0) (hm : ‖θm‖ = ‖θp‖) {δs : ℝ} (hδs : 0 < δs)
    (hsep : ∀ z w : ℂ, expPoly θp θm θdp θdm L d z = 0 → expPoly θp θm θdp θdm L d w = 0 →
      0 ≤ z.re → 0 ≤ w.re → z ≠ w → δs ≤ dist z w)
    (hfin : {z : ℂ | expPoly θp θm θdp θdm L d z = 0 ∧ 0 ≤ z.re ∧
      analyticOrderAt (expPoly θp θm θdp θdm L d) z ≠ 1}.Finite) :
    ∃ δ > 0, ∃ c₁ > 0, ∃ rF : ℝ, ∀ ρ₀ : ℂ, expPoly θp θm θdp θdm L d ρ₀ = 0 → rF < ρ₀.re →
      (∀ z, expPoly θp θm θdp θdm L d z = 0 → dist z ρ₀ ≤ δ → z = ρ₀) ∧
      (∀ ρ : ℂ, dist ρ ρ₀ ≤ δ →
        c₁ * dist ρ ρ₀ * Real.exp (L * |ρ.im|) ≤ ‖expPoly θp θm θdp θdm L d ρ‖) ∧
      c₁ ≤ ‖deriv (expPoly θp θm θdp θdm L d) ρ₀‖ := by
  set F := expPoly θp θm θdp θdm L d with hF
  have hFd : Differentiable ℂ F := expPoly_differentiable _ _ _ _ _ _
  set δ := δs / 4 with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨c, hc, hcδ⟩ := expPoly_lower_dist (θdp := θdp) (θdm := θdm) hL hd hp hm hδpos
  obtain ⟨h₀, h01, hA⟩ := expPoly_lower_outside (θdp := θdp) (θdm := θdm) hL hd hp hm
  obtain ⟨R, hR⟩ := (hfin.image Complex.re).bddAbove
  refine ⟨δ, hδpos, c / δ * Real.exp (-(L * (h₀ + δ))), by positivity, max R 0 + 2 * δ, ?_⟩
  intro ρ₀ hz hre
  have hre0 : 0 ≤ ρ₀.re := by linarith [le_max_right R 0]
  have hord : analyticOrderAt F ρ₀ = 1 := by
    by_contra hne
    have := hR ⟨ρ₀, ⟨hz, hre0, hne⟩, rfl⟩
    linarith [le_max_left R 0]
  have hder : deriv F ρ₀ ≠ 0 := deriv_ne_zero_of_order_one hFd hz hord
  have hclaim : ∀ w, F w = 0 → dist w ρ₀ ≤ 2 * δ → w = ρ₀ := by
    intro w hw hdw
    by_contra hne
    have hwre : 0 ≤ w.re := by
      have h1 : |w.re - ρ₀.re| ≤ dist w ρ₀ := by
        simpa [Complex.dist_eq] using Complex.abs_re_le_norm (w - ρ₀)
      have := (abs_le.1 h1).1
      linarith [le_max_right R 0, le_max_left R 0]
    have := hsep w ρ₀ hw hz hwre hre0 hne
    linarith
  set g := dslope F ρ₀ with hg
  have hgd : Differentiable ℂ g := differentiable_dslope hFd ρ₀
  have hgne : ∀ z ∈ closedBall ρ₀ δ, g z ≠ 0 := by
    intro z hzb
    by_cases hzz : z = ρ₀
    · rw [hzz, hg, dslope_same]; exact hder
    · have hFz : F z ≠ 0 := fun h => hzz (hclaim z h (by
        have := mem_closedBall.1 hzb; linarith))
      intro h0
      have := sub_smul_dslope F ρ₀ z
      rw [← hg, h0, smul_zero, hz, sub_zero] at this
      exact hFz this.symm
  have hgs : ∀ z ∈ sphere ρ₀ δ, c / δ ≤ ‖g z‖ := by
    intro z hzs
    have hzd : dist z ρ₀ = δ := mem_sphere.1 hzs
    have hnear : ∀ w, F w = 0 → δ ≤ dist z w := by
      intro w hw
      by_cases hwr : w = ρ₀
      · rw [hwr, hzd]
      · have h2 : 2 * δ < dist w ρ₀ := by
          by_contra hle
          exact hwr (hclaim w hw (not_lt.1 hle))
        have := dist_triangle w z ρ₀
        rw [dist_comm w z] at this
        linarith
    have h1 := hcδ z hnear
    have hFz : ‖F z‖ = δ * ‖g z‖ := by
      have := sub_smul_dslope F ρ₀ z
      rw [← hg, hz, sub_zero] at this
      rw [← this, smul_eq_mul, norm_mul, ← dist_eq_norm, hzd]
    have hex : 1 ≤ Real.exp (L * |z.im|) := Real.one_le_exp (by positivity)
    rw [div_le_iff₀ hδpos]
    nlinarith
  have hgall := norm_ge_on_ball hgd hδpos (by positivity) hgne hgs
  have hρ₀im : |ρ₀.im| < h₀ := expPoly_zero_im_lt hp hA hz
  refine ⟨fun z hz' hzd => hclaim z hz' (by linarith), fun ρ hρ => ?_, ?_⟩
  · have hFρ : ‖F ρ‖ = dist ρ ρ₀ * ‖g ρ‖ := by
      have := sub_smul_dslope F ρ₀ ρ
      rw [← hg, hz, sub_zero] at this
      rw [← this, smul_eq_mul, norm_mul, dist_eq_norm]
    have himρ : |ρ.im| ≤ h₀ + δ := by
      have h1 : |ρ.im - ρ₀.im| ≤ dist ρ ρ₀ := by
        simpa [Complex.dist_eq] using Complex.abs_im_le_norm (ρ - ρ₀)
      calc |ρ.im| = |(ρ.im - ρ₀.im) + ρ₀.im| := by ring_nf
        _ ≤ |ρ.im - ρ₀.im| + |ρ₀.im| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hge := hgall ρ (mem_closedBall.2 hρ)
    have hexp : Real.exp (L * |ρ.im|) ≤ Real.exp (L * (h₀ + δ)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left himρ hL.le)
    have hprod : Real.exp (-(L * (h₀ + δ))) * Real.exp (L * (h₀ + δ)) = 1 := by
      rw [← Real.exp_add]; simp
    have hd0 : 0 ≤ dist ρ ρ₀ := dist_nonneg
    have hexpn : 0 < Real.exp (-(L * (h₀ + δ))) := Real.exp_pos _
    rw [hFρ]
    calc c / δ * Real.exp (-(L * (h₀ + δ))) * dist ρ ρ₀ * Real.exp (L * |ρ.im|)
        ≤ c / δ * Real.exp (-(L * (h₀ + δ))) * dist ρ ρ₀ * Real.exp (L * (h₀ + δ)) := by
          gcongr
      _ = c / δ * dist ρ ρ₀ := by
          calc _ = c / δ * dist ρ ρ₀ * (Real.exp (-(L * (h₀ + δ))) * Real.exp (L * (h₀ + δ))) := by
                ring
            _ = _ := by rw [hprod, mul_one]
      _ ≤ dist ρ ρ₀ * ‖g ρ‖ := by nlinarith
  · have := hgall ρ₀ (mem_closedBall_self hδpos.le)
    rw [hg, dslope_same] at this
    have h1 : Real.exp (-(L * (h₀ + δ))) ≤ 1 := Real.exp_le_one_iff.2 (by
      have := hL.le; nlinarith [hρ₀im, abs_nonneg ρ₀.im])
    calc _ ≤ c / δ * 1 := by gcongr
      _ ≤ _ := by simpa using this

end Involution
