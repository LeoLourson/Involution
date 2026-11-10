module

public import Involution.Estimates.ReflectionZerosRouche

/-! Предложение `prop:10` статьи в параметрической форме: нули `H(ρ) = cos ρL + γ cos ρd`
при условии `|γ| cosh(|d| r) < sin(Lr)`: по одному простому нулю в кругах, отделённость,
вещественность при вещественном `γ`, существование `r`. -/

@[expose] public noncomputable section

open Metric Set

namespace Involution

variable {L d r : ℝ} {γ : ℂ}

/-- (iii), простота: каждый нуль `H` имеет кратность ровно 1. -/
theorem reflH_zero_order_one (hL : 0 < L) (hd : |d| ≤ L) (hr0 : 0 < r)
    (hr : r ≤ Real.pi / (2 * L)) (hγ : ‖γ‖ * Real.cosh (|d| * r) < Real.sin (L * r)) {ρ : ℂ}
    (h : reflH L d γ ρ = 0) : analyticOrderAt (reflH L d γ) ρ = 1 := by
  obtain ⟨n, hn⟩ := reflH_zero_mem_ball hL hd hr0 hr hγ h
  obtain ⟨w, hw, -, hord, huniq⟩ := reflH_ball_unique_simple hL hd hr0 hr hγ n
  rwa [huniq ρ hn h]

/-- (iii), отделённость: нули `H` попарно на расстоянии не менее `π/L - 2r > 0`. -/
theorem reflH_zeros_separated (hL : 0 < L) (hd : |d| ≤ L) (hr0 : 0 < r)
    (hr : r < Real.pi / (2 * L)) (hγ : ‖γ‖ * Real.cosh (|d| * r) < Real.sin (L * r)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ ρ' : ℂ, reflH L d γ ρ = 0 → reflH L d γ ρ' = 0 → ρ ≠ ρ' →
      δ ≤ ‖ρ - ρ'‖ := by
  have hr' := hr.le
  have hpi : Real.pi / L = 2 * (Real.pi / (2 * L)) := by field_simp
  refine ⟨Real.pi / L - 2 * r, by linarith, fun ρ ρ' h h' hne => ?_⟩
  obtain ⟨n, hn⟩ := reflH_zero_mem_ball hL hd hr0 hr' hγ h
  obtain ⟨m, hm⟩ := reflH_zero_mem_ball hL hd hr0 hr' hγ h'
  by_cases hnm : n = m
  · subst hnm
    obtain ⟨w, -, -, -, hu⟩ := reflH_ball_unique_simple hL hd hr0 hr' hγ n
    exact absurd ((hu ρ hn h).trans (hu ρ' hm h').symm) hne
  · have h1 := pi_div_le_center_dist hL hnm
    rw [mem_ball, dist_eq_norm] at hn hm
    have h2 : ‖(reflCenter L n : ℂ) - reflCenter L m‖ ≤ ‖ρ - ρ'‖ + 2 * r := by
      calc _ = ‖(ρ - ρ') - (ρ - (reflCenter L n : ℂ)) + (ρ' - (reflCenter L m : ℂ))‖ := by
            ring_nf
        _ ≤ ‖(ρ - ρ') - (ρ - (reflCenter L n : ℂ))‖ + ‖ρ' - (reflCenter L m : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ ‖ρ - ρ'‖ + ‖ρ - (reflCenter L n : ℂ)‖ + ‖ρ' - (reflCenter L m : ℂ)‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ _ := by linarith
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h2
    linarith

/-- (iv): при вещественном `γ` все нули `H` вещественны. -/
theorem reflH_zero_real (hL : 0 < L) (hd : |d| ≤ L) (hr0 : 0 < r)
    (hr : r ≤ Real.pi / (2 * L)) (hγ : ‖γ‖ * Real.cosh (|d| * r) < Real.sin (L * r))
    (hreal : γ.im = 0) {ρ : ℂ} (h : reflH L d γ ρ = 0) : ρ.im = 0 := by
  obtain ⟨n, hn⟩ := reflH_zero_mem_ball hL hd hr0 hr hγ h
  obtain ⟨w, -, -, -, hu⟩ := reflH_ball_unique_simple hL hd hr0 hr hγ n
  have hconj : ∀ z, reflH L d γ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (reflH L d γ z) := by
    intro z
    have hg : (starRingEnd ℂ) γ = γ := Complex.conj_eq_iff_im.2 hreal
    unfold reflH
    simp [← Complex.cos_conj, hg]
  have hcb : ∀ z ∈ ball (reflCenter L n : ℂ) r,
      (starRingEnd ℂ) z ∈ ball (reflCenter L n : ℂ) r := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    have : (starRingEnd ℂ) z - (reflCenter L n : ℂ) =
        (starRingEnd ℂ) (z - (reflCenter L n : ℂ)) := by
      simp
    rw [this, Complex.norm_conj]; exact hz
  have h1 := hu ρ hn h
  have h2 := hu ((starRingEnd ℂ) ρ) (hcb ρ hn) (by rw [hconj, h]; simp)
  have : (starRingEnd ℂ) ρ = ρ := h2.trans h1.symm
  exact Complex.conj_eq_iff_im.1 this

/-- (v): достаточное условие существования `r`. -/
theorem exists_radius (hL : 0 < L) (hγ : ‖γ‖ * Real.cosh (Real.pi * |d| / (2 * L)) < 1) :
    ∃ r : ℝ, 0 < r ∧ r < Real.pi / (2 * L) ∧ ‖γ‖ * Real.cosh (|d| * r) < Real.sin (L * r) := by
  set r₀ := Real.pi / (2 * L) with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  have hcont : ContinuousAt (fun r : ℝ => Real.sin (L * r) - ‖γ‖ * Real.cosh (|d| * r)) r₀ := by
    fun_prop
  have hval : 0 < Real.sin (L * r₀) - ‖γ‖ * Real.cosh (|d| * r₀) := by
    have e1 : L * r₀ = Real.pi / 2 := by rw [hr₀]; field_simp
    have e2 : |d| * r₀ = Real.pi * |d| / (2 * L) := by rw [hr₀]; ring
    rw [e1, e2, Real.sin_pi_div_two]; linarith
  have hev := (hcont.eventually (lt_mem_nhds hval)).filter_mono (nhdsWithin_le_nhds (s := Iio r₀))
  have hev2 : ∀ᶠ r in nhdsWithin r₀ (Iio r₀), r ∈ Ioo 0 r₀ := Ioo_mem_nhdsLT hr₀pos
  obtain ⟨r, h1, h2⟩ := (hev.and hev2).exists
  exact ⟨r, h2.1, h2.2, by linarith⟩

/-- Итог `prop:10` для `H`: пункты (i)–(iii) вместе. -/
theorem reflH_zeros (hL : 0 < L) (hd : |d| < L) (hr0 : 0 < r) (hr : r < Real.pi / (2 * L))
    (hγ : ‖γ‖ * Real.cosh (|d| * r) < Real.sin (L * r)) :
    (∀ ρ : ℂ, reflH L d γ ρ = 0 → ∃ n : ℤ, ρ ∈ ball (reflCenter L n : ℂ) r) ∧
    (∀ n : ℤ, ∃ w ∈ ball (reflCenter L n : ℂ) r, reflH L d γ w = 0 ∧
      analyticOrderAt (reflH L d γ) w = 1 ∧
      ∀ z ∈ ball (reflCenter L n : ℂ) r, reflH L d γ z = 0 → z = w) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ ρ ρ' : ℂ, reflH L d γ ρ = 0 → reflH L d γ ρ' = 0 → ρ ≠ ρ' →
      δ ≤ ‖ρ - ρ'‖) ∧
    (∀ ρ : ℂ, reflH L d γ ρ = 0 → analyticOrderAt (reflH L d γ) ρ = 1) :=
  ⟨fun _ h => reflH_zero_mem_ball hL hd.le hr0 hr.le hγ h,
   reflH_ball_unique_simple hL hd.le hr0 hr.le hγ,
   reflH_zeros_separated hL hd.le hr0 hr hγ,
   fun _ h => reflH_zero_order_one hL hd.le hr0 hr.le hγ h⟩

/-- Перенос на `F = c · H`, `c ≠ 0` (форма `ZerosSeparated` и `ZerosEventuallySimple`):
отделённость нулей с `Re ρ ≥ 0`. -/
theorem scaled_separated (hL : 0 < L) (hd : |d| < L) (hr0 : 0 < r) (hr : r < Real.pi / (2 * L))
    (hγ : ‖γ‖ * Real.cosh (|d| * r) < Real.sin (L * r)) {c : ℂ} (hc : c ≠ 0) {F : ℂ → ℂ}
    (hF : ∀ ρ, F ρ = c * reflH L d γ ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ ρ' : ℂ, 0 ≤ ρ.re → 0 ≤ ρ'.re → F ρ = 0 → F ρ' = 0 →
      ρ ≠ ρ' → δ ≤ ‖ρ - ρ'‖ := by
  obtain ⟨δ, hδ, h⟩ := reflH_zeros_separated hL hd.le hr0 hr hγ
  refine ⟨δ, hδ, fun ρ ρ' _ _ h1 h2 hne => h ρ ρ' ?_ ?_ hne⟩
  · rw [hF] at h1; exact (mul_eq_zero.1 h1).resolve_left hc
  · rw [hF] at h2; exact (mul_eq_zero.1 h2).resolve_left hc

/-- Перенос на `F = c · H`: все нули `F` (в том числе с `Re ρ ≥ 0`) простые. -/
theorem scaled_eventually_simple (hL : 0 < L) (hd : |d| < L) (hr0 : 0 < r)
    (hr : r < Real.pi / (2 * L)) (hγ : ‖γ‖ * Real.cosh (|d| * r) < Real.sin (L * r)) {c : ℂ}
    (hc : c ≠ 0) {F : ℂ → ℂ} (hF : ∀ ρ, F ρ = c * reflH L d γ ρ) :
    {ρ : ℂ | 0 ≤ ρ.re ∧ F ρ = 0 ∧ analyticOrderAt F ρ ≠ 1}.Finite := by
  have hFe : F = fun ρ => c * reflH L d γ ρ := funext hF
  have hH : AnalyticOnNhd ℂ (reflH L d γ) univ := by
    intro z _; unfold reflH; fun_prop
  refine (Set.finite_empty).subset fun ρ ⟨_, h0, hne⟩ => ?_
  have h1 : reflH L d γ ρ = 0 := by
    rw [hF] at h0; exact (mul_eq_zero.1 h0).resolve_left hc
  have h2 := reflH_zero_order_one hL hd.le hr0 hr.le hγ h1
  apply hne
  rw [hFe]
  have := analyticOrderAt_mul (𝕜 := ℂ) (f := fun _ : ℂ => c) (g := reflH L d γ) (z₀ := ρ)
    analyticAt_const (hH ρ (mem_univ _))
  have h3 : analyticOrderAt (fun _ : ℂ => c) ρ = 0 := analyticAt_const.analyticOrderAt_eq_zero.2 hc
  have h4 : (fun ρ => c * reflH L d γ ρ) = (fun _ : ℂ => c) * reflH L d γ := rfl
  rw [h4]; simpa [h3, h2] using this

end Involution
