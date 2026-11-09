module

public import Involution.Theorems.GeneralBCEigBasic
public import Involution.Setup.Rouche

/-! # Теорема thm:eig, часть 2: локальные утверждения (пакет G6)

Порядок нуля `Δ` в точке `ρ²` равен порядку нуля `F + η` в `ρ`; корень `λ^{1/2}` имеет
`Re ≥ 0`; далёкий нуль `F + η` лежит в `δ`-окрестности нуля `F`; простота далёких нулей
при сильной регулярности (шаг 5 доказательства thm:eig, без нумерации). -/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace Involution
namespace GeneralBC

/-- Главная ветвь корня: `Re λ^{1/2} ≥ 0`. -/
theorem re_cpow_half_nonneg (lam : ℂ) : 0 ≤ (lam ^ (1 / 2 : ℂ)).re := by
  by_cases h : lam = 0
  · subst h; simp
  · rw [Complex.cpow_def_of_ne_zero h, Complex.exp_re]
    refine mul_nonneg (Real.exp_pos _).le ?_
    have h1 := Complex.neg_pi_lt_arg lam
    have h2 := Complex.arg_le_pi lam
    have : (Complex.log lam * (1 / 2 : ℂ)).im = Complex.arg lam / 2 := by
      simp [Complex.log_im]; ring
    rw [this]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

/-- Нуль с ненулевой производной прост. -/
theorem analyticOrderAt_eq_one_of_deriv_ne_zero {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (h0 : f z = 0) (hd : deriv f z ≠ 0) : analyticOrderAt f z = 1 := by
  have h := hf.analyticOrderAt_deriv_add_one
  have h' : analyticOrderAt (deriv f) z = 0 :=
    (analyticOrderAt_eq_zero).2 (Or.inr hd)
  simp only [h0, sub_zero, h'] at h
  simpa using h.symm

/-- Простой нуль имеет ненулевую производную. -/
theorem deriv_ne_zero_of_analyticOrderAt_eq_one {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (h : analyticOrderAt f z = 1) : deriv f z ≠ 0 := by
  have h1 : analyticOrderAt (deriv f) z = ((0 : ℕ) : ℕ∞) :=
    analyticOrderAt_deriv_of_pos hf (n := 0) (by simpa using h)
  have := (analyticOrderAt_eq_zero (f := deriv f) (z₀ := z)).1 (by simpa using h1)
  rcases this with h2 | h2
  · exact absurd hf.deriv h2
  · exact h2

/-- Порядок нуля `Δ` в `ρ²` равен порядку нуля `F + η` в `ρ ≠ 0`. -/
theorem analyticOrderAt_Delta_sq {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) {η : ℂ → ℂ} (hηd : DifferentiableOn ℂ η {0}ᶜ)
    (hη : ∀ ρ : ℂ, ρ ≠ 0 →
      ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) = cStar a U * (Fchar a U ρ + η ρ))
    {ρ : ℂ} (hρ : ρ ≠ 0) :
    analyticOrderAt (Delta a U) (ρ ^ 2) = analyticOrderAt (fun w => Fchar a U w + η w) ρ := by
  have hsq : AnalyticAt ℂ (fun w : ℂ => w ^ 2) ρ := by fun_prop
  have hder : deriv (fun w : ℂ => w ^ 2) ρ ≠ 0 := by
    simp [hρ]
  have h1 := analyticOrderAt_comp_of_deriv_ne_zero (f := Delta a U) hsq hder
  have hΨ : AnalyticAt ℂ (fun w => Fchar a U w + η w) ρ := by
    have h2 : AnalyticAt ℂ η ρ :=
      hηd.analyticAt (isOpen_compl_singleton.mem_nhds (by simpa using hρ))
    exact ((Fchar_differentiable a U).analyticAt ρ).add h2
  set u : ℂ → ℂ := fun w => cStar a U * w ^ ((kappaSum U : ℤ) - 1) with hu
  have huA : AnalyticAt ℂ u ρ := by
    refine analyticAt_const.mul ?_
    exact (analyticAt_id.zpow hρ)
  have hu0 : u ρ ≠ 0 := by
    simp only [hu]
    exact mul_ne_zero (cStar_ne_zero h hU) (zpow_ne_zero _ hρ)
  have hev : (Delta a U ∘ fun w : ℂ => w ^ 2) =ᶠ[𝓝 ρ] u * fun w => Fchar a U w + η w := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hρ)] with w hw
    have hw' : w ≠ 0 := hw
    have := hη w hw'
    simp only [Function.comp, Pi.mul_apply, hu]
    calc Delta a U (w ^ 2) = w ^ ((kappaSum U : ℤ) - 1) *
          (w ^ (1 - (kappaSum U : ℤ)) * Delta a U (w ^ 2)) := by
          rw [← mul_assoc, ← zpow_add₀ hw']; simp
      _ = _ := by rw [this]; ring
  rw [← h1, analyticOrderAt_congr hev, analyticOrderAt_mul huA hΨ,
    (huA.analyticOrderAt_eq_zero).2 hu0, zero_add]

/-- Из `‖η‖ e^{-L|Im ρ|} ≤ ε` следует `‖η‖ ≤ ε e^{L|Im ρ|}`. -/
theorem norm_le_of_mul_exp_neg_le {x ε L t : ℝ} (hx : x * Real.exp (-L * t) ≤ ε) :
    x ≤ ε * Real.exp (L * t) := by
  have hexp : Real.exp (-L * t) * Real.exp (L * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc x = x * (Real.exp (-L * t) * Real.exp (L * t)) := by rw [hexp, mul_one]
    _ = x * Real.exp (-L * t) * Real.exp (L * t) := by ring
    _ ≤ ε * Real.exp (L * t) := mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le

/-- Далёкий нуль `F + η` лежит в `δ`-окрестности нуля `F`. -/
theorem exists_Fzero_near {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hreg : Regular a U) {η : ℂ → ℂ}
    (hsmall : ∀ ε > 0, ∃ r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ → ‖η ρ‖ * Real.exp (-(Ltot a) * |ρ.im|) ≤ ε)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ → Fchar a U ρ + η ρ = 0 →
      ∃ z : ℂ, Fchar a U z = 0 ∧ ‖ρ - z‖ < δ := by
  obtain ⟨c, hc, hb⟩ := lem_F_b ⟨m, κ, h⟩ hreg δ hδ
  obtain ⟨r, hr⟩ := hsmall (c / 2) (by positivity)
  refine ⟨r, fun ρ hρ h0 => ?_⟩
  by_contra hcon
  have hall : ∀ z : ℂ, Fchar a U z = 0 → δ ≤ ‖ρ - z‖ := by
    intro z hz
    by_contra hlt
    exact hcon ⟨z, hz, not_le.1 hlt⟩
  have h1 := hb ρ hall
  have h2 := norm_le_of_mul_exp_neg_le (hr ρ hρ)
  have h3 : ‖Fchar a U ρ‖ = ‖η ρ‖ := by
    rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
  have := Real.exp_pos (Ltot a * |ρ.im|)
  nlinarith

/-- Далёкие нули `Δ(ρ²)` с `Re ρ ≥ 0` просты при сильной регулярности (шаг 5, без нумерации). -/
theorem large_zero_simple {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (hreg : Regular a U) (hsr : StronglyRegular a U)
    (hdet : DetPrincipalPart a U) :
    ∃ R : ℝ, ∀ ρ : ℂ, R ≤ ‖ρ‖ → 0 ≤ ρ.re → Delta a U (ρ ^ 2) = 0 →
      analyticOrderAt (Delta a U) (ρ ^ 2) = 1 := by
  obtain ⟨h₀, r₁, h1, hr1, H⟩ := delta_sq_ne_zero_far h hU hreg hdet
  obtain ⟨δ, c₁, rF, hδ, hc₁, HS⟩ := lem_simple ⟨m, κ, h⟩ hsr
  obtain ⟨η, hηd, hη, hsmall⟩ := hdet
  obtain ⟨r₃, hr3⟩ := exists_Fzero_near h hreg hsmall hδ
  obtain ⟨r₂, hr2⟩ := hsmall (c₁ * δ / 2) (by positivity)
  refine ⟨max (max (max r₁ r₂) (max r₃ (rF + h₀ + δ + 1))) (h₀ + 2 * δ + |r₂| + |rF| + 1),
    fun ρ hρR hre hz => ?_⟩
  have hρ1 : r₁ ≤ ‖ρ‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hρR)
  have hρ3 : r₃ ≤ ‖ρ‖ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hρR)
  have hρ4 : rF + h₀ + δ + 1 ≤ ‖ρ‖ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hρR)
  have hρ5 : h₀ + 2 * δ + |r₂| + |rF| + 1 ≤ ‖ρ‖ := le_trans (le_max_right _ _) hρR
  have hρ2 : r₂ ≤ ‖ρ‖ := by
    have := abs_nonneg rF; have := le_abs_self r₂; linarith
  have him : |ρ.im| < h₀ := by
    by_contra hcon
    exact H ρ hρ1 (not_lt.1 hcon) hz
  have hρpos : 0 < ‖ρ‖ := by
    have := abs_nonneg rF; linarith
  have hρ0 : ρ ≠ 0 := norm_pos_iff.1 hρpos
  have hnorm : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
  have hreρ : ‖ρ‖ - h₀ ≤ ρ.re := by
    rw [abs_of_nonneg hre] at hnorm; linarith
  have hΨ0 : Fchar a U ρ + η ρ = 0 := by
    have h2 := hη ρ hρ0
    rw [hz, mul_zero] at h2
    rcases mul_eq_zero.1 h2.symm with h3 | h3
    · exact absurd h3 (cStar_ne_zero h hU)
    · exact h3
  obtain ⟨z, hFz, hzd⟩ := hr3 ρ hρ3 hΨ0
  have hzre : ρ.re - δ < z.re := by
    have : |(ρ - z).re| ≤ ‖ρ - z‖ := Complex.abs_re_le_norm _
    have h4 : (ρ - z).re = ρ.re - z.re := by simp
    rw [h4] at this
    have := (abs_le.1 this).2
    linarith
  have hzrF : rF < z.re := by
    have := abs_nonneg rF; have := le_abs_self rF; linarith
  obtain ⟨hu, hlow, hder⟩ := HS z hFz hzrF
  have hFd := Fchar_differentiable a U
  have hzδ : δ < z.re := by
    have := abs_nonneg rF; have := abs_nonneg r₂; linarith
  have hzball : ∀ w : ℂ, ‖w - z‖ ≤ δ → w ≠ 0 := by
    intro w hw h0
    subst h0
    have h5 : ‖(0 : ℂ) - z‖ = ‖z‖ := by simp
    have := Complex.re_le_norm z
    rw [h5] at hw
    linarith
  have hord : analyticOrderAt (Fchar a U) z = 1 := by
    refine analyticOrderAt_eq_one_of_deriv_ne_zero ((hFd.analyticAt z)) hFz ?_
    intro h0
    rw [h0, norm_zero] at hder
    linarith
  have hcl : closedBall z δ ⊆ ({0}ᶜ : Set ℂ) := by
    intro w hw
    exact hzball w (by simpa [dist_eq_norm] using hw)
  have hfg : ∀ w ∈ sphere z δ, ‖η w‖ < ‖Fchar a U w‖ := by
    intro w hw
    have hwz : ‖w - z‖ = δ := by simpa [dist_eq_norm] using hw
    have hwn : r₂ ≤ ‖w‖ := by
      have : ‖z‖ - δ ≤ ‖w‖ := by
        have := norm_sub_norm_le z w
        rw [norm_sub_rev] at this; linarith
      have hz1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
      have := abs_nonneg rF; have := le_abs_self r₂; have := abs_nonneg r₂
      linarith
    have e1 := norm_le_of_mul_exp_neg_le (hr2 w hwn)
    have e2 := hlow w (le_of_eq hwz)
    rw [hwz] at e2
    have := Real.exp_pos (Ltot a * |w.im|)
    have : c₁ * δ / 2 * Real.exp (Ltot a * |w.im|) < c₁ * δ * Real.exp (Ltot a * |w.im|) := by
      apply mul_lt_mul_of_pos_right _ this
      have : 0 < c₁ * δ := by positivity
      linarith
    linarith
  obtain ⟨w, hwb, hw0, hwo, hwu⟩ := rouche_simple (f := Fchar a U) (g := η)
    isOpen_compl_singleton hcl hδ hFd.differentiableOn hηd hfg (z₀ := z) (mem_ball_self hδ)
    hFz hord (fun w hw hFw => hu w hFw (mem_ball_iff_norm.1 hw).le)
  have hρb : ρ ∈ ball z δ := by simpa [dist_eq_norm] using hzd
  have hρw : ρ = w := hwu ρ hρb (by simpa using hΨ0)
  rw [analyticOrderAt_Delta_sq h hU hηd hη hρ0, hρw]
  exact hwo

end GeneralBC
end Involution
