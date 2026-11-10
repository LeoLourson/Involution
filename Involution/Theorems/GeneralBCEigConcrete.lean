module

public import Involution.Theorems.GeneralBCEigLocal
public import Involution.Theorems.GeneralBCEigGlobal

/-! # Теорема thm:eig (b): конкретные данные `Fchar`, `Gfun`, `Delta` (пакет G6)

`Gfun(ρ²) = ρ^{κ-1} F(ρ)`, кратности нулей `Gfun` и `Delta` в `ρ²` через `F` и `F + η`,
`PlanarData` для `Fchar`. -/

@[expose] public noncomputable section

open Set Filter Topology

namespace Involution
namespace GeneralBC

theorem kappaSum_sub_one (U : Forms) :
    (kappaSum U : ℤ) - 1 = match U.kind with
      | Forms.Kind.k00 => -1
      | Forms.Kind.k11 => 1
      | Forms.Kind.k10 => 0 := by
  unfold kappaSum Forms.ord Forms.kind
  by_cases h0 : U.HasDeriv 0 <;> by_cases h1 : U.HasDeriv 1 <;> simp [h0, h1]

theorem Gfun_sq_zpow (a : ℝ → ℝ) (U : Forms) {ρ : ℂ} (hρ : ρ ≠ 0) :
    Gfun a U (ρ ^ 2) = ρ ^ ((kappaSum U : ℤ) - 1) * Fchar a U ρ := by
  rw [Gfun_sq a U ρ hρ, kappaSum_sub_one]
  cases U.kind <;> simp [div_eq_inv_mul, zpow_neg]

/-- Порядок нуля `Gfun` в `ρ²` равен порядку нуля `F` в `ρ ≠ 0`. -/
theorem analyticOrderAt_Gfun_sq (a : ℝ → ℝ) (U : Forms) {ρ : ℂ} (hρ : ρ ≠ 0) :
    analyticOrderAt (Gfun a U) (ρ ^ 2) = analyticOrderAt (Fchar a U) ρ := by
  have hsq : AnalyticAt ℂ (fun w : ℂ => w ^ 2) ρ := by fun_prop
  have hder : deriv (fun w : ℂ => w ^ 2) ρ ≠ 0 := by simp [hρ]
  have h1 := analyticOrderAt_comp_of_deriv_ne_zero (f := Gfun a U) hsq hder
  have huA : AnalyticAt ℂ (fun w : ℂ => w ^ ((kappaSum U : ℤ) - 1)) ρ := analyticAt_id.zpow hρ
  have hFA : AnalyticAt ℂ (Fchar a U) ρ := (Fchar_differentiable a U).analyticAt ρ
  have hev : (Gfun a U ∘ fun w : ℂ => w ^ 2) =ᶠ[𝓝 ρ]
      (fun w : ℂ => w ^ ((kappaSum U : ℤ) - 1)) * Fchar a U := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hρ)] with w hw
    have hw' : w ≠ 0 := hw
    simp only [Function.comp, Pi.mul_apply]
    exact Gfun_sq_zpow a U hw'
  rw [← h1, analyticOrderAt_congr hev, analyticOrderAt_mul huA hFA,
    (huA.analyticOrderAt_eq_zero).2 (zpow_ne_zero _ hρ), zero_add]

/-- `PlanarData` для `Fchar` и остатка `η` из леммы lem:det. -/
theorem planarData_Fchar {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hreg : Regular a U) {η : ℂ → ℂ} (hηd : DifferentiableOn ℂ η {0}ᶜ)
    (hsmall : ∀ ε > 0, ∃ r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ →
      ‖η ρ‖ * Real.exp (-(Ltot a) * |ρ.im|) ≤ ε) :
    PlanarData (Fchar a U) η (Ltot a) := by
  obtain ⟨h₀, h1, hlow, N₀, hN⟩ := lem_F_ac ⟨m, κ, h⟩ hreg
  have hE : 0 < ‖theta a U‖ := norm_pos_iff.2 hreg
  have hne : ∀ ρ : ℂ, h₀ ≤ |ρ.im| → Fchar a U ρ ≠ 0 := by
    intro ρ hρ h0
    have := hlow ρ hρ
    rw [h0, norm_zero] at this
    have := Real.exp_pos (Ltot a * |ρ.im|)
    nlinarith
  refine ⟨Fchar_differentiable a U, hηd, ⟨h₀, N₀, fun z hz => ?_, hN⟩, fun δ hδ => ?_,
    hsmall, ⟨(h₀ : ℂ) * Complex.I, hne _ ?_⟩⟩
  · by_contra hc
    exact hne z (not_lt.1 hc) hz
  · obtain ⟨c, hc, H⟩ := lem_F_b ⟨m, κ, h⟩ hreg δ hδ
    exact ⟨c, hc, H⟩
  · simp [abs_of_nonneg (by linarith : 0 ≤ h₀)]

theorem goodRad_all {F : ℂ → ℂ} {h₀ ε b : ℝ} (hsym : ∀ z, F z = 0 → F (-z) = 0)
    (hstrip : ∀ z, F z = 0 → |z.im| < h₀) (hε : ε ≤ 1 / 2) (hb : h₀ + 1 ≤ b)
    (hg : GoodRad F ε b) : ∀ z, F z = 0 → 2 * ε ≤ |‖z‖ - b| := by
  intro z hz
  rcases lt_trichotomy z.re 0 with hneg | hzero | hpos
  · have := hg (-z) (hsym z hz) (by simpa using hneg)
    rwa [norm_neg] at this
  · have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    rw [hzero, abs_zero, zero_add] at h1
    have h2 := hstrip z hz
    rw [abs_of_neg (by linarith)]
    linarith
  · exact hg z hz hpos

theorem analyticOrderAt_const_mul {f : ℂ → ℂ} {z c : ℂ} (hc : c ≠ 0) (hf : AnalyticAt ℂ f z) :
    analyticOrderAt (fun w => c * f w) z = analyticOrderAt f z := by
  have : (fun w => c * f w) = (fun _ => c) * f := rfl
  rw [this, analyticOrderAt_mul analyticAt_const hf,
    (analyticAt_const (v := c) (x := z)).analyticOrderAt_eq_zero.2 hc, zero_add]

end GeneralBC
end Involution
