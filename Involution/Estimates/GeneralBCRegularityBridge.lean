module

public import Involution.Estimates.GeneralBCRegularityPos
public import Involution.Estimates.ExpPolyZeros
public import Involution.Estimates.ExpPolySimple
public import Involution.Estimates.ExpPolyCount
public import Involution.Estimates.ExpPolyLower

/-! # Связь `F` с экспоненциальным многочленом W4 (пакет G5)

`Fchar a U = expPoly θ₊ θ₋ θ_d⁺ θ_d⁻ L d`; гипотезы W4 для `Fchar` при регулярности;
`lem:F` (a)–(d) и `lem:simple` для `Fchar`. Формулировки — как в `G0/Statements.lean`; вместо
`HypH` и `AdmissibleForms` достаточно `Hyp a` (нужны лишь `0 < L`, `|d| < L`). -/

@[expose] public noncomputable section

open Set Metric

namespace Involution
namespace GeneralBC

theorem Fchar_eq_expPoly (a : ℝ → ℝ) (U : Forms) :
    Fchar a U = expPoly (theta a U) (thetaMinus a U) (thetaDPlus a U)
      (thetaDMinus a U) (Ltot a) (dlt a) := by
  funext ρ; rw [Fchar_eq_expSum]; rfl

theorem hm_Fchar (a : ℝ → ℝ) (U : Forms) : ‖thetaMinus a U‖ = ‖theta a U‖ := by
  rcases thetaMinus_eq a U with h | h <;> simp [h, theta]

/-- Симметрия нулей: `F(z) = 0 → F(-z) = 0` (чётность/нечётность `F`). -/
theorem hsym_Fchar (a : ℝ → ℝ) (U : Forms) (z : ℂ) (hz : Fchar a U z = 0) :
    Fchar a U (-z) = 0 := by
  rw [Fchar_eq_expSum] at hz ⊢
  unfold thetaPlus thetaMinus thetaDPlus thetaDMinus at *
  cases hk : U.kind <;> simp only [hk] at hz ⊢ <;>
  · have e1 : ∀ x : ℂ, Complex.exp (-(Complex.I * -z * x)) = Complex.exp (Complex.I * z * x) := by
      intro x; congr 1; ring
    have e2 : ∀ x : ℂ, Complex.exp (Complex.I * -z * x) = Complex.exp (-(Complex.I * z * x)) := by
      intro x; congr 1; ring
    rw [e1, e2, e1, e2]
    first | linear_combination (-1 : ℂ) * hz | linear_combination hz

variable {a : ℝ → ℝ} {U : Forms}

/-- Положительность `L`, `|d| < L` из `Hyp a`. -/
theorem Ltot_dlt (h : Hyp a) : 0 < Ltot a ∧ |dlt a| < Ltot a := by
  obtain ⟨m, κ, h⟩ := h
  exact ⟨Ltot_pos h, abs_dlt_lt_Ltot h⟩

/-- lem:F (a), (c): при регулярности существует `h₀ ≥ 1` с оценкой снизу вне полосы и
числом нулей в прямоугольниках не более `N₀` (с кратностью). -/
theorem lem_F_ac (h : Hyp a) (hreg : Regular a U) :
    ∃ h₀ : ℝ, 1 ≤ h₀ ∧
      (∀ ρ : ℂ, h₀ ≤ |ρ.im| →
        (1 / 2) * ‖theta a U‖ * Real.exp (Ltot a * |ρ.im|) ≤ ‖Fchar a U ρ‖) ∧
      ∃ N₀ : ℕ, ∀ X : ℝ,
        {z : ℂ | Fchar a U z = 0 ∧ z.re ∈ Icc X (X + 1) ∧ |z.im| ≤ h₀}.Finite ∧
        ∑ᶠ z ∈ {z : ℂ | Fchar a U z = 0 ∧ z.re ∈ Icc X (X + 1) ∧ |z.im| ≤ h₀},
          (analyticOrderAt (Fchar a U) z).toNat ≤ N₀ := by
  obtain ⟨hL, hd⟩ := Ltot_dlt h
  rw [Fchar_eq_expPoly]
  obtain ⟨h₀, h1, hA⟩ := expPoly_lower_outside (θdp := thetaDPlus a U) (θdm := thetaDMinus a U)
    hL hd hreg (hm_Fchar a U)
  obtain ⟨N, hN⟩ := expPoly_count_rect hL hd hreg (by linarith) hA
  refine ⟨h₀, h1, hA, N, fun X => ?_⟩
  have hw : expPoly (theta a U) (thetaMinus a U) (thetaDPlus a U) (thetaDMinus a U)
      (Ltot a) (dlt a) ((h₀ : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have := hA ((h₀ : ℂ) * Complex.I) (by simp [abs_of_nonneg (by linarith : 0 ≤ h₀)])
    rw [h0, norm_zero] at this
    have hp : 0 < ‖theta a U‖ := norm_pos_iff.2 hreg
    have := Real.exp_pos (Ltot a * |((h₀ : ℂ) * Complex.I).im|)
    nlinarith
  have hfin : {z : ℂ | expPoly (theta a U) (thetaMinus a U) (thetaDPlus a U)
      (thetaDMinus a U) (Ltot a) (dlt a) z = 0 ∧ z.re ∈ Icc X (X + 1) ∧ |z.im| ≤ h₀}.Finite := by
    refine (expPoly_zeros_finite_ball hw ((X : ℂ)) (|X| + 1 + h₀ + 1)).subset fun z hz => ?_
    obtain ⟨h0, hr, hi⟩ := hz
    refine ⟨h0, ?_⟩
    rw [mem_closedBall, dist_eq_norm]
    have e1 : ‖z - X‖ ≤ |(z - X).re| + |(z - X).im| := Complex.norm_le_abs_re_add_abs_im _
    have : |(z - (X : ℂ)).re| ≤ 1 := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
    have h3 : |(z - (X : ℂ)).im| ≤ h₀ := by simpa using hi
    have := abs_nonneg X
    linarith
  refine ⟨hfin, ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact hN X _ (fun z hz => by
    have := (hfin.mem_toFinset).1 hz
    exact ⟨this.2.1.1, this.2.1.2, this.2.2, this.1⟩)

/-- lem:F (b). -/
theorem lem_F_b (h : Hyp a) (hreg : Regular a U) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℂ, (∀ z : ℂ, Fchar a U z = 0 → δ ≤ ‖ρ - z‖) →
      c * Real.exp (Ltot a * |ρ.im|) ≤ ‖Fchar a U ρ‖ := by
  obtain ⟨hL, hd⟩ := Ltot_dlt h
  rw [Fchar_eq_expPoly]
  obtain ⟨c, hc, H⟩ := expPoly_lower_dist (θdp := thetaDPlus a U) (θdm := thetaDMinus a U)
    hL hd hreg (hm_Fchar a U) hδ
  exact ⟨c, hc, fun ρ hρ => H ρ (fun z hz => by rw [dist_eq_norm]; exact hρ z hz)⟩

/-- lem:F (d): бесконечно много нулей, в том числе в `Re ρ > 0`. -/
theorem lem_F_d (h : Hyp a) (hreg : Regular a U) :
    {z : ℂ | Fchar a U z = 0 ∧ 0 < z.re}.Infinite := by
  obtain ⟨hL, hd⟩ := Ltot_dlt h
  have := expPoly_zeros_pos_re_infinite (θdp := thetaDPlus a U) (θdm := thetaDMinus a U)
    hL hd hreg (hm_Fchar a U) (by
      intro z hz
      rw [← Fchar_eq_expPoly] at hz ⊢
      exact hsym_Fchar a U z hz)
  rwa [← Fchar_eq_expPoly] at this

/-- lem:simple для `Fchar`. -/
theorem lem_simple (h : Hyp a) (hsr : StronglyRegular a U) :
    ∃ δ c₁ r_F : ℝ, 0 < δ ∧ 0 < c₁ ∧ ∀ ρ₀ : ℂ, Fchar a U ρ₀ = 0 → r_F < ρ₀.re →
      (∀ ρ : ℂ, Fchar a U ρ = 0 → ‖ρ - ρ₀‖ ≤ δ → ρ = ρ₀) ∧
      (∀ ρ : ℂ, ‖ρ - ρ₀‖ ≤ δ →
        c₁ * ‖ρ - ρ₀‖ * Real.exp (Ltot a * |ρ.im|) ≤ ‖Fchar a U ρ‖) ∧
      c₁ ≤ ‖deriv (Fchar a U) ρ₀‖ := by
  obtain ⟨hL, hd⟩ := Ltot_dlt h
  obtain ⟨hR, ⟨δs, hδs, hsep⟩, hfin⟩ := hsr
  unfold ZerosEventuallySimple at hfin
  rw [Fchar_eq_expPoly] at hsep hfin ⊢
  obtain ⟨δ, hδ, c₁, hc, rF, H⟩ := expPoly_simple_zero hL hd hR (hm_Fchar a U) hδs
    (fun z w hz hw h1 h2 hne => by simpa [dist_eq_norm] using hsep z w h1 h2 hz hw hne)
    (by convert hfin using 2; ext z; tauto)
  refine ⟨δ, c₁, rF, hδ, hc, fun ρ₀ h0 hr => ?_⟩
  obtain ⟨h1, h2, h3⟩ := H ρ₀ h0 hr
  exact ⟨fun ρ hρ hle => h1 ρ hρ (by rwa [dist_eq_norm]),
    fun ρ hρ => by simpa [dist_eq_norm] using h2 ρ (by rwa [dist_eq_norm]), h3⟩

end GeneralBC
end Involution
