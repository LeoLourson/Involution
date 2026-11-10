module

public import Involution.Setup.Rouche
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Планарные данные и теорема Руше для круга (пакет G6, thm:eig (b))

`PlanarData F η L` собирает свойства главной части `F` и остатка `η`, нужные для сопоставления
нулей: оценки леммы lem:F и малость `η`. Круг `B(c₀, s)`, граница которого удалена от нулей `F`
не меньше чем на `δ`, содержит одинаково много нулей `F` и `F + η`. -/

@[expose] public noncomputable section

open Set Metric

namespace Involution
namespace GeneralBC

/-- Свойства пары `(F, η)` с показателем `L`: `F` целая, `η` голоморфна при `ρ ≠ 0`, нули `F`
лежат в полосе `|Im ρ| < h₀`, в единичных прямоугольниках их не больше `N₀`, оценка снизу
вне окрестностей нулей, малость `η`. -/
structure PlanarData (F η : ℂ → ℂ) (L : ℝ) : Prop where
  entire : Differentiable ℂ F
  eta_diff : DifferentiableOn ℂ η {0}ᶜ
  count : ∃ (h₀ : ℝ) (N₀ : ℕ), (∀ z, F z = 0 → |z.im| < h₀) ∧ ∀ X : ℝ,
    {z : ℂ | F z = 0 ∧ z.re ∈ Icc X (X + 1) ∧ |z.im| ≤ h₀}.Finite ∧
    ∑ᶠ z ∈ {z : ℂ | F z = 0 ∧ z.re ∈ Icc X (X + 1) ∧ |z.im| ≤ h₀},
      (analyticOrderAt F z).toNat ≤ N₀
  lowb : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℂ, (∀ z : ℂ, F z = 0 → δ ≤ ‖ρ - z‖) →
    c * Real.exp (L * |ρ.im|) ≤ ‖F ρ‖
  small : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ →
    ‖η ρ‖ * Real.exp (-L * |ρ.im|) ≤ ε
  nz : ∃ z, F z ≠ 0

variable {F η : ℂ → ℂ} {L : ℝ}

theorem rouche_disc (hP : PlanarData F η L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, ∀ (c₀ : ℂ) (s : ℝ), 0 < s → r + s ≤ ‖c₀‖ →
      (∀ z, F z = 0 → δ ≤ |‖z - c₀‖ - s|) →
      zeroCount F c₀ s = zeroCount (fun w => F w + η w) c₀ s ∧
      (ball c₀ s ∩ Function.support (zeroMult (fun w => F w + η w))).Finite := by
  obtain ⟨c, hc, hb⟩ := hP.lowb δ hδ
  obtain ⟨r₀, hr₀⟩ := hP.small (c / 2) (by positivity)
  refine ⟨max r₀ 1, fun c₀ s hs hcs hz => ?_⟩
  have hcs1 : s < ‖c₀‖ := by have := le_max_right r₀ 1; linarith
  have hcl : closedBall c₀ s ⊆ ({0}ᶜ : Set ℂ) := by
    intro w hw h0
    have hw' : ‖w - c₀‖ ≤ s := by simpa [dist_eq_norm] using hw
    rw [Set.mem_singleton_iff] at h0
    subst h0
    simp only [zero_sub, norm_neg] at hw'
    linarith
  have hfg : ∀ w ∈ sphere c₀ s, ‖η w‖ < ‖F w‖ := by
    intro w hw
    have hws : ‖w - c₀‖ = s := by simpa [dist_eq_norm] using hw
    have hwn : r₀ ≤ ‖w‖ := by
      have h1 : ‖c₀‖ - ‖w - c₀‖ ≤ ‖w‖ := by
        have := norm_sub_norm_le c₀ (c₀ - w)
        rw [norm_sub_rev] at this
        simpa [sub_sub_cancel] using this
      have := le_max_left r₀ 1
      linarith
    have h1 := hb w (fun z hzz => by
      have h2 := hz z hzz
      have h3 : |‖z - c₀‖ - s| ≤ ‖w - z‖ := by
        rw [← hws]
        have := abs_norm_sub_norm_le (z - c₀) (w - c₀)
        rwa [show (z - c₀) - (w - c₀) = -(w - z) by ring, norm_neg] at this
      linarith)
    have h2 := hr₀ w hwn
    have h4 : ‖η w‖ ≤ c / 2 * Real.exp (L * |w.im|) := by
      have hexp : Real.exp (-L * |w.im|) * Real.exp (L * |w.im|) = 1 := by
        rw [← Real.exp_add]; simp
      calc ‖η w‖ = ‖η w‖ * (Real.exp (-L * |w.im|) * Real.exp (L * |w.im|)) := by
            rw [hexp, mul_one]
        _ = ‖η w‖ * Real.exp (-L * |w.im|) * Real.exp (L * |w.im|) := by ring
        _ ≤ c / 2 * Real.exp (L * |w.im|) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    have := Real.exp_pos (L * |w.im|)
    nlinarith
  refine ⟨rouche isOpen_compl_singleton hcl hs hP.entire.differentiableOn hP.eta_diff hfg, ?_⟩
  -- конечность нулей `F + η` в круге
  have hball : ball c₀ ‖c₀‖ ⊆ ({0}ᶜ : Set ℂ) := by
    intro w hw h0
    rw [Set.mem_singleton_iff] at h0
    subst h0
    simp [dist_eq_norm] at hw
  have hd : DifferentiableOn ℂ (fun w => F w + η w) (ball c₀ ‖c₀‖) :=
    (hP.entire.differentiableOn.mono hball).add (hP.eta_diff.mono hball)
  have hp : c₀ + (s : ℂ) ∈ sphere c₀ s := by
    simp [abs_of_pos hs]
  have hne : F (c₀ + (s : ℂ)) + η (c₀ + (s : ℂ)) ≠ 0 := by
    intro h0
    have h1 := hfg _ hp
    have : F (c₀ + (s : ℂ)) = -η (c₀ + (s : ℂ)) := eq_neg_of_add_eq_zero_left h0
    rw [this, norm_neg] at h1
    exact lt_irrefl _ h1
  have hpb : c₀ + (s : ℂ) ∈ ball c₀ ‖c₀‖ := by
    simp [dist_eq_norm, abs_of_pos hs, hcs1]
  exact zeroMult_support_finite hcs1 hd hpb hne

end GeneralBC
end Involution
