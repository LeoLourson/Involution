module

public import Involution.Estimates.GeneralBCDetMain
public import Involution.Folding.GeneralBCFsr

/-! # Лемма `lem:eta2`: оценка `η = O(1/|ρ|)` (пакет G8a, C26)

Повторяет доказательство `lem_det` с остатком `R = O(1/|ρ|)` из `lem_fsr2`: берём в
`core_bound` параметр `ε = C'/‖ρ‖`. Вывод `lem_fsr2` при `h = 0` входит гипотезой `hfsr2`;
вариант `lem_eta2_of_S54` подставляет `lem_fsr2`. -/

@[expose] public noncomputable section

open MeasureTheory Set Matrix Complex

namespace Involution
namespace GeneralBC

/-- Оценка для одного знака `s`: из остатка `‖R_ij‖ ≤ C/‖ρ‖` следует
`‖ρ^{1-κ}Δ(ρ²)/c_∗ − F‖ ≤ K C'/‖ρ‖ · e^{L|Im ρ|}` при больших `‖ρ‖`. -/
theorem eta2_small_s {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) {s : ℝ}
    (hs : ∃ (C r₁ : ℝ) (R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ),
      ∀ ρ : ℂ, -(0 : ℝ) ≤ s * ρ.im → r₁ ≤ ‖ρ‖ →
        (∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, ‖R x ρ i j‖ ≤ C / ‖ρ‖) ∧
        IsSol a ρ (fun x => Wmat a x * Dmat a x * (1 + R x ρ) * Emat a x ρ)) :
    ∃ (K r : ℝ), 1 ≤ r ∧ ∀ ρ : ℂ, -(0 : ℝ) ≤ s * ρ.im → r ≤ ‖ρ‖ →
      ‖ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) / cStar a U - Fchar a U ρ‖ ≤
        K / ‖ρ‖ * Real.exp (Ltot a * |ρ.im|) := by
  obtain ⟨C, r₁, R, hR⟩ := hs
  obtain ⟨ε₀, hε0, hε1, hCε, h768, -⟩ := exists_eps a U (η := 1) one_pos
  set C' : ℝ := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  refine ⟨Kc a U * C', max (max r₁ 1) (C' / ε₀), le_trans (le_max_right _ _) (le_max_left _ _),
    fun ρ hρs hρr => ?_⟩
  have hr1 : r₁ ≤ ‖ρ‖ := (le_max_left _ _).trans ((le_max_left _ _).trans hρr)
  have hone : 1 ≤ ‖ρ‖ := (le_max_right _ _).trans ((le_max_left _ _).trans hρr)
  have hdiv : C' / ε₀ ≤ ‖ρ‖ := (le_max_right _ _).trans hρr
  have hpos : 0 < ‖ρ‖ := lt_of_lt_of_le one_pos hone
  have hρ0 : ρ ≠ 0 := norm_pos_iff.1 hpos
  set ε : ℝ := C' / ‖ρ‖ with hε
  have hεpos : 0 < ε := by positivity
  have hεle : ε ≤ ε₀ := by
    rw [hε, div_le_iff₀ hpos]
    rw [div_le_iff₀ hε0] at hdiv
    linarith
  have hinv : ‖ρ⁻¹‖ ≤ ε := by
    rw [norm_inv, hε, ← one_div]
    exact div_le_div_of_nonneg_right hC'1 hpos.le
  have hRb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, ‖R x ρ i j‖ ≤ ε := fun x hx i j =>
    ((hR ρ hρs hr1).1 x hx i j).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) hpos.le)
  have hb := core_bound h hU hρ0 R (hR ρ hρs hr1).2 hεpos.le (hεle.trans hε1)
    ((mul_le_mul_of_nonneg_left hεle (Cc_nonneg a U)).trans hCε)
    (by linarith) hinv (hRb 0 ⟨le_rfl, zero_le_one⟩) (hRb 1 ⟨zero_le_one, le_rfl⟩)
  refine hb.trans (le_of_eq ?_)
  rw [hε]; ring

/-- Склейка двух знаков `s = ±1`. -/
theorem eta2_bound {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U)
    (hfsr2 : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      ∃ (C r₁ : ℝ) (R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ),
        ∀ ρ : ℂ, -(0 : ℝ) ≤ s * ρ.im → r₁ ≤ ‖ρ‖ →
          (∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, ‖R x ρ i j‖ ≤ C / ‖ρ‖) ∧
          IsSol a ρ (fun x => Wmat a x * Dmat a x * (1 + R x ρ) * Emat a x ρ)) :
    ∃ C r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ →
      ‖ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) / cStar a U - Fchar a U ρ‖ ≤
        C / ‖ρ‖ * Real.exp (Ltot a * |ρ.im|) := by
  obtain ⟨Kp, rp, -, hp⟩ := eta2_small_s h hU (hfsr2 1 (Or.inl rfl))
  obtain ⟨Km, rm, -, hm⟩ := eta2_small_s h hU (hfsr2 (-1) (Or.inr rfl))
  refine ⟨max Kp Km, max rp rm, fun ρ hρ => ?_⟩
  have he := Real.exp_pos (Ltot a * |ρ.im|)
  have hn : 0 ≤ (1 : ℝ) / ‖ρ‖ * Real.exp (Ltot a * |ρ.im|) := by positivity
  rcases le_total 0 ρ.im with hi | hi
  · refine (hp ρ (by simpa using hi) ((le_max_left _ _).trans hρ)).trans ?_
    rw [div_eq_mul_one_div Kp, div_eq_mul_one_div (max Kp Km), mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hn
  · refine (hm ρ (by simpa using hi) ((le_max_right _ _).trans hρ)).trans ?_
    rw [div_eq_mul_one_div Km, div_eq_mul_one_div (max Kp Km), mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hn

/-- **Лемма `lem:eta2`** (C26; `paper/exposition-G.tex`, `lem:eta2`): `η = O(1/|ρ|) e^{L|Im ρ|}`.
Вывод `lem_fsr2` при `h = 0` — гипотеза `hfsr2`. -/
theorem lem_eta2 {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U)
    (hfsr2 : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      ∃ (C r₁ : ℝ) (R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ),
        ∀ ρ : ℂ, -(0 : ℝ) ≤ s * ρ.im → r₁ ≤ ‖ρ‖ →
          (∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, ‖R x ρ i j‖ ≤ C / ‖ρ‖) ∧
          IsSol a ρ (fun x => Wmat a x * Dmat a x * (1 + R x ρ) * Emat a x ρ)) :
    ∃ η : ℂ → ℂ, DifferentiableOn ℂ η {0}ᶜ ∧
      (∀ ρ : ℂ, ρ ≠ 0 →
        ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) = cStar a U * (Fchar a U ρ + η ρ)) ∧
      ∃ C r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ → ‖η ρ‖ ≤ C / ‖ρ‖ * Real.exp (Ltot a * |ρ.im|) := by
  have hc := cStar_ne_zero h hU
  obtain ⟨C, r, hb⟩ := eta2_bound h hU hfsr2
  refine ⟨fun ρ => ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) / cStar a U - Fchar a U ρ,
    ?_, ?_, C, r, hb⟩
  · intro ρ hρ
    refine DifferentiableAt.differentiableWithinAt ?_
    have h1 : DifferentiableAt ℂ (fun ρ : ℂ => ρ ^ (1 - (kappaSum U : ℤ))) ρ :=
      differentiableAt_zpow.2 (Or.inl hρ)
    have h2 : DifferentiableAt ℂ (fun ρ : ℂ => Delta a U (ρ ^ 2)) ρ :=
      ((Delta_differentiable a U).comp (differentiable_pow 2)).differentiableAt
    exact ((h1.mul h2).div_const _).sub ((Fchar_differentiable a U).differentiableAt)
  · intro ρ _
    field_simp
    ring

/-- `lem:eta2` через `lem_fsr2` (теорема 1.2 из S54) при `a ∈ W²₁`. -/
theorem lem_eta2_of_S54 {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (ha2 : IsW21 a) {U : Forms}
    (hU : AdmissibleForms U) (hS : S54Theorem12) :
    ∃ η : ℂ → ℂ, DifferentiableOn ℂ η {0}ᶜ ∧
      (∀ ρ : ℂ, ρ ≠ 0 →
        ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) = cStar a U * (Fchar a U ρ + η ρ)) ∧
      ∃ C r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ → ‖η ρ‖ ≤ C / ‖ρ‖ * Real.exp (Ltot a * |ρ.im|) :=
  lem_eta2 h hU fun s hs => lem_fsr2 a ⟨m, κ, h⟩ ha2 hS 0 le_rfl s hs

/-- Единственность `η`: равенство при `ρ ≠ 0` однозначно определяет `η` вне нуля. -/
theorem eta_unique {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) {η₁ η₂ : ℂ → ℂ}
    (h1 : ∀ ρ : ℂ, ρ ≠ 0 →
      ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) = cStar a U * (Fchar a U ρ + η₁ ρ))
    (h2 : ∀ ρ : ℂ, ρ ≠ 0 →
      ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) = cStar a U * (Fchar a U ρ + η₂ ρ))
    {ρ : ℂ} (hρ : ρ ≠ 0) : η₁ ρ = η₂ ρ := by
  have hc := cStar_ne_zero h hU
  have := (h1 ρ hρ).symm.trans (h2 ρ hρ)
  have := mul_left_cancel₀ hc this
  exact add_left_cancel this

end GeneralBC
end Involution

end
