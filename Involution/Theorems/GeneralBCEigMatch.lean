module

public import Involution.Theorems.GeneralBCEigSmall
public import Involution.Theorems.GeneralBCEigTransfer
public import Involution.Theorems.GeneralBCEigZer

/-! # Теорема thm:eig (b): биекция нулей `Δ` и `G` (пакет G6)

Нули `Δ` и `G` с кратностями — типы `ZerTy (mult Δ)`, `ZerTy (mult G)`. Строится биекция
`σ`, для которой `ρ - ρ' → 0` вне конечного множества, где `ρ = λ^{1/2}`. -/

@[expose] public noncomputable section

open Set Metric

namespace Involution
namespace GeneralBC

theorem finite_mult_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnz : ∃ z, f z ≠ 0)
    (R : ℝ) : {z : ℂ | ‖z‖ ≤ R ∧ mult f z ≠ 0}.Finite := by
  obtain ⟨z₀, hz₀⟩ := hnz
  have hlt : R < max R ‖z₀‖ + 1 := by have := le_max_left R ‖z₀‖; linarith
  have hz₀b : z₀ ∈ ball (0 : ℂ) (max R ‖z₀‖ + 1) := by
    rw [mem_ball_zero_iff]; have := le_max_right R ‖z₀‖; linarith
  have := zeros_finite (c := (0 : ℂ)) hlt hf.differentiableOn hz₀b hz₀
  exact this.subset (fun z hz => ⟨mem_closedBall_zero_iff.2 hz.1,
    eq_zero_of_mult_ne_zero (hf.analyticAt z) hz.2⟩)

theorem lab_eq_some {T : Type*} (π : ℂ → T) (b : ℝ) (lam : ℂ) (τ : T) :
    (if ‖lam‖ < b then none else some (π (lam ^ (1 / 2 : ℂ))) : Option T) = some τ ↔
      ¬ ‖lam‖ < b ∧ π (lam ^ (1 / 2 : ℂ)) = τ := by
  by_cases h : ‖lam‖ < b <;> simp [h]

theorem lab_eq_none {T : Type*} (π : ℂ → T) (b : ℝ) (lam : ℂ) :
    (if ‖lam‖ < b then none else some (π (lam ^ (1 / 2 : ℂ))) : Option T) = none ↔
      ‖lam‖ < b := by
  by_cases h : ‖lam‖ < b <;> simp [h]

theorem exists_nonzero_ne_zero_point {F : ℂ → ℂ} (hF : Continuous F) (hnz : ∃ z, F z ≠ 0) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧ F ρ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz⟩ := hnz
  apply hz
  have : F = fun _ => 0 := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hF continuous_const ?_
    intro x hx
    exact hcon x hx
  rw [this]

end GeneralBC
end Involution
