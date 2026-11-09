module

public import Involution.Folding.GeneralBCFsrBasic

/-! # lem:fsr и lem:fsr2 (G2c)

lem:fsr (C24 шаги 4–6): асимптотическая фундаментальная матрица `Y_a = W 𝐃 (I + R) E` системы
`Y' = ρ K Y`. Сложенная система приведена заменой `Y = W 𝐃 Z̃` к `Z̃' = (Ã + ρ Λ) Z̃`
(`HypH.transfer`); `Ã` суммируема, диагональ нулевая, `Λ = i diag(c_j)`, `c_j` попарно различны.
Применяется теорема 1.5 из S51 (`S51Theorem15`), как в статье; нулевая диагональ `Ã` даёт
`M = I`. lem:fsr2 (C26 шаги 2–3): то же с теоремой 1.2 из S54 (`S54Theorem12`) при
`a ∈ W²₁`, остаток `O(1/|ρ|)`. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution.GeneralBC

/-- lem:fsr (C24 шаг 6, формула (5)): асимптотическая фундаментальная матрица
`Y_a = W 𝐃 (I + R) E` системы `Y' = ρ K Y` в `Im(sρ) ≥ −h`. Внешний вход — теорема 1.5 S51. -/
theorem lem_fsr (a : ℝ → ℝ) (ha : Hyp a) (hS : S51Theorem15) (h : ℝ) (hh : 0 ≤ h) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    ∃ R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ,
      UniformlySmall R {ρ | -h ≤ s * ρ.im} ∧
      ∃ r₀ : ℝ, ∀ ρ : ℂ, -h ≤ s * ρ.im → r₀ ≤ ‖ρ‖ →
        IsSol a ρ (fun x => Wmat a x * Dmat a x * (1 + R x ρ) * Emat a x ρ) := by
  obtain ⟨m, κ, hH⟩ := ha
  obtain ⟨R, hR, r₀, hsol⟩ := hS (cfun a) (Atilde a) hH.continuousOn_cfun
    (fun x hx _ _ hij => hH.cfun_ne (mem_Icc_neg_one_of_mem hx) hij) hH.integrable_Atilde s h hs hh
  refine ⟨R, hR, r₀, fun ρ hρ hr => ?_⟩
  refine hH.fsr_bridge ρ (fun x => R x ρ) (Atilde a) (Filter.Eventually.of_forall fun _ _ => rfl)
    (fun x _ j => by simp [Atilde_diag]) (hsol ρ hρ hr)

/-- Диагональные интегралы `B`, совпадающей с `Ã` п.в., нулевые. -/
theorem integral_diag_zero {a : ℝ → ℝ} {B : ℝ → Matrix (Fin 4) (Fin 4) ℂ}
    (hBae : ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → Atilde a x = B x) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ j, (∫ t in (0 : ℝ)..x, B t j j) = 0 := by
  intro x hx j
  have : (∫ t in (0 : ℝ)..x, B t j j) = ∫ t in (0 : ℝ)..x, (0 : ℂ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hBae] with t ht htI
    rw [uIoc_of_le hx.1] at htI
    rw [← ht ⟨htI.1.le, htI.2.trans hx.2⟩, Atilde_diag]
  simpa using this

/-- lem:fsr2 (C26 шаги 2–3): при `a ∈ W²₁` остаток `R = O(1/|ρ|)`. Внешний вход —
теорема 1.2 S54. -/
theorem lem_fsr2 (a : ℝ → ℝ) (ha : Hyp a) (ha2 : IsW21 a) (hS : S54Theorem12) (h : ℝ)
    (hh : 0 ≤ h) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∃ (C r₁ : ℝ) (R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ),
      ∀ ρ : ℂ, -h ≤ s * ρ.im → r₁ ≤ ‖ρ‖ →
        (∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, ‖R x ρ i j‖ ≤ C / ‖ρ‖) ∧
        IsSol a ρ (fun x => Wmat a x * Dmat a x * (1 + R x ρ) * Emat a x ρ) := by
  obtain ⟨m, κ, hH⟩ := ha
  obtain ⟨B, hBac, hBae⟩ := hH.Atilde_offdiag_ac ha2
  have hdist : ∀ x ∈ Icc (0 : ℝ) 1, ∀ i j : Fin 4, i ≠ j → cfun a i x ≠ cfun a j x :=
    fun x hx _ _ hij => hH.cfun_ne (mem_Icc_neg_one_of_mem hx) hij
  have hdi : ∀ i : Fin 4, IntervalIntegrable (fun x => B x i i) volume 0 1 := fun i =>
    (hBac i i).continuousOn.intervalIntegrable
  have hoff : ∀ i j : Fin 4, i ≠ j → AbsolutelyContinuousOnInterval (fun x => B x i j) 0 1 :=
    fun i j _ => hBac i j
  obtain ⟨C, r₁, 𝓔, hsol⟩ := hS (cfun a) B hH.ac_cfun hdist hdi hoff s h hs hh
  refine ⟨C, r₁, 𝓔, fun ρ hρ hr => ⟨(hsol ρ hρ hr).1, ?_⟩⟩
  exact hH.fsr_bridge ρ (fun x => 𝓔 x ρ) B hBae (integral_diag_zero hBae) (hsol ρ hρ hr).2

end Involution.GeneralBC

end
