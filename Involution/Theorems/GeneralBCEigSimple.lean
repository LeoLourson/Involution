module

public import Involution.Theorems.GeneralBCEigLocal
public import Involution.Theorems.GeneralBCEigKernel

/-! # Теорема thm:eig (c): простота далёких нулей и одномерность собственных подпространств (G6)

Ненумерованная форма утверждения (c): все собственные значения с достаточно большим `‖λ‖`
являются простыми нулями `Δ`, и их собственные подпространства одномерны. -/

@[expose] public noncomputable section

namespace Involution
namespace GeneralBC

/-- Одномерность собственного подпространства в простом нуле `Δ` (при (H)). -/
theorem finrank_foldEigSpace_eq_one {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    {lam : ℂ} (hz : Delta a U lam = 0) (hord : analyticOrderAt (Delta a U) lam = 1) :
    Module.finrank ℂ (FoldEigSpace a U lam) = 1 := by
  have hA : AnalyticAt ℂ (Delta a U) lam := (Delta_differentiable a U).analyticAt lam
  have hd := deriv_ne_zero_of_analyticOrderAt_eq_one hA hord
  rw [(foldEquiv (U := U) (lam := lam) ⟨m, κ, h⟩).finrank_eq]
  exact finrank_ker_eq_one_of_deriv_det_ne_zero (M := foldMat a U)
    (foldMat_entry_differentiable a U) hz hd

/-- **thm:eig (c)**: при сильной регулярности все собственные значения с большим `‖λ‖` —
простые нули `Δ` с одномерным собственным подпространством. -/
theorem thm_eig_c {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (hreg : Regular a U) (hsr : StronglyRegular a U)
    (hdet : DetPrincipalPart a U) :
    ∃ R : ℝ, ∀ lam : ℂ, R ≤ ‖lam‖ → IsEigenvalue a U lam →
      analyticOrderAt (Delta a U) lam = 1 ∧ Module.finrank ℂ (FoldEigSpace a U lam) = 1 := by
  obtain ⟨R, hR⟩ := large_zero_simple h hU hreg hsr hdet
  refine ⟨R ^ 2, fun lam hlam hev => ?_⟩
  have hz : Delta a U lam = 0 := (isEigenvalue_iff_Delta_eq_zero ⟨m, κ, h⟩).1 hev
  have hn : ‖lam ^ (1 / 2 : ℂ)‖ ^ 2 = ‖lam‖ := by
    rw [← norm_pow, cpow_half_sq]
  have hRle : R ≤ ‖lam ^ (1 / 2 : ℂ)‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have : ‖lam‖ < R ^ 2 := by
      by_cases hR0 : 0 ≤ R
      · rw [← hn]; exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
      · exfalso
        have := norm_nonneg (lam ^ (1 / 2 : ℂ)); linarith
    linarith
  have hz' : Delta a U ((lam ^ (1 / 2 : ℂ)) ^ 2) = 0 := by rw [cpow_half_sq]; exact hz
  have hord := hR _ hRle (re_cpow_half_nonneg lam) hz'
  rw [cpow_half_sq] at hord
  exact ⟨hord, finrank_foldEigSpace_eq_one h hz hord⟩

end GeneralBC
end Involution
