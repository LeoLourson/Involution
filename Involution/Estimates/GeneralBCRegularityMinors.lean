module

public import Involution.Estimates.GeneralBCRegularityPos
public import Involution.Folding.GeneralBCAdmissible

/-! # Миноры `J₀`, `J₁` и постоянная `γ_U` (пакет G5)

Для допустимых форм: `J₀ ≠ 0` при виде `(0,0)` (линейная независимость), `J₁ ≠ 0` при виде
`(1,1)` (нормированность), `γ_U ≠ 0` при (H). -/

@[expose] public noncomputable section

namespace Involution
namespace GeneralBC

variable {a : ℝ → ℝ} {m κ : ℝ} {U : Forms}

theorem Forms.kind_k00 (hk : U.kind = Forms.Kind.k00) : ¬U.HasDeriv 0 ∧ ¬U.HasDeriv 1 := by
  by_contra hc
  unfold Forms.kind at hk
  simp only [hc, ↓reduceIte] at hk
  split_ifs at hk

theorem Forms.kind_k11 (hk : U.kind = Forms.Kind.k11) : U.HasDeriv 0 ∧ U.HasDeriv 1 := by
  by_cases h1 : ¬U.HasDeriv 0 ∧ ¬U.HasDeriv 1
  · unfold Forms.kind at hk
    simp only [h1] at hk
    cases hk
  · by_contra h2
    unfold Forms.kind at hk
    simp only [h1, h2, ↓reduceIte] at hk
    cases hk

theorem Forms.ord_le_one (U : Forms) (j : Fin 2) : U.ord j ≤ 1 := by
  classical
  unfold Forms.ord; split_ifs <;> omega

theorem Forms.ord_of_hasDeriv {U : Forms} {j : Fin 2} (h : U.HasDeriv j) : U.ord j = 1 := by
  classical
  simp only [Forms.ord, h, ↓reduceIte]

theorem Forms.ord_of_not {U : Forms} {j : Fin 2} (h : ¬ U.HasDeriv j) : U.ord j = 0 := by
  classical
  simp only [Forms.ord, h, ↓reduceIte]

/-- `J₀ ≠ 0` для вида `(0,0)` (линейная независимость). -/
theorem J0_ne_zero (hU : AdmissibleForms U) (hk : U.kind = Forms.Kind.k00) : U.J0 ≠ 0 := by
  obtain ⟨h0, h1⟩ := Forms.kind_k00 hk
  simp only [Forms.HasDeriv, not_or, not_not] at h0 h1
  intro hJ
  have key : ∀ g0 g1 : ℂ, g0 * U.α 0 0 + g1 * U.α 1 0 = 0 → g0 * U.β 0 0 + g1 * U.β 1 0 = 0 →
      g0 = 0 ∧ g1 = 0 := by
    intro g0 g1 e1 e2
    have := Fintype.linearIndependent_iff.1 hU.indep ![g0, g1] (by
      funext c
      fin_cases c <;> simp [Forms.row, Fin.sum_univ_two, h0.1, h0.2, h1.1, h1.2, e1, e2])
    exact ⟨this 0, this 1⟩
  unfold Forms.J0 at hJ
  have r1 := key (U.α 1 0) (-U.α 0 0) (by ring) (by linear_combination -hJ)
  have r2 := key (U.β 1 0) (-U.β 0 0) (by linear_combination hJ) (by ring)
  have r3 := key 1 0 (by simp [r1.1, neg_eq_zero.1 r1.2]) (by simp [r2.1, neg_eq_zero.1 r2.2])
  exact one_ne_zero r3.1

/-- Для комбинации с нулевым старшим коэффициентом порядок равен нулю. -/
theorem ord_combo_zero (U : Forms) (c0 c1 : ℂ)
    (e1 : c0 * U.α 0 1 + c1 * U.α 1 1 = 0) (e2 : c0 * U.β 0 1 + c1 * U.β 1 1 = 0)
    (c : Matrix (Fin 2) (Fin 2) ℂ) (h0 : c 0 0 = c0) (h1 : c 0 1 = c1) :
    (U.combo c).ord 0 = 0 := by
  apply Forms.ord_of_not
  simp only [Forms.HasDeriv, Forms.combo, Fin.sum_univ_two, h0, h1, not_or, not_not]
  exact ⟨e1, e2⟩

/-- `J₁ ≠ 0` для вида `(1,1)` (нормированность). -/
theorem J1_ne_zero (hU : AdmissibleForms U) (hk : U.kind = Forms.Kind.k11) : U.J1 ≠ 0 := by
  obtain ⟨h0, h1⟩ := Forms.kind_k11 hk
  intro hJ
  unfold Forms.J1 at hJ
  have hnorm := hU.normalized
  -- ненулевой вектор `(c0, c1)`, гасящий старшие коэффициенты
  obtain ⟨c0, c1, hne, e1, e2⟩ : ∃ c0 c1 : ℂ, (c0 ≠ 0 ∨ c1 ≠ 0) ∧
      c0 * U.α 0 1 + c1 * U.α 1 1 = 0 ∧ c0 * U.β 0 1 + c1 * U.β 1 1 = 0 := by
    by_cases hα : U.α 1 1 = 0 ∧ U.α 0 1 = 0
    · refine ⟨U.β 1 1, -U.β 0 1, ?_, by rw [hα.1, hα.2]; ring, by ring⟩
      right
      have : U.β 0 1 ≠ 0 := by
        rcases h0 with h | h
        · exact absurd hα.2 h
        · exact h
      exact neg_ne_zero.2 this
    · refine ⟨U.α 1 1, -U.α 0 1, ?_, by ring, by linear_combination hJ⟩
      by_contra hc
      rcases not_or.1 hc with ⟨hc1, hc2⟩
      exact hα ⟨not_not.1 hc1, neg_eq_zero.1 (not_not.1 hc2)⟩
  by_cases hc1 : c1 = 0
  · have hc0 : c0 ≠ 0 := by tauto
    let M : Matrix (Fin 2) (Fin 2) ℂ := !![c0, c1; 0, 1]
    have hdet : IsUnit M.det := by
      rw [isUnit_iff_ne_zero, Matrix.det_fin_two_of]; simpa using hc0
    have := hnorm M hdet
    rw [ord_combo_zero U c0 c1 e1 e2 M rfl rfl, Forms.ord_of_hasDeriv h0,
      Forms.ord_of_hasDeriv h1] at this
    have := Forms.ord_le_one (U.combo M) 1
    omega
  · let M : Matrix (Fin 2) (Fin 2) ℂ := !![c0, c1; 1, 0]
    have hdet : IsUnit M.det := by
      rw [isUnit_iff_ne_zero, Matrix.det_fin_two_of]; simpa using hc1
    have := hnorm M hdet
    rw [ord_combo_zero U c0 c1 e1 e2 M rfl rfl, Forms.ord_of_hasDeriv h0,
      Forms.ord_of_hasDeriv h1] at this
    have := Forms.ord_le_one (U.combo M) 1
    omega

/-- `γ_U ≠ 0` при (H) и допустимых формах. -/
theorem gammaU_ne_zero (h : HypH a m κ) (hU : AdmissibleForms U) : gammaU a U ≠ 0 := by
  have hk := regularity_varkappa_ne_zero h
  have hI := Complex.I_ne_zero
  have hk' : (varkappa a : ℂ) ≠ 0 := by exact_mod_cast hk
  have hw1 : (omega a 1 : ℂ) ≠ 0 := by exact_mod_cast (regularity_omega_pos h (Or.inl rfl)).ne'
  have hw2 : (omega a (-1) : ℂ) ≠ 0 := by exact_mod_cast (regularity_omega_pos h (Or.inr rfl)).ne'
  have he : (eps a : ℂ) ≠ 0 := by exact_mod_cast eps_ne_zero a
  unfold gammaU
  cases hkind : U.kind
  · have := J0_ne_zero hU hkind
    simp [hI, hk', this]
  · have := J1_ne_zero hU hkind
    simp [hI, hk', hw1, hw2, this]
  · simp [hI, he]

end GeneralBC
end Involution
