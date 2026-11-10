module

public import Involution.Folding.GeneralBCFoldMain

/-! # Предложение `prop:refl`, последняя фраза (C24, утверждение 6, шаг 17)

При чётном `a` из (H) вектор `(1, 1, 0, 0)` лежит в ядре `V₀ + V₁ Φ(1, λ)` для форм (E):
решение с чётными данными остаётся чётным (`w₁ = w₂`, `w₁' = w₂'`) по единственности для
системы, симметричной относительно перестановки компонент. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval Matrix

namespace Involution
namespace GeneralBC

variable {a : ℝ → ℝ} {U : Forms} {lam : ℂ}

theorem foldX_integral {m κ : ℝ} (hH : HypH a m κ) (lam : ℂ) (v : Fin 4 → ℂ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    foldX a lam v x = v + ∫ t in (0 : ℝ)..x, foldXd a lam v t := by
  have hsub : uIcc 0 x ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2
  have hint : IntervalIntegrable (foldXd a lam v) volume 0 x :=
    ((foldXd_continuousOn hH lam v).mono hsub).intervalIntegrable
  ext i
  rw [Pi.add_apply, integral_apply_pi hint]
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx.1
    (((foldX_comp_continuousOn a lam v i).mono (Icc_subset_Icc le_rfl hx.2)))
    (fun t ht => (hasDerivAt_foldX_pos hH lam v ⟨ht.1, lt_of_lt_of_le ht.2 hx.2⟩
      i).hasDerivWithinAt)
    (((foldXd_comp_continuousOn hH lam v i).mono hsub).intervalIntegrable)
  rw [this, foldX_zero]; ring

/-- Перестановка `0 ↔ 1`, `2 ↔ 3`. -/
def foldSwap (u : Fin 4 → ℂ) : Fin 4 → ℂ := ![u 1, u 0, u 3, u 2]

theorem foldB_swap (hev : ∀ x, a (-x) = a x) (lam : ℂ) (u : Fin 4 → ℂ) (t : ℝ) :
    (foldA0 t + lam • foldA1 a t) *ᵥ foldSwap u =
      foldSwap ((foldA0 t + lam • foldA1 a t) *ᵥ u) := by
  rw [foldB_mulVec', foldB_mulVec']
  ext i
  fin_cases i <;> simp [foldSwap, hev t]

/-- `foldSwap` как линейное отображение. -/
def foldSwapLin : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun := foldSwap
  map_add' u w := by ext i; fin_cases i <;> simp [foldSwap]
  map_smul' c u := by ext i; fin_cases i <;> simp [foldSwap]

theorem integral_foldSwap {f : ℝ → Fin 4 → ℂ} {x : ℝ} (hf : IntervalIntegrable f volume 0 x) :
    ∫ t in (0 : ℝ)..x, foldSwap (f t) = foldSwap (∫ t in (0 : ℝ)..x, f t) :=
  (foldSwapLin.toContinuousLinearMap).intervalIntegral_comp_comm hf

theorem foldSwap_foldX {m κ : ℝ} (hH : HypH a m κ) (hev : ∀ x, a (-x) = a x) (lam : ℂ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    foldSwap (foldX a lam ![1, 1, 0, 0] x) = foldX a lam ![1, 1, 0, 0] x := by
  set v : Fin 4 → ℂ := ![1, 1, 0, 0] with hvdef
  have hSv : foldSwap v = v := by ext i; fin_cases i <;> simp [foldSwap, hvdef]
  have hcont : ContinuousOn (fun t => foldSwap (foldX a lam v t)) (Icc 0 1) := by
    refine continuousOn_pi.2 fun i => ?_
    fin_cases i
    · exact foldX_comp_continuousOn a lam v 1
    · exact foldX_comp_continuousOn a lam v 0
    · exact foldX_comp_continuousOn a lam v 3
    · exact foldX_comp_continuousOn a lam v 2
  have key := linearCauchy_unique (A₀ := foldA0) (A₁ := foldA1 a) continuousOn_const
    (foldA1_continuousOn ⟨m, κ, hH⟩) lam (X := fun t => foldSwap (foldX a lam v t)) hcont
    (fun x hx => by
      have hsub : uIcc 0 x ⊆ Icc (0 : ℝ) 1 := by
        rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2
      have hint : IntervalIntegrable (foldXd a lam v) volume 0 x :=
        ((foldXd_continuousOn hH lam v).mono hsub).intervalIntegrable
      have e := foldX_integral hH lam v hx
      simp only [foldB_swap hev]
      have hS := integral_foldSwap hint
      change ∫ t in (0 : ℝ)..x, foldSwap (foldXd a lam v t) = _ at hS
      change foldSwap (foldX a lam v x) = foldSwap (foldX a lam v 0) +
        ∫ t in (0 : ℝ)..x, foldSwap (foldXd a lam v t)
      rw [hS, e, foldX_zero]
      ext i
      fin_cases i <;> simp [foldSwap]) x hx
  rw [key, foldX_zero, hSv]; rfl

/-- prop:refl, вторая часть: при чётном `a` каждое `λ` — собственное значение для форм (E). -/
theorem prop_refl_even_eigenvalue {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ)
    (hev : ∀ x, a (-x) = a x) (lam : ℂ) : IsEigenvalue a reflForms lam := by
  rw [isEigenvalue_iff_Delta_eq_zero ⟨m, κ, h⟩]
  unfold Delta
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨![1, 1, 0, 0], ?_, ?_⟩
  · intro h0
    have := congrFun h0 0
    simp at this
  · have hs := foldSwap_foldX h hev lam (x := 1) ⟨by norm_num, le_rfl⟩
    have s0 := congrFun hs 0
    have s2 := congrFun hs 2
    simp only [foldSwap] at s0 s2
    simp at s0 s2
    rw [foldMat_mulVec_eq]
    ext i
    fin_cases i <;>
      simp [foldV0, foldV1, reflForms, dotProduct, Fin.sum_univ_four]
    · linear_combination s2.symm
    · linear_combination s0.symm
end GeneralBC
end Involution
