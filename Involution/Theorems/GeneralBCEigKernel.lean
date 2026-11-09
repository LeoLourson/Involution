module

public import Involution.Folding.GeneralBCFoldMain
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Простой нуль определителя и одномерность ядра (пакет G6)

Если определитель `det M(λ)` целой матрицы-функции имеет в `λ₀` нуль с ненулевой производной,
то ядро `M(λ₀)` одномерно. Доказательство через сопряжённую матрицу: при `dim ker ≥ 2` все
элементы `adj M(λ₀)` равны нулю, дифференцирование тождества `M adj M = det M · I` даёт
`M(λ₀) X = (det M)'(λ₀) · I` и обратимость `M(λ₀)`. -/

@[expose] public noncomputable section

open Matrix

namespace Involution
namespace GeneralBC

theorem foldMat_entry_differentiable (a : ℝ → ℝ) (U : Forms) (i j : Fin 4) :
    Differentiable ℂ (fun l => foldMat a U l i j) := by
  simp only [foldMat, Matrix.add_apply, Matrix.mul_apply]
  exact (differentiable_const _).add (Differentiable.fun_sum fun k _ =>
    (differentiable_linearCauchy _ _ _ _ _).const_mul _)

theorem differentiable_det_entries {n : Type*} [Fintype n] [DecidableEq n]
    {M : ℂ → Matrix n n ℂ} (hM : ∀ i j, Differentiable ℂ (fun l => M l i j)) :
    Differentiable ℂ (fun l => (M l).det) := by
  simp only [Matrix.det_apply']
  refine Differentiable.fun_sum (fun σ _ => ?_)
  refine Differentiable.const_mul ?_ _
  exact Differentiable.fun_finsetProd (fun k _ => hM _ _)

theorem differentiable_adjugate_entries {n : Type*} [Fintype n] [DecidableEq n]
    {M : ℂ → Matrix n n ℂ} (hM : ∀ i j, Differentiable ℂ (fun l => M l i j)) (j k : n) :
    Differentiable ℂ (fun l => (M l).adjugate j k) := by
  simp only [Matrix.adjugate_apply]
  refine differentiable_det_entries (M := fun l => (M l).updateRow k (Pi.single j 1)) ?_
  intro p q
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiable_const _
  · exact hM p q

/-- Если `dim ker A ≥ 2`, то `adj A = 0`. -/
theorem adjugate_eq_zero_of_two_le_finrank {A : Matrix (Fin 4) (Fin 4) ℂ}
    (h2 : 2 ≤ Module.finrank ℂ (LinearMap.ker A.mulVecLin)) : A.adjugate = 0 := by
  ext i j
  rw [Matrix.adjugate_apply]
  simp only [Matrix.zero_apply]
  let φ : LinearMap.ker A.mulVecLin →ₗ[ℂ] ℂ :=
    (LinearMap.proj i).comp (LinearMap.ker A.mulVecLin).subtype
  have hlt : Module.finrank ℂ ℂ < Module.finrank ℂ (LinearMap.ker A.mulVecLin) := by
    rw [Module.finrank_self]; omega
  obtain ⟨v, hvφ, hv0⟩ := (Submodule.ne_bot_iff _).1
    (LinearMap.ker_ne_bot_of_finrank_lt (f := φ) hlt)
  have hvi : (v : Fin 4 → ℂ) i = 0 := hvφ
  have hAv : A *ᵥ (v : Fin 4 → ℂ) = 0 := v.2
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨(v : Fin 4 → ℂ), ?_, ?_⟩
  · intro h; exact hv0 (Subtype.ext h)
  · ext k
    simp only [Matrix.mulVec, Matrix.updateRow_apply]
    split_ifs with hk
    · simp [dotProduct, Pi.single_apply, hvi]
    · have := congrFun hAv k
      simpa [Matrix.mulVec] using this

/-- Простой нуль определителя влечёт одномерность ядра. -/
theorem finrank_ker_eq_one_of_deriv_det_ne_zero {M : ℂ → Matrix (Fin 4) (Fin 4) ℂ}
    (hM : ∀ i j, Differentiable ℂ (fun l => M l i j)) {l0 : ℂ} (h0 : (M l0).det = 0)
    (hd : deriv (fun l => (M l).det) l0 ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (M l0).mulVecLin) = 1 := by
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker (M l0).mulVecLin) := by
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hMv⟩, ?_⟩
    intro h; exact hv (congrArg Subtype.val h)
  by_contra hne
  have h2 : 2 ≤ Module.finrank ℂ (LinearMap.ker (M l0).mulVecLin) := by omega
  have hadj := adjugate_eq_zero_of_two_le_finrank h2
  set X : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun j k => deriv (fun l => (M l).adjugate j k) l0
    with hX
  have key : ∀ i k, ∑ j, (M l0) i j * X j k =
      if i = k then deriv (fun l => (M l).det) l0 else 0 := by
    intro i k
    have hid : (fun l => ∑ j, M l i j * (M l).adjugate j k) =
        fun l => if i = k then (M l).det else 0 := by
      funext l
      have := congrFun (congrFun (Matrix.mul_adjugate (M l)) i) k
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
      rw [this]; split_ifs <;> simp
    have h1 : HasDerivAt (fun l => ∑ j, M l i j * (M l).adjugate j k)
        (∑ j, (deriv (fun l => M l i j) l0 * (M l0).adjugate j k +
          M l0 i j * deriv (fun l => (M l).adjugate j k) l0)) l0 := by
      refine HasDerivAt.fun_sum (fun j _ => ?_)
      exact ((hM i j) l0).hasDerivAt.mul ((differentiable_adjugate_entries hM j k) l0).hasDerivAt
    have h2' : HasDerivAt (fun l => if i = k then (M l).det else 0)
        (if i = k then deriv (fun l => (M l).det) l0 else 0) l0 := by
      split_ifs
      · exact ((differentiable_det_entries hM) l0).hasDerivAt
      · exact hasDerivAt_const _ _
    rw [hid] at h1
    have := h1.unique h2'
    rw [← this]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hadj]; simp [hX]
  have hAX : (M l0) * X = (deriv (fun l => (M l).det) l0) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    ext i k
    rw [Matrix.mul_apply, key]
    simp [Matrix.one_apply]
  have hinv : (M l0) * ((deriv (fun l => (M l).det) l0)⁻¹ • X) = 1 := by
    rw [Matrix.mul_smul, hAX, smul_smul, inv_mul_cancel₀ hd, one_smul]
  exact (Matrix.det_ne_zero_of_right_inverse hinv) h0

end GeneralBC
end Involution
