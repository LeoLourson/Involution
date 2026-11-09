module

public import Involution.Folding.GeneralBCAdmissible
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Перестановка форм `U₁ ↔ U₂` (пакет G5)

`Forms.swap` меняет формы местами. Сохраняются линейная независимость, нормированность,
собственные значения и собственные пары. Для любой пары одна из `U`, `U.swap` удовлетворяет
`IsOrdered` (обе — при `κ₁ = κ₂`), поэтому `AdmissibleForms` достигается перестановкой. -/

@[expose] public noncomputable section

namespace Involution
namespace GeneralBC
namespace Forms

/-- Перестановка форм: `U.swap = (U₂, U₁)`. -/
def swap (U : Forms) : Forms where
  α j i := U.α j.rev i
  β j i := U.β j.rev i

@[simp] theorem swap_swap (U : Forms) : U.swap.swap = U := by
  cases U; simp [swap, Fin.rev_rev]

theorem eval_swap (U : Forms) (j : Fin 2) (y y' : ℝ → ℂ) :
    U.swap.eval j y y' = U.eval j.rev y y' := rfl

theorem row_swap (U : Forms) (j : Fin 2) : U.swap.row j = U.row j.rev := rfl

theorem hasDeriv_swap (U : Forms) (j : Fin 2) : U.swap.HasDeriv j ↔ U.HasDeriv j.rev := Iff.rfl

theorem ord_swap (U : Forms) (j : Fin 2) : U.swap.ord j = U.ord j.rev := by
  classical
  unfold ord
  exact if_congr Iff.rfl rfl rfl

theorem linIndep_swap_of {U : Forms} (h : U.LinIndep) : U.swap.LinIndep := by
  have : U.swap.row = U.row ∘ Fin.rev := funext fun j => row_swap U j
  unfold LinIndep at *
  rw [this]
  exact h.comp _ Fin.rev_injective

/-- `swap` сохраняет линейную независимость. -/
theorem linIndep_swap_iff (U : Forms) : U.swap.LinIndep ↔ U.LinIndep :=
  ⟨fun h => by simpa using linIndep_swap_of h, linIndep_swap_of⟩

theorem combo_swap (U : Forms) (c : Matrix (Fin 2) (Fin 2) ℂ) :
    U.swap.combo c = U.combo (c.submatrix id Fin.rev) := by
  have e : ∀ f : Fin 2 → ℂ, ∑ l, f (Fin.rev l) = ∑ l, f l := fun f =>
    Equiv.sum_comp Fin.revPerm f
  cases U
  simp only [combo, swap, Matrix.submatrix_apply, id_eq]
  congr 1 <;> funext j i
  · exact (e (fun l => c j l * _)).symm
  · exact (e (fun l => c j l * _)).symm

theorem isUnit_det_submatrix_rev {c : Matrix (Fin 2) (Fin 2) ℂ} (hc : IsUnit c.det) :
    IsUnit (c.submatrix id Fin.rev).det := by
  rw [isUnit_iff_ne_zero] at *
  have h := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin 2)) c
  have h' : (c.submatrix id Fin.revPerm).det = (c.submatrix id Fin.rev).det := rfl
  rw [← h', h]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin 2))) with h1 | h1
  · rw [h1]; simpa using hc
  · rw [h1]; simpa using hc

theorem isNormalized_swap_of {U : Forms} (h : U.IsNormalized) : U.swap.IsNormalized := by
  intro c hc
  have := h _ (isUnit_det_submatrix_rev hc)
  rw [← combo_swap] at this
  have e1 : U.swap.ord 0 + U.swap.ord 1 = U.ord 0 + U.ord 1 := by
    rw [ord_swap, ord_swap]; exact add_comm _ _
  have e2 := ord_swap (U.combo (c.submatrix id Fin.rev)).swap
  rw [e1]
  have e3 : (U.swap.combo c).ord 0 + (U.swap.combo c).ord 1 =
      (U.combo (c.submatrix id Fin.rev)).ord 0 + (U.combo (c.submatrix id Fin.rev)).ord 1 := by
    rw [combo_swap]
  rw [e3]
  exact h _ (isUnit_det_submatrix_rev hc)

/-- `swap` сохраняет нормированность. -/
theorem isNormalized_swap_iff (U : Forms) : U.swap.IsNormalized ↔ U.IsNormalized :=
  ⟨fun h => by simpa using isNormalized_swap_of h, isNormalized_swap_of⟩

theorem isOrdered_swap_iff (U : Forms) : U.swap.IsOrdered ↔ U.ord 0 ≤ U.ord 1 := by
  simp only [IsOrdered, ord_swap]; rfl

/-- Одна из `U`, `U.swap` расставлена: `κ₁ ≥ κ₂`. -/
theorem isOrdered_or_swap (U : Forms) : U.IsOrdered ∨ U.swap.IsOrdered := by
  rw [isOrdered_swap_iff]; unfold IsOrdered; omega

/-- Обе расставлены тогда и только тогда, когда `κ₁ = κ₂`. -/
theorem isOrdered_and_swap_iff (U : Forms) :
    (U.IsOrdered ∧ U.swap.IsOrdered) ↔ U.ord 0 = U.ord 1 := by
  rw [isOrdered_swap_iff]; unfold IsOrdered; omega

/-- Ровно одна из `U`, `U.swap` расставлена, если `κ₁ ≠ κ₂`. -/
theorem isOrdered_xor_swap {U : Forms} (h : U.ord 0 ≠ U.ord 1) :
    Xor U.IsOrdered U.swap.IsOrdered := by
  rw [isOrdered_swap_iff]; unfold IsOrdered Xor
  rcases lt_or_gt_of_ne h with h1 | h1
  · right; exact ⟨h1.le, by omega⟩
  · left; exact ⟨h1.le, by omega⟩

end Forms

/-- Собственные пары `U` и `U.swap` совпадают. -/
theorem isEigenpair_swap_iff (a : ℝ → ℝ) (U : Forms) (lam : ℂ) (y y' y'' : ℝ → ℂ) :
    IsEigenpair a U.swap lam y y' y'' ↔ IsEigenpair a U lam y y' y'' := by
  have key : ∀ V : Forms, IsEigenpair a V.swap lam y y' y'' → IsEigenpair a V lam y y' y'' := by
    intro V h
    refine ⟨h.ac_y, h.ac_y', h.deriv_y, h.deriv_y', h.eqn, fun j => ?_, h.nontrivial⟩
    have := h.bc j.rev
    rwa [Forms.eval_swap, Fin.rev_rev] at this
  exact ⟨key U, fun h => key U.swap (by simpa using h)⟩

/-- Множества собственных значений `U` и `U.swap` совпадают. -/
theorem isEigenvalue_swap_iff (a : ℝ → ℝ) (U : Forms) (lam : ℂ) :
    IsEigenvalue a U.swap lam ↔ IsEigenvalue a U lam := by
  unfold IsEigenvalue
  simp only [isEigenpair_swap_iff]

/-- `AdmissibleForms` достигается перестановкой: для независимой нормированной пары
допустима `U` или `U.swap`. -/
theorem admissible_or_swap {U : Forms} (hi : U.LinIndep) (hn : U.IsNormalized) :
    AdmissibleForms U ∨ AdmissibleForms U.swap := by
  rcases Forms.isOrdered_or_swap U with h | h
  · exact Or.inl ⟨hi, hn, h⟩
  · exact Or.inr ⟨(Forms.linIndep_swap_iff U).2 hi, (Forms.isNormalized_swap_iff U).2 hn, h⟩

/-- Если `κ₁ ≠ κ₂`, допустима ровно одна из `U`, `U.swap`. -/
theorem admissible_xor_swap {U : Forms} (hi : U.LinIndep) (hn : U.IsNormalized)
    (h : U.ord 0 ≠ U.ord 1) : Xor (AdmissibleForms U) (AdmissibleForms U.swap) := by
  have hx := Forms.isOrdered_xor_swap h
  have e1 : AdmissibleForms U ↔ U.IsOrdered := ⟨fun h => h.ordered, fun h => ⟨hi, hn, h⟩⟩
  have e2 : AdmissibleForms U.swap ↔ U.swap.IsOrdered :=
    ⟨fun h => h.ordered, fun h => ⟨(Forms.linIndep_swap_iff U).2 hi,
      (Forms.isNormalized_swap_iff U).2 hn, h⟩⟩
  rw [e1, e2]; exact hx

end GeneralBC
end Involution
