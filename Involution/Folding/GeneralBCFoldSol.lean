module

public import Involution.Folding.GeneralBCFoldCalc
public import Involution.Folding.GeneralBCFold

/-! # Решения задачи (1), (2) и пространство собственных функций

`IsSolution` — `IsEigenpair` без требования `y ≢ 0`; `FoldEigSpace` — подмодуль функций на
`[-1,1]` (сужения решений); `foldInit` — начальный вектор `w(0)`. Из абсолютной
непрерывности `y`, `y'` выводятся формулы Ньютона–Лейбница и `y ∈ C¹(-1,1)`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval

namespace Involution
namespace GeneralBC

/-- Решение (1), (2) без требования `y ≢ 0`. -/
structure IsSolution (a : ℝ → ℝ) (U : Forms) (lam : ℂ) (y y' y'' : ℝ → ℂ) : Prop where
  ac_y : AbsolutelyContinuousOnInterval y (-1) 1
  ac_y' : AbsolutelyContinuousOnInterval y' (-1) 1
  deriv_y : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt y (y' x) x
  deriv_y' : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt y' (y'' x) x
  eqn : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → -y'' x - (a x : ℂ) * y'' (-x) = lam * y x
  bc : ∀ j, U.eval j y y' = 0

theorem isEigenpair_iff {a U lam y y' y''} :
    IsEigenpair a U lam y y' y'' ↔
      IsSolution a U lam y y' y'' ∧ ∃ x ∈ Icc (-1 : ℝ) 1, y x ≠ 0 :=
  ⟨fun h => ⟨⟨h.ac_y, h.ac_y', h.deriv_y, h.deriv_y', h.eqn, h.bc⟩, h.nontrivial⟩,
   fun h => ⟨h.1.ac_y, h.1.ac_y', h.1.deriv_y, h.1.deriv_y', h.1.eqn, h.1.bc, h.2⟩⟩

namespace IsSolution
variable {a : ℝ → ℝ} {U : Forms} {lam : ℂ} {y y' y'' : ℝ → ℂ}

theorem zero : IsSolution a U lam 0 0 0 where
  ac_y := ContDiffOn.absolutelyContinuousOnInterval (f := (0 : ℝ → ℂ)) contDiffOn_const
  ac_y' := ContDiffOn.absolutelyContinuousOnInterval (f := (0 : ℝ → ℂ)) contDiffOn_const
  deriv_y := Filter.Eventually.of_forall fun x _ => hasDerivAt_const x 0
  deriv_y' := Filter.Eventually.of_forall fun x _ => hasDerivAt_const x 0
  eqn := Filter.Eventually.of_forall fun x _ => by simp
  bc := fun j => by simp [Forms.eval]

theorem add {z z' z'' : ℝ → ℂ} (h : IsSolution a U lam y y' y'')
    (h2 : IsSolution a U lam z z' z'') : IsSolution a U lam (y + z) (y' + z') (y'' + z'') where
  ac_y := h.ac_y.add h2.ac_y
  ac_y' := h.ac_y'.add h2.ac_y'
  deriv_y := by
    filter_upwards [h.deriv_y, h2.deriv_y] with x hx hx2 hxI using (hx hxI).add (hx2 hxI)
  deriv_y' := by
    filter_upwards [h.deriv_y', h2.deriv_y'] with x hx hx2 hxI using (hx hxI).add (hx2 hxI)
  eqn := by
    filter_upwards [h.eqn, h2.eqn] with x hx hx2 hxI
    have := hx hxI
    have := hx2 hxI
    simp only [Pi.add_apply]
    linear_combination hx hxI + hx2 hxI
  bc := fun j => by
    have e1 := h.bc j
    have e2 := h2.bc j
    simp only [Forms.eval, Pi.add_apply] at e1 e2 ⊢
    linear_combination e1 + e2

theorem smul (c : ℂ) (h : IsSolution a U lam y y' y'') :
    IsSolution a U lam (c • y) (c • y') (c • y'') where
  ac_y := h.ac_y.const_smul c
  ac_y' := h.ac_y'.const_smul c
  deriv_y := by
    filter_upwards [h.deriv_y] with x hx hxI using (hx hxI).const_smul c
  deriv_y' := by
    filter_upwards [h.deriv_y'] with x hx hxI using (hx hxI).const_smul c
  eqn := by
    filter_upwards [h.eqn] with x hx hxI
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination c * hx hxI
  bc := fun j => by
    have e1 := h.bc j
    simp only [Forms.eval, Pi.smul_apply, smul_eq_mul] at e1 ⊢
    linear_combination c * e1

theorem continuousOn_y' (h : IsSolution a U lam y y' y'') : ContinuousOn y' (Icc (-1) 1) := by
  simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using h.ac_y'.continuousOn

theorem continuousOn_y (h : IsSolution a U lam y y' y'') : ContinuousOn y (Icc (-1) 1) := by
  simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using h.ac_y.continuousOn

theorem zero_mem_Icc : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

theorem y_ftc (h : IsSolution a U lam y y' y'') {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    y x = y 0 + ∫ t in (0 : ℝ)..x, y' t := by
  have := (ftc_Icc h.ac_y h.deriv_y zero_mem_Icc hx).2
  rw [this]; ring

theorem hasDerivAt_y (h : IsSolution a U lam y y' y'') {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt y (y' x) x :=
  hasDerivAt_of_ftc h.continuousOn_y' (fun _ hx => h.y_ftc hx) hx

theorem y'_ftc (h : IsSolution a U lam y y' y'') {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    y' x = y' 0 + ∫ t in (0 : ℝ)..x, y'' t := by
  have := (ftc_Icc h.ac_y' h.deriv_y' zero_mem_Icc hx).2
  rw [this]; ring
end IsSolution

/-- Пространство собственных функций при `λ` (вместе с нулём), как подмодуль функций на `[-1,1]`. -/
def FoldEigSpace (a : ℝ → ℝ) (U : Forms) (lam : ℂ) : Submodule ℂ (Icc (-1 : ℝ) 1 → ℂ) where
  carrier := {f | ∃ y y' y'' : ℝ → ℂ, IsSolution a U lam y y' y'' ∧ ∀ x : Icc (-1 : ℝ) 1, f x = y x}
  zero_mem' := ⟨0, 0, 0, IsSolution.zero, fun x => rfl⟩
  add_mem' := by
    rintro f g ⟨y, y', y'', h, hf⟩ ⟨z, z', z'', h2, hg⟩
    exact ⟨y + z, y' + z', y'' + z'', h.add h2, fun x => by simp [hf x, hg x]⟩
  smul_mem' := by
    rintro c f ⟨y, y', y'', h, hf⟩
    exact ⟨c • y, c • y', c • y'', h.smul c, fun x => by simp [hf x]⟩

/-- Начальный вектор `w(0) = (y(0), y(0), y'(0), -y'(0))` собственной функции `y` по её сужению
на `[-1,1]` (производная в нуле берётся у продолжения `IccExtend`). -/
noncomputable def foldInit (f : Icc (-1 : ℝ) 1 → ℂ) : Fin 4 → ℂ :=
  ![f ⟨0, IsSolution.zero_mem_Icc⟩, f ⟨0, IsSolution.zero_mem_Icc⟩,
    deriv (Set.IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f) 0,
    -deriv (Set.IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f) 0]

theorem foldInit_eq {a U lam} {y y' y'' : ℝ → ℂ} (h : IsSolution a U lam y y' y'')
    {f : Icc (-1 : ℝ) 1 → ℂ} (hf : ∀ x : Icc (-1 : ℝ) 1, f x = y x) :
    foldInit f = ![y 0, y 0, y' 0, -y' 0] := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hd : HasDerivAt (Set.IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f) (y' 0) 0 := by
    refine (h.hasDerivAt_y h0).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds h0.1 h0.2] with t ht
    rw [Set.IccExtend_of_mem _ _ (Ioo_subset_Icc_self ht)]
    exact hf _
  simp [foldInit, hd.deriv, hf]

/-- `foldInit` на пространстве собственных функций линейно. -/
noncomputable def foldInitLin (a : ℝ → ℝ) (U : Forms) (lam : ℂ) :
    FoldEigSpace a U lam →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun f := foldInit f.1
  map_add' f g := by
    obtain ⟨y, y', y'', h, hf⟩ := f.2
    obtain ⟨z, z', z'', h2, hg⟩ := g.2
    have e1 := foldInit_eq h hf
    have e2 := foldInit_eq h2 hg
    have e3 := foldInit_eq (h.add h2) (f := f.1 + g.1) (fun x => by simp [hf x, hg x])
    simp only [Submodule.coe_add]
    rw [e3, e1, e2]
    ext i; fin_cases i <;> simp
    ring
  map_smul' c f := by
    obtain ⟨y, y', y'', h, hf⟩ := f.2
    have e1 := foldInit_eq h hf
    have e3 := foldInit_eq (h.smul c) (f := c • f.1) (fun x => by simp [hf x])
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [e3, e1]
    ext i; fin_cases i <;> simp

end GeneralBC
end Involution
