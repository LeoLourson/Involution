module

public import Involution.Setup.LinearCauchyVolterra
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.ContinuousMap.Compact

/-! Оператор Вольтерры на `C([0,1], 𝔸)` и ряд Пикара `∑ₖ (K₀ + λ K₁)ᵏ 1` в банаховой
алгебре `𝔸` над `ℂ`. Это общая часть построения матрицы Коши (`LinearCauchy`). -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution
namespace LinearCauchy

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- Продолжение функции с `[0,1]` на `ℝ` (проекцией на отрезок). -/
def ext (f : C(Icc (0 : ℝ) 1, 𝔸)) (t : ℝ) : 𝔸 := f (projIcc 0 1 zero_le_one t)

omit [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] in
lemma continuous_ext (f : C(Icc (0 : ℝ) 1, 𝔸)) : Continuous (ext f) :=
  f.continuous.comp continuous_projIcc

omit [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] in
lemma ext_of_mem (f : C(Icc (0 : ℝ) 1, 𝔸)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ext f t = f ⟨t, ht⟩ := by
  simp [ext, projIcc_of_mem _ ht]

omit [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] in
lemma norm_ext_le (f : C(Icc (0 : ℝ) 1, 𝔸)) (t : ℝ) : ‖ext f t‖ ≤ ‖f‖ :=
  f.norm_coe_le_norm _

/-- Первообразная `x ↦ ∫₀ˣ f` как непрерывное отображение. -/
def primitive (f : C(Icc (0 : ℝ) 1, 𝔸)) : C(Icc (0 : ℝ) 1, 𝔸) :=
  ⟨fun x => ∫ t in (0 : ℝ)..x, ext f t,
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_ext f).intervalIntegrable a b) 0).comp continuous_subtype_val⟩

omit [CompleteSpace 𝔸] in
lemma primitive_apply (f : C(Icc (0 : ℝ) 1, 𝔸)) (x : Icc (0 : ℝ) 1) :
    primitive f x = ∫ t in (0 : ℝ)..x, ext f t := rfl

/-- Оператор Вольтерры. -/
def volterra : C(Icc (0 : ℝ) 1, 𝔸) →L[ℂ] C(Icc (0 : ℝ) 1, 𝔸) :=
  LinearMap.mkContinuous
    { toFun := primitive
      map_add' := fun f g => by
        ext x
        simp only [primitive_apply, ext, ContinuousMap.add_apply]
        exact intervalIntegral.integral_add
          ((continuous_ext f).intervalIntegrable _ _) ((continuous_ext g).intervalIntegrable _ _)
      map_smul' := fun c f => by
        ext x
        simp only [primitive_apply, ext, ContinuousMap.smul_apply, RingHom.id_apply]
        exact intervalIntegral.integral_smul c _ }
    1 (fun f => by
      rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg f)]
      intro x
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := (x : ℝ)) (f := ext f) (C := ‖f‖) (fun t _ => norm_ext_le f t)
      refine this.trans ?_
      have hx := x.2
      rw [sub_zero, abs_of_nonneg hx.1]
      nlinarith [norm_nonneg f, hx.2])

omit [CompleteSpace 𝔸] in
lemma volterra_apply (f : C(Icc (0 : ℝ) 1, 𝔸)) (x : Icc (0 : ℝ) 1) :
    volterra f x = ∫ t in (0 : ℝ)..x, ext f t := rfl

end LinearCauchy
end Involution

end
