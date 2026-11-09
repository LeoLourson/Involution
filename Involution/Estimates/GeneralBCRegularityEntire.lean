module

public import Involution.Estimates.GeneralBCRegularityBridge
public import Involution.Estimates.ExpPolySimple
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # `G` — целая функция `λ` (пакет G5)

`Fchar` чётна для вида `(1,0)` и нечётна для `(0,0)`, `(1,1)`. Чётная целая `f` даёт целую
`λ ↦ f(λ^{1/2})` (ветвь корня не влияет: `f` чётна; в нуле — устранимая особенность). Отсюда
`Gfun_differentiable`. -/

@[expose] public noncomputable section

open Complex Set

namespace Involution
namespace GeneralBC

theorem cpow_half_sq (l : ℂ) : (l ^ (1 / 2 : ℂ)) ^ 2 = l := by
  simp

/-- Чётная целая `f`: `λ ↦ f(λ^{1/2})` целая. -/
theorem differentiable_even_comp_sqrt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (he : ∀ ρ, f (-ρ) = f ρ) : Differentiable ℂ (fun l : ℂ => f (l ^ (1 / 2 : ℂ))) := by
  set g : ℂ → ℂ := fun l => f (l ^ (1 / 2 : ℂ)) with hg
  have hg2 : ∀ l, g l = f (I * (-l) ^ (1 / 2 : ℂ)) := by
    intro l
    have : (l ^ (1 / 2 : ℂ)) ^ 2 = (I * (-l) ^ (1 / 2 : ℂ)) ^ 2 := by
      rw [mul_pow, cpow_half_sq, cpow_half_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
    · simp only [hg, h]
    · simp only [hg, h, he]
  have hd0 : ∀ l, l ≠ 0 → DifferentiableAt ℂ g l := by
    intro l hl
    by_cases hs : l ∈ slitPlane
    · exact hf.differentiableAt.comp l
        (DifferentiableAt.cpow_const (by fun_prop) hs)
    · have hs' : -l ∈ slitPlane := by
        rw [mem_slitPlane_iff] at hs ⊢
        simp only [Complex.neg_re, Complex.neg_im, neg_ne_zero]
        have h1 : l.re ≤ 0 ∧ l.im = 0 := by
          by_contra hc
          apply hs
          by_cases him : l.im = 0
          · left; by_contra hr; exact hc ⟨not_lt.1 hr, him⟩
          · right; exact him
        rcases lt_or_eq_of_le h1.1 with h | h
        · left; linarith
        · exact absurd (Complex.ext h h1.2) hl
      have : g = fun l => f (I * (-l) ^ (1 / 2 : ℂ)) := funext hg2
      rw [this]
      refine hf.differentiableAt.comp l ?_
      exact (DifferentiableAt.cpow_const (f := fun l : ℂ => -l) (by fun_prop) hs').const_mul I
  have hc0 : ContinuousAt g 0 := by
    have h1 : ContinuousAt (fun l : ℂ => l ^ (1 / 2 : ℂ)) 0 :=
      continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num)
    exact hf.continuous.continuousAt.comp h1
  have hon : DifferentiableOn ℂ g univ := by
    rw [← differentiableOn_compl_singleton_and_continuousAt_iff (c := 0) Filter.univ_mem]
    exact ⟨fun l hl => (hd0 l hl.2).differentiableWithinAt, hc0⟩
  exact differentiableOn_univ.1 hon

variable {a : ℝ → ℝ} {U : Forms}

theorem Fchar_differentiable (a : ℝ → ℝ) (U : Forms) : Differentiable ℂ (Fchar a U) := by
  rw [Fchar_eq_expPoly]; exact expPoly_differentiable _ _ _ _ _ _

/-- `F` чётна для вида `(1,0)`. -/
theorem Fchar_neg_k10 (hk : U.kind = Forms.Kind.k10) (ρ : ℂ) :
    Fchar a U (-ρ) = Fchar a U ρ := by
  unfold Fchar
  split_ifs <;> simp only [hk, neg_mul, Complex.cos_neg, Complex.sin_neg] <;> ring

/-- `F` нечётна для видов `(0,0)`, `(1,1)`. -/
theorem Fchar_neg_odd (hk : U.kind ≠ Forms.Kind.k10) (ρ : ℂ) :
    Fchar a U (-ρ) = -Fchar a U ρ := by
  unfold Fchar
  cases hk' : U.kind
  · split_ifs <;> simp [neg_mul, Complex.cos_neg, Complex.sin_neg]
  · split_ifs <;> simp [neg_mul, Complex.cos_neg, Complex.sin_neg]
  · exact absurd hk' hk

theorem Fchar_zero_of_odd (hk : U.kind ≠ Forms.Kind.k10) : Fchar a U 0 = 0 := by
  have := Fchar_neg_odd (a := a) hk 0
  rw [neg_zero] at this
  linear_combination this / 2

/-- Чётность `dslope F 0` для нечётной `F`. -/
theorem dslope_even (hk : U.kind ≠ Forms.Kind.k10) (ρ : ℂ) :
    dslope (Fchar a U) 0 (-ρ) = dslope (Fchar a U) 0 ρ := by
  by_cases h : ρ = 0
  · simp [h]
  · have h' : -ρ ≠ 0 := neg_ne_zero.2 h
    rw [dslope_of_ne _ h', dslope_of_ne _ h, slope_def_field, slope_def_field,
      Fchar_neg_odd hk, Fchar_zero_of_odd hk]
    field_simp
    ring

theorem Gfun_eq_of_k10 (hk : U.kind = Forms.Kind.k10) :
    Gfun a U = fun l => Fchar a U (l ^ (1 / 2 : ℂ)) := by
  funext l
  by_cases hl : l = 0
  · subst hl; simp [Gfun, hk]
  · simp [Gfun, hk, hl]

theorem Gfun_eq_of_k00 (hk : U.kind = Forms.Kind.k00) :
    Gfun a U = fun l => dslope (Fchar a U) 0 (l ^ (1 / 2 : ℂ)) := by
  have hk' : U.kind ≠ Forms.Kind.k10 := by rw [hk]; decide
  funext l
  by_cases hl : l = 0
  · subst hl; simp [Gfun, hk]
  · have hne : l ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; simp [hl]
    rw [dslope_of_ne _ hne, slope_def_field, Fchar_zero_of_odd hk']
    simp [Gfun, hk, hl, div_eq_inv_mul]

theorem Gfun_eq_of_k11 (hk : U.kind = Forms.Kind.k11) :
    Gfun a U = fun l => (l ^ (1 / 2 : ℂ)) * Fchar a U (l ^ (1 / 2 : ℂ)) := by
  funext l
  by_cases hl : l = 0
  · subst hl; simp [Gfun, hk]
  · simp [Gfun, hk, hl]

/-- `G` — целая функция `λ` (C24 шаг 13). -/
theorem Gfun_differentiable (a : ℝ → ℝ) (U : Forms) : Differentiable ℂ (Gfun a U) := by
  have hF := Fchar_differentiable a U
  cases hk : U.kind
  · rw [Gfun_eq_of_k00 hk]
    exact differentiable_even_comp_sqrt (differentiable_dslope hF 0)
      (dslope_even (by rw [hk]; decide))
  · rw [Gfun_eq_of_k11 hk]
    refine differentiable_even_comp_sqrt (f := fun ρ => ρ * Fchar a U ρ)
      (differentiable_id.mul hF) (fun ρ => ?_)
    simp only [Fchar_neg_odd (a := a) (U := U) (by rw [hk]; decide)]
    ring
  · rw [Gfun_eq_of_k10 hk]
    exact differentiable_even_comp_sqrt hF (Fchar_neg_k10 hk)

/-- Тождество `G(ρ²) = ρ^{κ₁+κ₂−1} F(ρ)` при `ρ ≠ 0`. -/
theorem Gfun_sq (a : ℝ → ℝ) (U : Forms) (ρ : ℂ) (h0 : ρ ≠ 0) :
    Gfun a U (ρ ^ 2) =
      match U.kind with
      | Forms.Kind.k00 => Fchar a U ρ / ρ
      | Forms.Kind.k11 => ρ * Fchar a U ρ
      | Forms.Kind.k10 => Fchar a U ρ := by
  have hsq : ((ρ ^ 2) ^ (1 / 2 : ℂ)) ^ 2 = ρ ^ 2 := cpow_half_sq _
  have hpm : (ρ ^ 2) ^ (1 / 2 : ℂ) = ρ ∨ (ρ ^ 2) ^ (1 / 2 : ℂ) = -ρ :=
    sq_eq_sq_iff_eq_or_eq_neg.1 hsq
  have hne : ρ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  cases hk : U.kind
  · simp only [Gfun, hne, ↓reduceIte, hk]
    have hodd := Fchar_neg_odd (a := a) (U := U) (by rw [hk]; decide) ρ
    rcases hpm with h | h <;> rw [h]
    rw [hodd, div_neg, neg_div, neg_neg]
  · simp only [Gfun, hne, ↓reduceIte, hk]
    have hodd := Fchar_neg_odd (a := a) (U := U) (by rw [hk]; decide) ρ
    rcases hpm with h | h <;> rw [h]
    rw [hodd]; ring
  · simp only [Gfun, hne, ↓reduceIte, hk]
    rcases hpm with h | h <;> rw [h]
    rw [Fchar_neg_k10 hk]

end GeneralBC
end Involution
