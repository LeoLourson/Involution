module

public import Involution.Estimates.GeneralBCRegularityPos
public import Involution.Estimates.DirichletSeriesCriterion

/-! # `prop:dir` в терминах задачи (пакет G5)

Условия Дирихле `dirichletForms` имеют вид `(0,0)`; `Fchar a dirichletForms` есть `dirCS ℓ₊ ℓ₋`
при `a(0) > 0` (`ε = 1`) и `dirSC ℓ₊ ℓ₋` иначе. Задача регулярна, нули — серии статьи,
сильная регулярность равносильна условию на несократимую дробь `ℓ₊/ℓ₋ = r/s`. -/

@[expose] public noncomputable section

open Set

namespace Involution
namespace GeneralBC

variable {a : ℝ → ℝ} {m κ : ℝ}

theorem dirichletForms_kind : dirichletForms.kind = Forms.Kind.k00 := by
  have h0 : ¬ dirichletForms.HasDeriv 0 := by simp [Forms.HasDeriv, dirichletForms]
  have h1 : ¬ dirichletForms.HasDeriv 1 := by simp [Forms.HasDeriv, dirichletForms]
  simp [Forms.kind, h0, h1]

theorem Fchar_dirichlet_of_pos (h : 0 < a 0) :
    Fchar a dirichletForms = dirCS (ell a 1) (ell a (-1)) := by
  funext ρ
  simp [Fchar, dirichletForms_kind, h, dirCS]

theorem Fchar_dirichlet_of_nonpos (h : ¬ 0 < a 0) :
    Fchar a dirichletForms = dirSC (ell a 1) (ell a (-1)) := by
  funext ρ
  simp [Fchar, dirichletForms_kind, h, dirSC]

/-- prop:dir: задача Дирихле регулярна (без условий на `a`). -/
theorem prop_dir_regular (a : ℝ → ℝ) : Regular a dirichletForms :=
  regular_of_k00 a _ dirichletForms_kind

/-- prop:dir: нули `F` — серии статьи. -/
theorem prop_dir_zeros (h : HypH a m κ) (ρ : ℂ) :
    Fchar a dirichletForms ρ = 0 ↔
      if 0 < a 0 then
        (∃ n : ℤ, ρ = ((Real.pi * (n - 1 / 2) / ell a 1 : ℝ) : ℂ)) ∨
        (∃ n : ℤ, ρ = ((Real.pi * n / ell a (-1) : ℝ) : ℂ))
      else
        (∃ n : ℤ, ρ = ((Real.pi * n / ell a 1 : ℝ) : ℂ)) ∨
        (∃ n : ℤ, ρ = ((Real.pi * (n - 1 / 2) / ell a (-1) : ℝ) : ℂ)) := by
  have hp := (ell_pos h (Or.inl rfl)).ne'
  have hm := (ell_pos h (Or.inr rfl)).ne'
  by_cases hε : 0 < a 0
  · simp only [hε, ↓reduceIte]
    rw [Fchar_dirichlet_of_pos hε, dirCS_eq_zero_iff _ _ hp hm]
    refine or_congr ⟨fun ⟨k, hk⟩ => ⟨k + 1, ?_⟩, fun ⟨n, hn⟩ => ⟨n - 1, ?_⟩⟩ (by simp [mul_comm])
    · rw [hk]; congr 1; push_cast; ring
    · rw [hn]; congr 1; push_cast; ring
  · simp only [hε, ↓reduceIte]
    rw [Fchar_dirichlet_of_nonpos hε, dirSC_eq_zero_iff _ _ hp hm]
    refine or_congr (by simp [mul_comm]) ⟨fun ⟨k, hk⟩ => ⟨k + 1, ?_⟩, fun ⟨n, hn⟩ => ⟨n - 1, ?_⟩⟩
    · rw [hk]; congr 1; push_cast; ring
    · rw [hn]; congr 1; push_cast; ring

/-- `StronglyRegular` для Дирихле — это `DirichletStrongRegular` для `Fchar`. -/
theorem stronglyRegular_dirichlet_iff (a : ℝ → ℝ) :
    StronglyRegular a dirichletForms ↔ DirichletStrongRegular (Fchar a dirichletForms) := by
  unfold StronglyRegular DirichletStrongRegular ZerosSeparated ZerosEventuallySimple
  simp only [prop_dir_regular, true_and]
  refine and_congr ?_ Iff.rfl
  constructor
  · rintro ⟨δ, hδ, H⟩
    exact ⟨δ, hδ, fun ρ σ h1 h2 h3 h4 h5 => H ρ σ h3 h4 h1 h2 h5⟩
  · rintro ⟨δ, hδ, H⟩
    exact ⟨δ, hδ, fun ρ σ h3 h4 h1 h2 h5 => H ρ σ h1 h2 h3 h4 h5⟩

/-- prop:dir: сильная регулярность равносильна условию на несократимую дробь. -/
theorem prop_dir_strongly_regular_iff (h : HypH a m κ) :
    StronglyRegular a dirichletForms ↔
      ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ Nat.Coprime r s ∧
        ell a 1 / ell a (-1) = (r : ℝ) / s ∧ (if 0 < a 0 then Odd s else Odd r) := by
  have hp := ell_pos h (Or.inl rfl)
  have hm := ell_pos h (Or.inr rfl)
  rw [stronglyRegular_dirichlet_iff]
  by_cases hε : 0 < a 0
  · simp only [hε, ↓reduceIte]
    rw [Fchar_dirichlet_of_pos hε, dirCS_strongRegular_iff _ _ hp hm]
    constructor
    · rintro ⟨p, q, h1, h2, h3, h4, h5⟩; exact ⟨p, q, h1, h2, h3, h5, h4⟩
    · rintro ⟨p, q, h1, h2, h3, h5, h4⟩; exact ⟨p, q, h1, h2, h3, h4, h5⟩
  · simp only [hε, ↓reduceIte]
    rw [Fchar_dirichlet_of_nonpos hε, dirSC_strongRegular_iff _ _ hp hm]
    constructor
    · rintro ⟨p, q, h1, h2, h3, h4, h5⟩; exact ⟨p, q, h1, h2, h3, h5, h4⟩
    · rintro ⟨p, q, h1, h2, h3, h5, h4⟩; exact ⟨p, q, h1, h2, h3, h4, h5⟩

end GeneralBC
end Involution
