module

public import Involution.Theorems.GeneralBCEigLocal
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Теорема thm:eig (b): перенос блоков из `ρ`-плоскости в `λ`-плоскость (пакет G6)

Отображение `ρ ↦ ρ²` биективно переводит правую полуплоскость в плоскость с разрезом по
отрицательной полуоси; суммы кратностей по блокам при этом сохраняются. -/

@[expose] public noncomputable section

open Set

namespace Involution
namespace GeneralBC

theorem sqrt_sq_of_re_pos {x : ℂ} (hx : 0 < x.re) : (x ^ 2) ^ (1 / 2 : ℂ) = x := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hx)
  rw [abs_lt] at h
  have := Complex.pow_cpow_ofNat_inv (x := x) (n := 2) (by simpa using h.1) (by simpa using h.2.le)
  simpa [one_div] using this

/-- Крупный ненулевой нуль в `λ`-плоскости происходит из `ρ`-плоскости. -/
theorem large_zero_root {fl : ℂ → ℕ} {b₀ : ℝ} (hb₀ : 0 ≤ b₀)
    (h2 : ∀ x : ℂ, b₀ < ‖x‖ → 0 ≤ x.re → fl (x ^ 2) ≠ 0 → 0 < x.re)
    (h3 : ∀ lam : ℂ, ‖lam‖ = b₀ ^ 2 → fl lam = 0) {lam : ℂ} (hge : ¬ ‖lam‖ < b₀ ^ 2)
    (hm : fl lam ≠ 0) :
    (lam ^ (1 / 2 : ℂ)) ^ 2 = lam ∧ lam ^ (1 / 2 : ℂ) ≠ 0 ∧ b₀ < ‖lam ^ (1 / 2 : ℂ)‖ ∧
      0 < (lam ^ (1 / 2 : ℂ)).re := by
  set x : ℂ := lam ^ (1 / 2 : ℂ) with hx
  have hxsq : x ^ 2 = lam := cpow_half_sq lam
  have hn : ‖x‖ ^ 2 = ‖lam‖ := by rw [← norm_pow, hxsq]
  have hlam : b₀ ^ 2 < ‖lam‖ := by
    rw [not_lt] at hge
    refine lt_of_le_of_ne hge (fun h => ?_)
    exact hm (h3 lam h.symm)
  have hnx : b₀ < ‖x‖ := by
    by_contra hcon
    rw [not_lt] at hcon
    have := pow_le_pow_left₀ (norm_nonneg _) hcon 2
    linarith
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnx; linarith
  have hm' : fl (x ^ 2) ≠ 0 := by rw [hxsq]; exact hm
  exact ⟨hxsq, hx0, hnx, h2 x hnx (re_cpow_half_nonneg lam) hm'⟩

theorem transfer_fiber_sum {T : Type*} (π : ℂ → T) (τ : T) (fl fx : ℂ → ℕ) (b₀ : ℝ)
    (hb₀ : 0 ≤ b₀) (h1 : ∀ x : ℂ, x ≠ 0 → fl (x ^ 2) = fx x)
    (h2 : ∀ x : ℂ, b₀ < ‖x‖ → 0 ≤ x.re → fl (x ^ 2) ≠ 0 → 0 < x.re)
    (h3 : ∀ lam : ℂ, ‖lam‖ = b₀ ^ 2 → fl lam = 0) :
    ∑ᶠ lam ∈ {lam : ℂ | ¬ ‖lam‖ < b₀ ^ 2 ∧ π (lam ^ (1 / 2 : ℂ)) = τ}, fl lam =
      ∑ᶠ x ∈ {x : ℂ | π x = τ ∧ b₀ < ‖x‖ ∧ 0 < x.re}, fx x := by
  rw [← finsum_mem_inter_support fl, ← finsum_mem_inter_support fx]
  symm
  refine finsum_mem_eq_of_bijOn (fun x => x ^ 2) ⟨?_, ?_, ?_⟩ (fun x hx => ?_)
  · rintro x ⟨⟨hπ, hb, hre⟩, hm⟩
    have hx0 : x ≠ 0 := fun h => by rw [h] at hre; simp at hre
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [not_lt, norm_pow]
      exact pow_le_pow_left₀ hb₀ hb.le 2
    · rw [sqrt_sq_of_re_pos hre]; exact hπ
    · simp only [Function.mem_support] at hm ⊢
      rw [h1 x hx0]; exact hm
  · rintro x ⟨⟨-, -, hre⟩, -⟩ y ⟨⟨-, -, hre'⟩, -⟩ hxy
    simp only at hxy
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hxy with h | h
    · exact h
    · exfalso
      have := congrArg Complex.re h
      simp at this
      linarith
  · rintro lam ⟨⟨hge, hπ⟩, hm⟩
    simp only [Function.mem_support] at hm
    obtain ⟨hxsq, hx0, hnx, hre⟩ := large_zero_root hb₀ h2 h3 hge hm
    refine ⟨lam ^ (1 / 2 : ℂ), ⟨⟨hπ, hnx, hre⟩, ?_⟩, hxsq⟩
    simp only [Function.mem_support]
    rw [← h1 _ hx0, hxsq]; exact hm
  · obtain ⟨⟨-, -, hre⟩, -⟩ := hx
    have hx0 : x ≠ 0 := fun h => by rw [h] at hre; simp at hre
    exact (h1 x hx0).symm

theorem transfer_finite {T : Type*} (π : ℂ → T) (τ : T) (fl fx : ℂ → ℕ) (b₀ : ℝ)
    (hb₀ : 0 ≤ b₀) (h1 : ∀ x : ℂ, x ≠ 0 → fl (x ^ 2) = fx x)
    (h2 : ∀ x : ℂ, b₀ < ‖x‖ → 0 ≤ x.re → fl (x ^ 2) ≠ 0 → 0 < x.re)
    (h3 : ∀ lam : ℂ, ‖lam‖ = b₀ ^ 2 → fl lam = 0)
    (hfin : {x : ℂ | π x = τ ∧ b₀ < ‖x‖ ∧ 0 < x.re ∧ fx x ≠ 0}.Finite) :
    {lam : ℂ | ¬ ‖lam‖ < b₀ ^ 2 ∧ π (lam ^ (1 / 2 : ℂ)) = τ ∧ fl lam ≠ 0}.Finite := by
  refine (hfin.image (fun x => x ^ 2)).subset (fun lam hlam => ?_)
  obtain ⟨hge, hπ, hm⟩ := hlam
  obtain ⟨hxsq, hx0, hnx, hre⟩ := large_zero_root hb₀ h2 h3 hge hm
  refine ⟨lam ^ (1 / 2 : ℂ), ⟨hπ, hnx, hre, ?_⟩, hxsq⟩
  rw [← h1 _ hx0, hxsq]; exact hm

end GeneralBC
end Involution
