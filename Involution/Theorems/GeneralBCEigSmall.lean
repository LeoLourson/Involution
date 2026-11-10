module

public import Involution.Theorems.GeneralBCEigConcrete

/-! # Теорема thm:eig (b): ограниченная часть (пакет G6)

Теорема Руше в `λ`-плоскости на круге `|λ| < b²`, если `b` — хороший радиус: `Δ` и `G` имеют
в круге поровну нулей, на окружности нулей нет. -/

@[expose] public noncomputable section

open Set Metric

namespace Involution
namespace GeneralBC

theorem small_count_eq {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (hreg : Regular a U) {η : ℂ → ℂ}
    (hηd : DifferentiableOn ℂ η {0}ᶜ)
    (hη : ∀ ρ : ℂ, ρ ≠ 0 →
      ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) = cStar a U * (Fchar a U ρ + η ρ))
    (hsmall : ∀ ε > 0, ∃ r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ →
      ‖η ρ‖ * Real.exp (-(Ltot a) * |ρ.im|) ≤ ε)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ r : ℝ, ∀ b : ℝ, r ≤ b → GoodRad (Fchar a U) ε b →
      (∀ lam ∈ sphere (0 : ℂ) (b ^ 2), Delta a U lam ≠ 0 ∧ Gfun a U lam ≠ 0) ∧
      zeroCount (Delta a U) 0 (b ^ 2) = zeroCount (Gfun a U) 0 (b ^ 2) := by
  have hP := planarData_Fchar h hreg hηd hsmall
  obtain ⟨h₀, N₀, hstrip, -⟩ := hP.count
  obtain ⟨c, hc, hb⟩ := hP.lowb (2 * ε) (by positivity)
  obtain ⟨r₁, hr₁⟩ := hP.small (c / 2) (by positivity)
  refine ⟨max (max r₁ (h₀ + 1)) 1, fun b hb' hg => ?_⟩
  have hbpos : 0 < b := by have := le_max_right (max r₁ (h₀ + 1)) 1; linarith
  have hr1b : r₁ ≤ b := by
    have := le_max_left r₁ (h₀ + 1)
    have := le_max_left (max r₁ (h₀ + 1)) 1
    linarith
  have hh0b : h₀ + 1 ≤ b := by
    have := le_max_right r₁ (h₀ + 1)
    have := le_max_left (max r₁ (h₀ + 1)) 1
    linarith
  have hall := goodRad_all (hsym_Fchar a U) hstrip hε2 hh0b hg
  have hcne := cStar_ne_zero h hU
  set k : ℤ := (kappaSum U : ℤ) - 1 with hk
  -- оценка на окружности
  have key : ∀ lam ∈ sphere (0 : ℂ) (b ^ 2),
      ‖Delta a U lam - cStar a U * Gfun a U lam‖ < ‖cStar a U * Gfun a U lam‖ := by
    intro lam hlam
    have hlamn : ‖lam‖ = b ^ 2 := by
      rwa [mem_sphere_zero_iff_norm] at hlam
    set ρ : ℂ := lam ^ (1 / 2 : ℂ) with hρ
    have hρsq : ρ ^ 2 = lam := cpow_half_sq lam
    have hnorm : ‖ρ‖ = b := by
      have : ‖ρ‖ ^ 2 = b ^ 2 := by rw [← norm_pow, hρsq, hlamn]
      exact (sq_eq_sq₀ (norm_nonneg _) hbpos.le).1 this
    have hρ0 : ρ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hnorm; linarith
    have hF := hb ρ (fun z hz => by
      have h1 := hall z hz
      have h2 := abs_norm_sub_norm_le z ρ
      rw [hnorm] at h2
      rw [norm_sub_rev] at h2
      linarith)
    have hηb := norm_le_of_mul_exp_neg_le (hr₁ ρ (by rw [hnorm]; exact hr1b))
    have hlt : ‖η ρ‖ < ‖Fchar a U ρ‖ := by
      have := Real.exp_pos (Ltot a * |ρ.im|)
      nlinarith
    have hG : Gfun a U lam = ρ ^ k * Fchar a U ρ := by
      rw [← hρsq]; exact Gfun_sq_zpow a U hρ0
    have hD : Delta a U lam = ρ ^ k * (cStar a U * (Fchar a U ρ + η ρ)) := by
      have h2 := hη ρ hρ0
      have hk' : (1 : ℤ) - (kappaSum U : ℤ) = -k := by rw [hk]; ring
      rw [hk', zpow_neg, hρsq] at h2
      have hρk : ρ ^ k ≠ 0 := zpow_ne_zero _ hρ0
      rw [← h2]; field_simp
    rw [hG, hD]
    have hpos : 0 < ‖ρ ^ k‖ * ‖cStar a U‖ := by
      have := norm_pos_iff.2 hcne
      have := norm_pos_iff.2 (zpow_ne_zero k hρ0)
      positivity
    calc ‖ρ ^ k * (cStar a U * (Fchar a U ρ + η ρ)) - cStar a U * (ρ ^ k * Fchar a U ρ)‖
        = ‖ρ ^ k‖ * ‖cStar a U‖ * ‖η ρ‖ := by
          rw [show ρ ^ k * (cStar a U * (Fchar a U ρ + η ρ)) - cStar a U * (ρ ^ k * Fchar a U ρ)
            = ρ ^ k * cStar a U * η ρ by ring, norm_mul, norm_mul]
      _ < ‖ρ ^ k‖ * ‖cStar a U‖ * ‖Fchar a U ρ‖ := mul_lt_mul_of_pos_left hlt hpos
      _ = ‖cStar a U * (ρ ^ k * Fchar a U ρ)‖ := by
          rw [norm_mul, norm_mul]; ring
  refine ⟨fun lam hlam => ?_, ?_⟩
  · have := key lam hlam
    have hf : cStar a U * Gfun a U lam ≠ 0 := by
      intro h0; rw [h0, norm_zero] at this; exact absurd this (not_lt.2 (norm_nonneg _))
    refine ⟨fun hD => ?_, fun hG => hf (by rw [hG, mul_zero])⟩
    rw [hD, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  · have hdf : DifferentiableOn ℂ (fun lam => cStar a U * Gfun a U lam) univ :=
      ((Gfun_differentiable a U).const_mul _).differentiableOn
    have hdg : DifferentiableOn ℂ (fun lam => Delta a U lam - cStar a U * Gfun a U lam) univ :=
      ((Delta_differentiable a U).sub ((Gfun_differentiable a U).const_mul _)).differentiableOn
    have hr : 0 < b ^ 2 := by positivity
    have hR := rouche (c := 0) isOpen_univ (subset_univ _) hr hdf hdg key
    have e1 : (fun lam => cStar a U * Gfun a U lam) +
        (fun lam => Delta a U lam - cStar a U * Gfun a U lam) = Delta a U := by
      funext lam; simp
    rw [e1] at hR
    rw [← hR]
    unfold zeroCount
    refine finsum_mem_congr rfl (fun z _ => ?_)
    unfold zeroMult analyticOrderNatAt
    rw [analyticOrderAt_const_mul hcne ((Gfun_differentiable a U).analyticAt z)]

end GeneralBC
end Involution
