module

public import Involution.Theorems.GeneralBCEigMatch

/-! # Теорема thm:eig (b): сопоставление нулей `Δ` и `G` (пакет G6)

Биекция `σ : ZerTy (mult Δ) ≃ ZerTy (mult G)` с тем, что разность корней `λ^{1/2}`
сопоставленных нулей не меньше `ε'` лишь для конечного числа пар. -/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace Involution
namespace GeneralBC

theorem exists_pairing {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (hreg : Regular a U) (hdet : DetPrincipalPart a U) :
    ∃ (b₀ : ℝ) (σ : ZerTy (mult (Delta a U)) ≃ ZerTy (mult (Gfun a U))), 0 ≤ b₀ ∧
      (∀ ε' > 0, {p : ZerTy (mult (Delta a U)) |
        ε' ≤ ‖p.1 ^ (1 / 2 : ℂ) - (σ p).1 ^ (1 / 2 : ℂ)‖}.Finite) ∧
      (∀ p : ZerTy (mult (Delta a U)), b₀ ^ 2 ≤ ‖p.1‖ →
        0 < (p.1 ^ (1 / 2 : ℂ)).re ∧ 0 < ((σ p).1 ^ (1 / 2 : ℂ)).re ∧
        Fchar a U ((σ p).1 ^ (1 / 2 : ℂ)) = 0 ∧
        analyticOrderAt (Fchar a U) ((σ p).1 ^ (1 / 2 : ℂ)) =
          analyticOrderAt (Gfun a U) (σ p).1) := by
  classical
  have hdet0 := hdet
  obtain ⟨η, hηd, hη, hsmall⟩ := hdet
  have hP := planarData_Fchar h hreg hηd hsmall
  obtain ⟨hA, rA, hA1, hrA, hfar⟩ := delta_sq_ne_zero_far h hU hreg hdet0
  obtain ⟨h₀c, N₀, hstrip, -⟩ := hP.count
  have hsc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ r : ℝ, ∀ b : ℝ, r ≤ b →
      GoodRad (Fchar a U) ε b →
      (∀ lam ∈ sphere (0 : ℂ) (b ^ 2), Delta a U lam ≠ 0 ∧ Gfun a U lam ≠ 0) ∧
      zeroCount (Delta a U) 0 (b ^ 2) = zeroCount (Gfun a U) 0 (b ^ 2) :=
    fun ε hε hε2 => small_count_eq h hU hreg hηd hη hsmall hε hε2
  choose! rs hrs using hsc
  obtain ⟨b₀, ε₀', πF, πΨ, hb0, hBf, hε0, hε0le, hgood, hfinF, hfinΨ, hsum, hclose, hbdd⟩ :=
    global_labels hP (fun ε => max (rs ε) (max rA (max hA (max h₀c 1))) + 1)
  have hb1 : rs ε₀' ≤ b₀ := by
    have := le_max_left (rs ε₀') (max rA (max hA (max h₀c 1))); linarith
  have hb2 : rA + 1 ≤ b₀ := by
    have := le_max_left rA (max hA (max h₀c 1))
    have := le_max_right (rs ε₀') (max rA (max hA (max h₀c 1))); linarith
  have hb3 : hA + 1 ≤ b₀ := by
    have := le_max_left hA (max h₀c 1)
    have := le_max_right rA (max hA (max h₀c 1))
    have := le_max_right (rs ε₀') (max rA (max hA (max h₀c 1))); linarith
  have hb4 : h₀c + 1 ≤ b₀ := by
    have := le_max_left h₀c 1
    have := le_max_right hA (max h₀c 1)
    have := le_max_right rA (max hA (max h₀c 1))
    have := le_max_right (rs ε₀') (max rA (max hA (max h₀c 1))); linarith
  obtain ⟨hsph, hcount⟩ := hrs ε₀' hε0 (by linarith) b₀ hb1 hgood
  have hDnz : ∃ z, Delta a U z ≠ 0 := delta_not_identically_zero h hU hreg hdet0
  have hGnz : ∃ z, Gfun a U z ≠ 0 := by
    obtain ⟨ρ, hρ0, hρ⟩ := exists_nonzero_ne_zero_point (Fchar_differentiable a U).continuous hP.nz
    refine ⟨ρ ^ 2, ?_⟩
    rw [Gfun_sq_zpow a U hρ0]
    exact mul_ne_zero (zpow_ne_zero _ hρ0) hρ
  -- свойства для переноса
  have h1Δ : ∀ x : ℂ, x ≠ 0 → mult (Delta a U) (x ^ 2) = mult (fun w => Fchar a U w + η w) x :=
    fun x hx => congrArg ENat.toNat (analyticOrderAt_Delta_sq h hU hηd hη hx)
  have h1G : ∀ x : ℂ, x ≠ 0 → mult (Gfun a U) (x ^ 2) = mult (Fchar a U) x :=
    fun x hx => congrArg ENat.toNat (analyticOrderAt_Gfun_sq a U hx)
  have hre_of : ∀ x : ℂ, b₀ < ‖x‖ → 0 ≤ x.re → ∀ c : ℝ, |x.im| < c → c + 1 ≤ b₀ → 0 < x.re := by
    intro x hx hre c hc hcb
    have h1 : ‖x‖ ≤ |x.re| + |x.im| := Complex.norm_le_abs_re_add_abs_im x
    rw [abs_of_nonneg hre] at h1
    linarith
  have h2Δ : ∀ x : ℂ, b₀ < ‖x‖ → 0 ≤ x.re → mult (Delta a U) (x ^ 2) ≠ 0 → 0 < x.re := by
    intro x hx hre hm
    have hz := eq_zero_of_mult_ne_zero ((Delta_differentiable a U).analyticAt _) hm
    have him : |x.im| < hA := by
      by_contra hcon
      rw [not_lt] at hcon
      exact hfar x (by linarith) hcon hz
    exact hre_of x hx hre hA him hb3
  have h2G : ∀ x : ℂ, b₀ < ‖x‖ → 0 ≤ x.re → mult (Gfun a U) (x ^ 2) ≠ 0 → 0 < x.re := by
    intro x hx hre hm
    have hz := eq_zero_of_mult_ne_zero ((Gfun_differentiable a U).analyticAt _) hm
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hx; linarith
    rw [Gfun_sq_zpow a U hx0] at hz
    have hF : Fchar a U x = 0 := by
      rcases mul_eq_zero.1 hz with h1 | h1
      · exact absurd h1 (zpow_ne_zero _ hx0)
      · exact h1
    exact hre_of x hx hre h₀c (hstrip x hF) hb4
  have hord0Δ : ∀ lam : ℂ, Delta a U lam ≠ 0 → mult (Delta a U) lam = 0 := by
    intro lam hf
    unfold mult zeroMult analyticOrderNatAt
    rw [((Delta_differentiable a U).analyticAt lam).analyticOrderAt_eq_zero.2 hf]
    rfl
  have hord0G : ∀ lam : ℂ, Gfun a U lam ≠ 0 → mult (Gfun a U) lam = 0 := by
    intro lam hf
    unfold mult zeroMult analyticOrderNatAt
    rw [((Gfun_differentiable a U).analyticAt lam).analyticOrderAt_eq_zero.2 hf]
    rfl
  have h3Δ : ∀ lam : ℂ, ‖lam‖ = b₀ ^ 2 → mult (Delta a U) lam = 0 := fun lam hl =>
    hord0Δ lam (hsph lam (mem_sphere_zero_iff_norm.2 hl)).1
  have h3G : ∀ lam : ℂ, ‖lam‖ = b₀ ^ 2 → mult (Gfun a U) lam = 0 := fun lam hl =>
    hord0G lam (hsph lam (mem_sphere_zero_iff_norm.2 hl)).2
  let πΔ : ℂ → Option (ℕ × Finset ℂ) := fun lam =>
    if ‖lam‖ < b₀ ^ 2 then none else some (πΨ (lam ^ (1 / 2 : ℂ)))
  let πG : ℂ → Option (ℕ × Finset ℂ) := fun lam =>
    if ‖lam‖ < b₀ ^ 2 then none else some (πF (lam ^ (1 / 2 : ℂ)))
  have hXΔ : ∀ τ, {lam | πΔ lam = τ ∧ mult (Delta a U) lam ≠ 0}.Finite := by
    intro τ
    cases τ with
    | none =>
      refine (finite_mult_ne_zero (Delta_differentiable a U) hDnz (b₀ ^ 2)).subset
        (fun lam hl => ?_)
      obtain ⟨h1, h2⟩ := hl
      exact ⟨((lab_eq_none πΨ _ lam).1 h1).le, h2⟩
    | some τ' =>
      refine (transfer_finite πΨ τ' (mult (Delta a U)) (mult (fun w => Fchar a U w + η w)) b₀
        hb0 h1Δ h2Δ h3Δ (hfinΨ τ')).subset (fun lam hl => ?_)
      obtain ⟨h1, h2⟩ := hl
      obtain ⟨h3, h4⟩ := (lab_eq_some πΨ _ lam τ').1 h1
      exact ⟨h3, h4, h2⟩
  have hXG : ∀ τ, {lam | πG lam = τ ∧ mult (Gfun a U) lam ≠ 0}.Finite := by
    intro τ
    cases τ with
    | none =>
      refine (finite_mult_ne_zero (Gfun_differentiable a U) hGnz (b₀ ^ 2)).subset
        (fun lam hl => ?_)
      obtain ⟨h1, h2⟩ := hl
      exact ⟨((lab_eq_none πF _ lam).1 h1).le, h2⟩
    | some τ' =>
      refine (transfer_finite πF τ' (mult (Gfun a U)) (mult (Fchar a U)) b₀
        hb0 h1G h2G h3G (hfinF τ')).subset (fun lam hl => ?_)
      obtain ⟨h1, h2⟩ := hl
      obtain ⟨h3, h4⟩ := (lab_eq_some πF _ lam τ').1 h1
      exact ⟨h3, h4, h2⟩
  have hsumΔG : ∀ τ, ∑ᶠ lam ∈ {lam | πΔ lam = τ}, mult (Delta a U) lam =
      ∑ᶠ lam ∈ {lam | πG lam = τ}, mult (Gfun a U) lam := by
    intro τ
    cases τ with
    | none =>
      have e1 : {lam | πΔ lam = none} = ball (0 : ℂ) (b₀ ^ 2) := by
        ext lam; rw [mem_ofPred_eq, mem_ball_zero_iff]; exact lab_eq_none πΨ _ lam
      have e2 : {lam | πG lam = none} = ball (0 : ℂ) (b₀ ^ 2) := by
        ext lam; rw [mem_ofPred_eq, mem_ball_zero_iff]; exact lab_eq_none πF _ lam
      rw [e1, e2]
      exact hcount
    | some τ' =>
      have e1 : {lam | πΔ lam = some τ'} =
          {lam : ℂ | ¬ ‖lam‖ < b₀ ^ 2 ∧ πΨ (lam ^ (1 / 2 : ℂ)) = τ'} := by
        ext lam; exact lab_eq_some πΨ _ lam τ'
      have e2 : {lam | πG lam = some τ'} =
          {lam : ℂ | ¬ ‖lam‖ < b₀ ^ 2 ∧ πF (lam ^ (1 / 2 : ℂ)) = τ'} := by
        ext lam; exact lab_eq_some πF _ lam τ'
      rw [e1, e2, transfer_fiber_sum πΨ τ' (mult (Delta a U))
        (mult (fun w => Fchar a U w + η w)) b₀ hb0 h1Δ h2Δ h3Δ,
        transfer_fiber_sum πF τ' (mult (Gfun a U)) (mult (Fchar a U)) b₀ hb0 h1G h2G h3G]
      exact (hsum τ').symm
  obtain ⟨σ, hσ⟩ := exists_equiv_of_fiber_sum (mult (Delta a U)) (mult (Gfun a U)) πΔ πG
    hXΔ hXG hsumΔG
  have key : ∀ p : ZerTy (mult (Delta a U)), b₀ ^ 2 ≤ ‖p.1‖ →
      ((p.1 ^ (1 / 2 : ℂ)) ^ 2 = p.1 ∧ p.1 ^ (1 / 2 : ℂ) ≠ 0 ∧ b₀ < ‖p.1 ^ (1 / 2 : ℂ)‖ ∧
        0 < (p.1 ^ (1 / 2 : ℂ)).re ∧
        mult (fun w => Fchar a U w + η w) (p.1 ^ (1 / 2 : ℂ)) ≠ 0) ∧
      (((σ p).1 ^ (1 / 2 : ℂ)) ^ 2 = (σ p).1 ∧ (σ p).1 ^ (1 / 2 : ℂ) ≠ 0 ∧
        b₀ < ‖(σ p).1 ^ (1 / 2 : ℂ)‖ ∧ 0 < ((σ p).1 ^ (1 / 2 : ℂ)).re ∧
        mult (Fchar a U) ((σ p).1 ^ (1 / 2 : ℂ)) ≠ 0) ∧
      πF ((σ p).1 ^ (1 / 2 : ℂ)) = πΨ (p.1 ^ (1 / 2 : ℂ)) := by
    intro p hp
    have hmD : mult (Delta a U) p.1 ≠ 0 := Nat.pos_iff_ne_zero.1 (Fin.pos p.2)
    have hge : ¬ ‖p.1‖ < b₀ ^ 2 := not_lt.2 hp
    obtain ⟨hsq, hx0, hnx, hre⟩ := large_zero_root hb0 h2Δ h3Δ hge hmD
    have hl : πΔ p.1 = some (πΨ (p.1 ^ (1 / 2 : ℂ))) :=
      (lab_eq_some πΨ (b₀ ^ 2) p.1 _).2 ⟨hge, rfl⟩
    have hσp := hσ p
    rw [hl] at hσp
    obtain ⟨hge', hlab⟩ := (lab_eq_some πF (b₀ ^ 2) (σ p).1 _).1 hσp
    have hmG : mult (Gfun a U) (σ p).1 ≠ 0 := Nat.pos_iff_ne_zero.1 (Fin.pos (σ p).2)
    obtain ⟨hsq', hx0', hnx', hre'⟩ := large_zero_root hb0 h2G h3G hge' hmG
    refine ⟨⟨hsq, hx0, hnx, hre, ?_⟩, ⟨hsq', hx0', hnx', hre', ?_⟩, hlab⟩
    · rw [← h1Δ _ hx0, hsq]; exact hmD
    · rw [← h1G _ hx0', hsq']; exact hmG
  refine ⟨b₀, σ, hb0, ?_, ?_⟩
  · intro ε' hε'
    obtain ⟨R', hR'⟩ := hclose ε' hε'
    refine (finite_zerTy_of_finite (mult (Delta a U))
      (finite_mult_ne_zero (Delta_differentiable a U) hDnz (max (b₀ ^ 2) (R' ^ 2)))).subset
      (fun p hp => ?_)
    refine ⟨?_, Nat.pos_iff_ne_zero.1 (Fin.pos p.2)⟩
    by_contra hbig
    rw [not_le] at hbig
    have hp1 : b₀ ^ 2 ≤ ‖p.1‖ := le_trans (le_max_left _ _) hbig.le
    obtain ⟨⟨hsq, hx0, hnx, hre, hm⟩, ⟨hsq', hx0', hnx', hre', hm'⟩, hlab⟩ := key p hp1
    have hR : R' ≤ ‖p.1 ^ (1 / 2 : ℂ)‖ := by
      by_contra h'
      rw [not_le] at h'
      have hn : ‖p.1 ^ (1 / 2 : ℂ)‖ ^ 2 = ‖p.1‖ := by rw [← norm_pow, hsq]
      have : ‖p.1 ^ (1 / 2 : ℂ)‖ ^ 2 < R' ^ 2 := pow_lt_pow_left₀ h' (norm_nonneg _) (by norm_num)
      have := le_max_right (b₀ ^ 2) (R' ^ 2)
      linarith
    have := hR' (p.1 ^ (1 / 2 : ℂ)) ((σ p).1 ^ (1 / 2 : ℂ)) hnx hre hnx' hre' hm' hm hR hlab
    exact absurd hp (not_le.2 this)
  · intro p hp
    obtain ⟨⟨hsq, hx0, hnx, hre, hm⟩, ⟨hsq', hx0', hnx', hre', hm'⟩, hlab⟩ := key p hp
    refine ⟨hre, hre', eq_zero_of_mult_ne_zero ((Fchar_differentiable a U).analyticAt _) hm', ?_⟩
    have := analyticOrderAt_Gfun_sq a U hx0'
    rw [hsq'] at this
    exact this.symm

end GeneralBC
end Involution
