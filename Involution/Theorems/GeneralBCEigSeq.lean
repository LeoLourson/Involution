module

public import Involution.Theorems.GeneralBCEigPairing
public import Involution.Theorems.GeneralBCEigSimple

/-! # Теорема thm:eig (b), (c): нумерация нулей (пакет G6)

Нули `Δ` и `G` с кратностями нумеруются последовательностями `lamk`, `lam0`: число индексов `k`
с `lamk k = z` равно кратности нуля `Δ` в `z` (`analyticOrderAt`, приведённый к `ℕ`), то же для
`lam0` и `G`; `ρ_k - ρ_k^0 → 0`, где `ρ = λ^{1/2}` (главная ветвь, `Re ρ ≥ 0`). -/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace Involution
namespace GeneralBC

theorem eventually_notMem_of_finite {S : Set ℕ} (hS : S.Finite) : ∀ᶠ k in atTop, k ∉ S := by
  have := hS.compl_mem_cofinite
  rw [Nat.cofinite_eq_atTop] at this
  exact this

theorem infinite_zerTy_G {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hreg : Regular a U) {η : ℂ → ℂ} {L : ℝ} (hP : PlanarData (Fchar a U) η L) :
    Infinite (ZerTy (mult (Gfun a U))) := by
  have hinfF := lem_F_d ⟨m, κ, h⟩ hreg
  have hpos : ∀ z : {z : ℂ | Fchar a U z = 0 ∧ 0 < z.re}, 0 < mult (Gfun a U) (z.1 ^ 2) := by
    intro z
    have hz0 : z.1 ≠ 0 := fun h0 => by have := z.2.2; rw [h0] at this; simp at this
    have e : mult (Gfun a U) (z.1 ^ 2) = mult (Fchar a U) z.1 :=
      congrArg ENat.toNat (analyticOrderAt_Gfun_sq a U hz0)
    rw [e]
    exact mult_pos_of_zero hP z.2.1
  let g : {z : ℂ | Fchar a U z = 0 ∧ 0 < z.re} → ZerTy (mult (Gfun a U)) :=
    fun z => ⟨z.1 ^ 2, ⟨0, hpos z⟩⟩
  have hg : Function.Injective g := by
    intro z z' hzz
    have h1 : z.1 ^ 2 = z'.1 ^ 2 := congrArg Sigma.fst hzz
    refine Subtype.ext ?_
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
    · exact h2
    · exfalso
      have := congrArg Complex.re h2
      have h3 := z.2.2
      have h4 := z'.2.2
      simp at this
      linarith
  have : Infinite {z : ℂ | Fchar a U z = 0 ∧ 0 < z.re} := hinfF.to_subtype
  exact Infinite.of_injective g hg

/-- **thm:eig (b)**: нумерация нулей `Δ` и `G` с кратностями и `ρ_k - ρ_k^0 → 0`. -/
theorem thm_eig_b {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (hreg : Regular a U) (hdet : DetPrincipalPart a U) :
    ∃ lamk lam0 : ℕ → ℂ,
      (∀ k, Delta a U (lamk k) = 0) ∧ (∀ k, Gfun a U (lam0 k) = 0) ∧
      (∀ z : ℂ, Nat.card {k : ℕ // lamk k = z} = (analyticOrderAt (Delta a U) z).toNat) ∧
      (∀ z : ℂ, Nat.card {k : ℕ // lam0 k = z} = (analyticOrderAt (Gfun a U) z).toNat) ∧
      Tendsto (fun k => ‖lamk k‖) atTop atTop ∧
      Tendsto (fun k => lamk k ^ (1 / 2 : ℂ) - lam0 k ^ (1 / 2 : ℂ)) atTop (𝓝 0) ∧
      ∃ K₀ : ℕ, ∀ k ≥ K₀, 0 < (lamk k ^ (1 / 2 : ℂ)).re ∧ 0 < (lam0 k ^ (1 / 2 : ℂ)).re ∧
        Fchar a U (lam0 k ^ (1 / 2 : ℂ)) = 0 ∧
        analyticOrderAt (Fchar a U) (lam0 k ^ (1 / 2 : ℂ)) =
          analyticOrderAt (Gfun a U) (lam0 k) := by
  classical
  obtain ⟨b₀, σ, hb0, hclose, hlarge⟩ := exists_pairing h hU hreg hdet
  have hdet0 := hdet
  obtain ⟨η, hηd, hη, hsmall⟩ := hdet
  have hP := planarData_Fchar h hreg hηd hsmall
  have hDnz : ∃ z, Delta a U z ≠ 0 := delta_not_identically_zero h hU hreg hdet0
  have hcount : Countable (ZerTy (mult (Delta a U))) := by
    refine countable_zerTy _ ?_
    have : Function.support (mult (Delta a U)) ⊆
        ⋃ n : ℕ, {z : ℂ | ‖z‖ ≤ n ∧ mult (Delta a U) z ≠ 0} := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
      exact mem_iUnion.2 ⟨n, hn, hz⟩
    exact (countable_iUnion (fun n : ℕ =>
      (finite_mult_ne_zero (Delta_differentiable a U) hDnz (n : ℝ)).countable)).mono this
  have hinf : Infinite (ZerTy (mult (Gfun a U))) := infinite_zerTy_G h hreg hP
  have hinfΔ : Infinite (ZerTy (mult (Delta a U))) := Infinite.of_injective σ.symm σ.symm.injective
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := ZerTy (mult (Delta a U)))
  have hbd : ∀ M : ℝ, {k : ℕ | ‖(e k).1‖ ≤ M}.Finite := by
    intro M
    have := finite_zerTy_of_finite (mult (Delta a U))
      (finite_mult_ne_zero (Delta_differentiable a U) hDnz M)
    refine (this.preimage e.injective.injOn).subset (fun k hk => ?_)
    exact ⟨hk, Nat.pos_iff_ne_zero.1 (Fin.pos (e k).2)⟩
  refine ⟨fun k => (e k).1, fun k => (σ (e k)).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact eq_zero_of_mult_ne_zero ((Delta_differentiable a U).analyticAt _)
      (Nat.pos_iff_ne_zero.1 (Fin.pos (e k).2))
  · intro k
    exact eq_zero_of_mult_ne_zero ((Gfun_differentiable a U).analyticAt _)
      (Nat.pos_iff_ne_zero.1 (Fin.pos (σ (e k)).2))
  · intro z
    exact (Nat.card_congr (e.subtypeEquiv (fun k => Iff.rfl))).trans
      (card_zerTy_fiber (mult (Delta a U)) z)
  · intro z
    exact (Nat.card_congr ((e.trans σ).subtypeEquiv (fun k => Iff.rfl))).trans
      (card_zerTy_fiber (mult (Gfun a U)) z)
  · refine tendsto_atTop.2 (fun R => ?_)
    filter_upwards [eventually_notMem_of_finite (hbd R)] with k hk
    exact not_le.1 hk |>.le
  · refine Metric.tendsto_atTop.2 (fun ε' hε' => ?_)
    have hfin : {k : ℕ | ε' ≤ ‖(e k).1 ^ (1 / 2 : ℂ) - (σ (e k)).1 ^ (1 / 2 : ℂ)‖}.Finite :=
      Set.Finite.preimage (f := e) e.injective.injOn (hclose ε' hε')
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_notMem_of_finite hfin)
    refine ⟨N, fun k hk => ?_⟩
    have := hN k hk
    rw [mem_ofPred_eq, not_le] at this
    simpa using this
  · have hfin := hbd (b₀ ^ 2)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_notMem_of_finite hfin)
    refine ⟨N, fun k hk => ?_⟩
    have := hN k hk
    rw [mem_ofPred_eq, not_le] at this
    exact hlarge (e k) this.le

/-- **thm:eig (c)** для нумерации: нули `lamk k → ∞` простые, подпространства одномерны. -/
theorem thm_eig_c_seq {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (hreg : Regular a U) (hsr : StronglyRegular a U)
    (hdet : DetPrincipalPart a U) {lamk : ℕ → ℂ} (hz : ∀ k, Delta a U (lamk k) = 0)
    (hT : Tendsto (fun k => ‖lamk k‖) atTop atTop) :
    ∃ K₀ : ℕ, ∀ k ≥ K₀, analyticOrderAt (Delta a U) (lamk k) = 1 ∧
      Module.finrank ℂ (FoldEigSpace a U (lamk k)) = 1 := by
  obtain ⟨R, hR⟩ := thm_eig_c h hU hreg hsr hdet
  obtain ⟨K₀, hK⟩ := eventually_atTop.1 (tendsto_atTop.1 hT R)
  exact ⟨K₀, fun k hk => hR (lamk k) (hK k hk)
    ((isEigenvalue_iff_Delta_eq_zero ⟨m, κ, h⟩).2 (hz k))⟩

/-- **thm:eig** целиком: `Δ ≢ 0`; (a); (b) с нумерацией; (c) для той же нумерации. -/
theorem thm_eig {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (hreg : Regular a U) (hdet : DetPrincipalPart a U) :
    (∃ lam : ℂ, Delta a U lam ≠ 0) ∧
    (∃ h' R : ℝ, 0 < h' ∧ ∀ lam : ℂ, IsEigenvalue a U lam → R ≤ ‖lam‖ →
      |(lam ^ (1 / 2 : ℂ)).im| ≤ h') ∧
    ∃ lamk lam0 : ℕ → ℂ,
      (∀ k, Delta a U (lamk k) = 0) ∧ (∀ k, Gfun a U (lam0 k) = 0) ∧
      (∀ z : ℂ, Nat.card {k : ℕ // lamk k = z} = (analyticOrderAt (Delta a U) z).toNat) ∧
      (∀ z : ℂ, Nat.card {k : ℕ // lam0 k = z} = (analyticOrderAt (Gfun a U) z).toNat) ∧
      Tendsto (fun k => ‖lamk k‖) atTop atTop ∧
      Tendsto (fun k => lamk k ^ (1 / 2 : ℂ) - lam0 k ^ (1 / 2 : ℂ)) atTop (𝓝 0) ∧
      (∃ K₀ : ℕ, ∀ k ≥ K₀, 0 < (lamk k ^ (1 / 2 : ℂ)).re ∧ 0 < (lam0 k ^ (1 / 2 : ℂ)).re ∧
        Fchar a U (lam0 k ^ (1 / 2 : ℂ)) = 0 ∧
        analyticOrderAt (Fchar a U) (lam0 k ^ (1 / 2 : ℂ)) =
          analyticOrderAt (Gfun a U) (lam0 k)) ∧
      (StronglyRegular a U → ∃ K₀ : ℕ, ∀ k ≥ K₀,
        analyticOrderAt (Delta a U) (lamk k) = 1 ∧
        Module.finrank ℂ (FoldEigSpace a U (lamk k)) = 1) := by
  obtain ⟨lamk, lam0, h1, h2, h3, h4, h5, h6, h7⟩ := thm_eig_b h hU hreg hdet
  refine ⟨delta_not_identically_zero h hU hreg hdet, thm_eig_a h hU hreg hdet,
    lamk, lam0, h1, h2, h3, h4, h5, h6, h7, fun hsr => ?_⟩
  exact thm_eig_c_seq h hU hreg hsr hdet h1 h5

end GeneralBC
end Involution
