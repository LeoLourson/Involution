module

public import Involution.Folding.GeneralBCFoldBack

/-! # Лемма `lem:fold`: `Δ` целая, нули `Δ` — собственные значения, изоморфизм ядер

Итоговые утверждения (при `Hyp a`, то есть (H)):
`Delta_differentiable` (без (H)), `isEigenvalue_iff_Delta_eq_zero`,
`foldEquiv : FoldEigSpace a U λ ≃ₗ[ℂ] foldKer a U λ`, действующий как `y ↦ w(0)`
(`foldEquiv_apply`). -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval Matrix

namespace Involution
namespace GeneralBC

variable {a : ℝ → ℝ} {U : Forms} {lam : ℂ}

/-- Ядро `ker (V₀ + V₁ Φ(1, λ))`. -/
def foldKer (a : ℝ → ℝ) (U : Forms) (lam : ℂ) : Submodule ℂ (Fin 4 → ℂ) :=
  LinearMap.ker (Matrix.mulVecLin (foldMat a U lam))

theorem mem_foldKer {v : Fin 4 → ℂ} : v ∈ foldKer a U lam ↔ foldMat a U lam *ᵥ v = 0 := by
  simp [foldKer]

theorem foldW_zero (y y' : ℝ → ℂ) : foldW y y' 0 = ![y 0, y 0, y' 0, -y' 0] := by
  simp [foldW]

theorem foldInit_mem_ker {m κ : ℝ} (hH : HypH a m κ) (f : FoldEigSpace a U lam) :
    foldInit f.1 ∈ foldKer a U lam := by
  obtain ⟨y, y', y'', h, hf⟩ := f.2
  rw [mem_foldKer, foldInit_eq h hf, ← foldW_zero]
  exact foldMat_mulVec_foldW hH h

theorem foldInit_injective {m κ : ℝ} (hH : HypH a m κ) :
    Function.Injective (foldInitLin a U lam) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  obtain ⟨y, y', y'', h, hfy⟩ := f.2
  have h0 : foldW y y' 0 = 0 := by
    rw [foldW_zero, ← foldInit_eq h hfy]; exact hf
  have hz : ∀ x ∈ Icc (0 : ℝ) 1, y x = 0 ∧ y (-x) = 0 := by
    intro x hx
    have := foldW_eq_phi hH h hx
    rw [h0, Matrix.mulVec_zero] at this
    exact ⟨congrFun this 0, congrFun this 1⟩
  ext ⟨z, hz'⟩
  simp only [Submodule.coe_zero, Pi.zero_apply]
  rw [hfy ⟨z, hz'⟩]
  rcases le_total 0 z with h1 | h1
  · exact (hz z ⟨h1, hz'.2⟩).1
  · have := (hz (-z) ⟨by linarith, by linarith [hz'.1]⟩).2
    simpa using this

theorem foldInit_surjective {m κ : ℝ} (hH : HypH a m κ) {v : Fin 4 → ℂ}
    (hv : v ∈ foldKer a U lam) : ∃ f : FoldEigSpace a U lam, foldInit f.1 = v := by
  rw [mem_foldKer] at hv
  have hs := foldY_isSolution hH hv
  refine ⟨⟨fun x => foldY a lam v x, _, _, _, hs, fun x => rfl⟩, ?_⟩
  rw [foldInit_eq hs (fun x => rfl)]
  have g := ker_glue hv
  have e0 : foldY a lam v 0 = v 0 := by simp [foldY, foldX_zero]
  have e1 : foldY' a lam v 0 = v 2 := by simp [foldY', foldX_zero]
  rw [e0, e1]
  ext i
  fin_cases i <;> simp [g.1]
  linear_combination -g.2

/-- Линейный изоморфизм `y ↦ w(0)` пространства собственных функций на ядро. -/
def foldEquiv (h : Hyp a) : FoldEigSpace a U lam ≃ₗ[ℂ] foldKer a U lam :=
  LinearEquiv.ofBijective
    ((foldInitLin a U lam).codRestrict (foldKer a U lam) (fun f => by
      obtain ⟨m, κ, hH⟩ := h
      exact foldInit_mem_ker hH f))
    ⟨by
      obtain ⟨m, κ, hH⟩ := h
      exact fun f g hfg => foldInit_injective hH (congrArg Subtype.val hfg),
     by
      obtain ⟨m, κ, hH⟩ := h
      rintro ⟨v, hv⟩
      obtain ⟨f, hf⟩ := foldInit_surjective hH hv
      exact ⟨f, Subtype.ext hf⟩⟩

theorem foldEquiv_apply (h : Hyp a) (f : FoldEigSpace a U lam) :
    ((foldEquiv h f : foldKer a U lam) : Fin 4 → ℂ) = foldInit f.1 := rfl

/-- `λ` — собственное значение тогда и только тогда, когда `Δ(λ) = 0` (при (H)). -/
theorem isEigenvalue_iff_Delta_eq_zero (h : Hyp a) :
    IsEigenvalue a U lam ↔ Delta a U lam = 0 := by
  obtain ⟨m, κ, hH⟩ := h
  unfold Delta
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨y, y', y'', hE⟩
    obtain ⟨hs, x, hx, hyx⟩ := isEigenpair_iff.1 hE
    let f : FoldEigSpace a U lam := ⟨fun z => y z, y, y', y'', hs, fun _ => rfl⟩
    have hf : f ≠ 0 := by
      intro h0
      have := congrFun (congrArg Subtype.val h0) ⟨x, hx⟩
      exact hyx this
    refine ⟨foldInit f.1, ?_, mem_foldKer.1 (foldInit_mem_ker hH f)⟩
    intro h0
    exact hf (foldInit_injective hH (a := a) (U := U) (lam := lam)
      (by simpa [foldInitLin] using h0.trans (map_zero (foldInitLin a U lam)).symm))
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨f, hf⟩ := foldInit_surjective hH (mem_foldKer.2 hv)
    obtain ⟨y, y', y'', hs, hfy⟩ := f.2
    refine ⟨y, y', y'', isEigenpair_iff.2 ⟨hs, ?_⟩⟩
    by_contra hcon
    have hz : ∀ x ∈ Icc (-1 : ℝ) 1, y x = 0 := fun x hx => by
      by_contra hne
      exact hcon ⟨x, hx, hne⟩
    apply hv0
    rw [← hf, foldInit_eq hs hfy]
    have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have d2 : HasDerivAt y 0 0 := by
      refine (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds h0.1 h0.2] with t ht
      exact hz t (Ioo_subset_Icc_self ht)
    have e : y' 0 = 0 := (hs.hasDerivAt_y h0).unique d2
    have e0 : y 0 = 0 := hz 0 IsSolution.zero_mem_Icc
    simp [e, e0]
end GeneralBC
end Involution
