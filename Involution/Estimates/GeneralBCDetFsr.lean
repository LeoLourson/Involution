module

public import Involution.Estimates.GeneralBCDetMain
public import Involution.Folding.GeneralBCFsr

/-! # Лемма lem:det с внешним входом S51 вместо гипотезы `hfsr`

`lem_det` (пакет G4) берёт вывод леммы lem:fsr гипотезой; здесь он получен из `lem_fsr`
(пакет G2c) при `h = 0`, и единственной внешней гипотезой остаётся `S51Theorem15`. -/

@[expose] public noncomputable section

namespace Involution
namespace GeneralBC

/-- lem:det при условии теоремы 1.5 S51. -/
theorem lem_det_of_S51 {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (hS : S51Theorem15) :
    ∃ η : ℂ → ℂ, DifferentiableOn ℂ η {0}ᶜ ∧
      (∀ ρ : ℂ, ρ ≠ 0 →
        ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) = cStar a U * (Fchar a U ρ + η ρ)) ∧
      ∀ ε > 0, ∃ r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ → ‖η ρ‖ * Real.exp (-(Ltot a) * |ρ.im|) ≤ ε :=
  lem_det h hU (fun s hs => lem_fsr a ⟨m, κ, h⟩ hS 0 le_rfl s hs)

end GeneralBC
end Involution
