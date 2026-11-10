module

public import Involution.Theorems.GeneralBCEigPair
public import Involution.Setup.RoucheZeros


/-! # Типы нулей с кратностями: конечность, счётность, число элементов в слое (пакет G6) -/

@[expose] public noncomputable section

open Set Metric

namespace Involution
namespace GeneralBC

variable {X : Type*}

theorem finite_zerTy_of_finite (m : X → ℕ) {S : Set X} (hS : S.Finite) :
    {p : ZerTy m | p.1 ∈ S}.Finite := by
  have : Finite S := hS.to_subtype
  let e : {p : ZerTy m // p.1 ∈ S} ≃ Σ x : S, Fin (m x.1) :=
    { toFun := fun p => ⟨⟨p.1.1, p.2⟩, p.1.2⟩
      invFun := fun q => ⟨⟨q.1.1, q.2⟩, q.1.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  have : Finite {p : ZerTy m // p.1 ∈ S} := Finite.of_equiv _ e.symm
  exact Set.finite_coe_iff.1 this

theorem countable_zerTy (m : X → ℕ) (hc : (Function.support m).Countable) :
    Countable (ZerTy m) := by
  have : Countable (Function.support m) := hc.to_subtype
  let f : ZerTy m → Function.support m × ℕ := fun p =>
    (⟨p.1, Nat.pos_iff_ne_zero.1 (Fin.pos p.2)⟩, p.2.val)
  refine Function.Injective.countable (f := f) ?_
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  simp only [f, Prod.mk.injEq] at h
  obtain ⟨h1, hij⟩ := h
  have hxy : x = y := congrArg Subtype.val h1
  subst hxy
  exact Sigma.ext rfl (heq_of_eq (Fin.ext hij))

theorem card_zerTy_fiber (m : X → ℕ) (z : X) :
    Nat.card {p : ZerTy m // p.1 = z} = m z := by
  have := (fiber_card m id z ((Set.finite_singleton z).subset (fun y hy => hy.1))).2
  simpa using this

end GeneralBC
end Involution
