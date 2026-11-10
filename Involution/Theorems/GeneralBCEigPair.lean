module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Fintype.Sigma

/-! # Теорема thm:eig (b): абстрактное сопоставление нулей по блокам (пакет G6)

Нули с кратностями функции `m : X → ℕ` — тип `Σ x, Fin (m x)`. Если два семейства нулей
разбиты на блоки (отображения `πX`, `πY` в общий тип блоков) и в каждом блоке суммы кратностей
конечны и равны, то есть биекция между типами нулей, сохраняющая блоки. -/

@[expose] public noncomputable section

open Set

namespace Involution
namespace GeneralBC

/-- Тип нулей с кратностями. -/
abbrev ZerTy {X : Type*} (m : X → ℕ) : Type _ := Σ x : X, Fin (m x)

variable {X Y T : Type*}

/-- Слой блока в типе нулей: конечен, число элементов — сумма кратностей. -/
theorem fiber_card (m : X → ℕ) (π : X → T) (t : T) (hfin : {x | π x = t ∧ m x ≠ 0}.Finite) :
    Finite {p : ZerTy m // π p.1 = t} ∧
      Nat.card {p : ZerTy m // π p.1 = t} = ∑ᶠ x ∈ {x | π x = t}, m x := by
  have : Fintype {x | π x = t ∧ m x ≠ 0} := hfin.fintype
  let e : {p : ZerTy m // π p.1 = t} ≃ Σ x : {x | π x = t ∧ m x ≠ 0}, Fin (m x.1) :=
    { toFun := fun p => ⟨⟨p.1.1, p.2, Nat.pos_iff_ne_zero.1 (Fin.pos p.1.2)⟩, p.1.2⟩
      invFun := fun q => ⟨⟨q.1.1, q.2⟩, q.1.2.1⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  have : Finite {p : ZerTy m // π p.1 = t} := Finite.of_equiv _ e.symm
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have h1 : ∑ᶠ x ∈ {x | π x = t}, m x = ∑ x ∈ hfin.toFinset, m x := by
    refine finsum_mem_eq_sum_of_inter_support_eq m ?_
    rw [hfin.coe_toFinset]; ext x; simp [Function.mem_support]
  rw [h1]
  exact (Finset.sum_subtype hfin.toFinset (fun x => by simp) m).symm

/-- Биекция нулей, сохраняющая блоки, если суммы кратностей в блоках конечны и равны. -/
theorem exists_equiv_of_fiber_sum (mX : X → ℕ) (mY : Y → ℕ) (πX : X → T) (πY : Y → T)
    (hX : ∀ t, {x | πX x = t ∧ mX x ≠ 0}.Finite) (hY : ∀ t, {y | πY y = t ∧ mY y ≠ 0}.Finite)
    (hsum : ∀ t, ∑ᶠ x ∈ {x | πX x = t}, mX x = ∑ᶠ y ∈ {y | πY y = t}, mY y) :
    ∃ σ : ZerTy mX ≃ ZerTy mY, ∀ p, πY (σ p).1 = πX p.1 := by
  have e1 : ∀ t, Nonempty ({p : ZerTy mX // πX p.1 = t} ≃ {q : ZerTy mY // πY q.1 = t}) := by
    intro t
    obtain ⟨f1, c1⟩ := fiber_card mX πX t (hX t)
    obtain ⟨f2, c2⟩ := fiber_card mY πY t (hY t)
    have := Fintype.ofFinite {p : ZerTy mX // πX p.1 = t}
    have := Fintype.ofFinite {q : ZerTy mY // πY q.1 = t}
    refine ⟨Fintype.equivOfCardEq ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, c1, c2, hsum t]
  let e := fun t => (e1 t).some
  let s1 := Equiv.sigmaFiberEquiv (fun p : ZerTy mX => πX p.1)
  let s2 := Equiv.sigmaFiberEquiv (fun q : ZerTy mY => πY q.1)
  refine ⟨s1.symm.trans ((Equiv.sigmaCongrRight e).trans s2), fun p => ?_⟩
  exact (e (πX p.1) ⟨p, rfl⟩).2

end GeneralBC
end Involution
