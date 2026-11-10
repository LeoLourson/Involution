module

public import Involution.Estimates.DirichletSeriesIrrational

/-! Критерий сильной регулярности для задачи Дирихле (предложение `prop:dir`).
Для `a, b > 0`:
* `dirCS a b` (`ε = 1`) сильно регулярна ⇔ `a / b = p / q`, `gcd(p, q) = 1`, `q` нечётно;
* `dirSC a b` (`ε = -1`) сильно регулярна ⇔ `a / b = p / q`, `gcd(p, q) = 1`, `p` нечётно.
При чётном `q` бесконечно много двукратных нулей, при иррациональном `a / b` нули сближаются. -/

@[expose] public noncomputable section

namespace Involution

/-- Чётный знаменатель: бесконечно много нулей кратности не 1. -/
theorem not_dirCS_strongRegular_of_even (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (p q : ℕ)
    (hp : 0 < p) (hcop : Nat.Coprime p q) (hev : Even q)
    (h : b * p = a * q) : ¬ DirichletStrongRegular (dirCS a b) := by
  rintro ⟨-, hfin⟩
  have hpodd : Odd p := by
    rcases Nat.even_or_odd p with hpe | hpo
    · exfalso
      have := Nat.dvd_gcd (even_iff_two_dvd.mp hpe) (even_iff_two_dvd.mp hev)
      rw [Nat.Coprime.gcd_eq_one hcop] at this
      omega
    · exact hpo
  obtain ⟨s, hs⟩ := hpodd
  obtain ⟨d, hd⟩ := hev
  have hpR : (p : ℝ) = 2 * s + 1 := by exact_mod_cast hs
  have hqR : (q : ℝ) = d + d := by exact_mod_cast hd
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hπ := Real.pi_pos
  let ρ : ℕ → ℂ := fun t => ((p * (2 * (t : ℝ) + 1) * Real.pi / (2 * a) : ℝ) : ℂ)
  have hmem : ∀ t : ℕ, ρ t ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ dirCS a b ρ = 0 ∧
      analyticOrderAt (dirCS a b) ρ ≠ 1} := by
    intro t
    have hc : Complex.cos (ρ t * a) = 0 := by
      rw [Complex.cos_eq_zero_iff]
      refine ⟨(2 * s * t + s + t : ℕ), ?_⟩
      have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      have hsC : (p : ℂ) = 2 * s + 1 := by exact_mod_cast hpR
      simp only [ρ]; push_cast; rw [hsC]; field_simp; ring
    have hsn : Complex.sin (ρ t * b) = 0 := by
      rw [Complex.sin_eq_zero_iff]
      refine ⟨((2 * t + 1) * d : ℕ), ?_⟩
      have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
      have hbC : (b : ℂ) * p = a * q := by exact_mod_cast h
      have hqC : (q : ℂ) = d + d := by exact_mod_cast hqR
      have hb' : (b : ℂ) = a * q / p := by field_simp; linear_combination hbC
      simp only [ρ]; push_cast; rw [hb', hqC]; field_simp; ring
    have hF : dirCS a b (ρ t) = 0 := by unfold dirCS; rw [hc, zero_mul]
    refine ⟨?_, hF, (dirCS_order_ne_one_iff a b ha.ne' hb.ne' _ hF).mpr ⟨hc, hsn⟩⟩
    simp only [ρ]; rw [Complex.ofReal_re]; positivity
  have hinj : Function.Injective ρ := by
    intro t t' htt
    have h1 : p * (2 * (t : ℝ) + 1) * Real.pi / (2 * a) =
        p * (2 * (t' : ℝ) + 1) * Real.pi / (2 * a) := Complex.ofReal_injective htt
    field_simp at h1
    have : (t : ℝ) = t' := by nlinarith
    exact_mod_cast this
  exact (Set.infinite_range_of_injective hinj)
    (hfin.subset (by rintro _ ⟨t, rfl⟩; exact hmem t))

/-- Критерий для `cos(ρ a) sin(ρ b)`: рациональное отношение с нечётным знаменателем. -/
theorem dirCS_strongRegular_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    DirichletStrongRegular (dirCS a b) ↔
      ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ Nat.Coprime p q ∧ Odd q ∧ a / b = (p : ℝ) / q := by
  constructor
  · intro hSR
    have hrat : ¬ Irrational (a / b) := fun hirr =>
      not_dirCS_strongRegular_of_irrational a b ha hb hirr hSR
    obtain ⟨r, hr⟩ := not_not.mp hrat
    have hrpos : 0 < r := by
      have : (0 : ℝ) < r := by rw [hr]; positivity
      exact_mod_cast this
    have hnum : 0 < r.num := Rat.num_pos.mpr hrpos
    have hnat : (r.num.toNat : ℝ) = r.num := by
      have : (r.num.toNat : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
      exact_mod_cast this
    have hrat' : a / b = (r.num.toNat : ℝ) / r.den := by
      rw [← hr, Rat.cast_def, hnat]
    have hcop : Nat.Coprime r.num.toNat r.den := by
      have h1 := r.reduced
      have h2 : r.num.natAbs = r.num.toNat := by omega
      rwa [h2] at h1
    have hq0 : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_pos.ne'
    refine ⟨r.num.toNat, r.den, by omega, r.den_pos, hcop, ?_, hrat'⟩
    by_contra hnodd
    refine not_dirCS_strongRegular_of_even a b ha hb r.num.toNat r.den (by omega) hcop
      (Nat.not_odd_iff_even.mp hnodd) ?_ hSR
    rw [div_eq_div_iff hb.ne' hq0] at hrat'
    linarith
  · rintro ⟨p, q, hp, hq, -, hodd, h⟩
    refine dirCS_strongRegular_of_rat a b ha hb p q hq hodd ?_
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp at h
    linarith

/-- Нули `dirSC a b = sin(ρ a) cos(ρ b)`: серии `jπ/a` и `(2k+1)π/(2b)`. -/
theorem dirSC_eq_zero_iff (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (ρ : ℂ) :
    dirSC a b ρ = 0 ↔ (∃ j : ℤ, ρ = ((j * Real.pi / a : ℝ) : ℂ)) ∨
      (∃ k : ℤ, ρ = (((2 * k + 1) * Real.pi / (2 * b) : ℝ) : ℂ)) := by
  rw [dirSC_eq_dirCS, dirCS_eq_zero_iff b a hb ha ρ, or_comm]

/-- Критерий для `sin(ρ a) cos(ρ b)`: рациональное отношение с нечётным числителем. -/
theorem dirSC_strongRegular_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    DirichletStrongRegular (dirSC a b) ↔
      ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ Nat.Coprime p q ∧ Odd p ∧ a / b = (p : ℝ) / q := by
  rw [dirSC_eq_dirCS, dirCS_strongRegular_iff b a hb ha]
  constructor
  · rintro ⟨p, q, hp, hq, hc, ho, h⟩
    refine ⟨q, p, hq, hp, hc.symm, ho, ?_⟩
    rw [← inv_div, h, inv_div]
  · rintro ⟨p, q, hp, hq, hc, ho, h⟩
    refine ⟨q, p, hq, hp, hc.symm, ho, ?_⟩
    rw [← inv_div, h, inv_div]

end Involution
