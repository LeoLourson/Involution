module

public import Involution.Folding.GeneralBC

/-! # Допустимые краевые формы линии G

Условия на краевые формы записи C24: формы линейно независимы, нормированы в смысле S48 и
расставлены так, что `κ₁ ≥ κ₂`. Таблица главной части `F` предполагает эту расстановку. -/

@[expose] public noncomputable section

namespace Involution
namespace GeneralBC

/-- Условия на формы C24: линейно независимы, нормированы, расставлены `κ₁ ≥ κ₂`. -/
structure AdmissibleForms (U : Forms) : Prop where
  indep : U.LinIndep
  normalized : U.IsNormalized
  ordered : U.IsOrdered

end GeneralBC
end Involution
