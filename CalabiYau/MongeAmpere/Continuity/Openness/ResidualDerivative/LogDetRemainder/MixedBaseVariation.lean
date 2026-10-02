module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetMatrixRemainder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Mixed-base difference of log-determinant Taylor remainders

Implementation-only matrix estimates for the chartwise Hölder transfer.
The parent imports this module privately; these declarations do not extend its public API.
All norms in the estimates are Frobenius norms.
-/

@[expose] public section

open scoped ComplexOrder ContDiff NNReal Matrix.Norms.Frobenius

namespace KahlerForm

theorem abs_re_trace_mul_le_frobenius_test {ι : Type*} [Fintype ι]
    (U V : Matrix ι ι ℂ) :
    |RCLike.re (U * V).trace| ≤ ‖U‖ * ‖V‖ := by
  classical
  exact Matrix.abs_re_trace_mul_le_frobenius U V

end KahlerForm
