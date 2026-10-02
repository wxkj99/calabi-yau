module

public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Euclidean.CoordinateFlux
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Algebra.Support

@[expose] public section

namespace ContinuousAlternatingMap

variable {n : ℕ}

/-- Each signed coordinate coefficient of a compactly supported `C¹` form is `C¹`
and supported within the support of the form. In dimension one (`n = 0`) this
is simply the coefficient of a zero-form. -/
theorem contDiff_hasCompactSupport_stokesCoordinateFlux
    {ω : (Fin (n + 1) → ℝ) →
      (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    (hω : ContDiff ℝ 1 ω) (hcompact : HasCompactSupport ω) :
    ContDiff ℝ 1 (stokesCoordinateFlux ω) ∧
      HasCompactSupport (stokesCoordinateFlux ω) := by
  constructor
  · apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ 1 (fun x => (-1 : ℝ) ^ i.val *
      ω x (i.removeNth (fun j : Fin (n + 1) =>
        (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ))))
    have heval : ContDiff ℝ 1 (fun x => ω x
        (i.removeNth (fun j : Fin (n + 1) =>
          (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ)))) := by
      exact ((ContinuousAlternatingMap.apply ℝ (Fin (n + 1) → ℝ) ℝ
        (i.removeNth (fun j : Fin (n + 1) =>
          (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ)))).contDiff.comp hω)
    exact contDiff_const.mul heval
  · apply HasCompactSupport.intro (K := tsupport ω) hcompact
    intro x hx
    have hzero : ω x = 0 := by
      exact (Function.notMem_support.mp (fun h => hx (subset_closure h)))
    ext i
    change (-1 : ℝ) ^ i.val * ω x
      (i.removeNth (fun j : Fin (n + 1) =>
        (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ))) = 0
    rw [hzero]
    simp

end ContinuousAlternatingMap
