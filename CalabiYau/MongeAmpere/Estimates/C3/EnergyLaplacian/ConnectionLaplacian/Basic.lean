module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors

/-!
# Canonical chart curvature and its holomorphic covariant derivative

Székelyhidi, §3.3, proof of Lemma 3.9, the Bianchi calculation following
(3.15), printed p. 45. The lowered derivative has two lower holomorphic
connection corrections.
Its argument order is `(p,j,q,k,l)`; raising uses inverse entry `(l,i)`.
Keep this public boundary independent of the deep finite-jet representation.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

@[expose]
noncomputable def c3CurvatureCovariantZ
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p j q k l : Fin n) : ℂ :=
  wirtingerDerivInChart (fun w => chartCurvature g w j q k l) z p -
    ∑ r, christoffelInChart g z r p j * chartCurvature g z r q k l -
    ∑ r, christoffelInChart g z r p k * chartCurvature g z j q r l

@[expose]
noncomputable def c3RaisedCurvatureInChart
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (i j k q : Fin n) : ℂ :=
  ∑ l, (g z)⁻¹ l i * chartCurvature g z j q k l

end KahlerForm
