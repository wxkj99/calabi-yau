module

public import CalabiYau.Geometry.Complex.Basic
public import CalabiYau.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2Regularity
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.HigherOrder

/-!
# Sobolev regularity of the shifted Poisson source

The resolvent is `(1 - ΔG)⁻¹`. Thus its preimage for a weak solution of `ΔG u = f`
is the L² class `u - f`, not `f` or `u + f`. Smoothness of `f` supplies every finite
Sobolev order, and hence the same regularity for the shifted source.
-/

@[expose] public section

open scoped Manifold ContDiff ENNReal
open MeasureTheory CalabiYau.Analysis.Laplacian

namespace CalabiYau

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
  [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]

omit [MeasurableSpace M] [BorelSpace M] [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))] in
/-- A smooth Poisson source makes the resolvent preimage as regular as the solution. -/
theorem poisson_domainSource_memWkpChart
    (g : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (u_h : laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)
    (q : SmoothScalar g)
    (hweak : laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h =
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q)
    (k : ℕ)
    (hu : Sobolev.Chart.MemWkpChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) k 2
      (h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) : M → ℝ)) :
    Sobolev.Chart.MemWkpChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) k 2
      (laplacianDomain.preimage
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h : M → ℝ) := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let U := h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
    (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)
  let Q := smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q
  let F := laplacianDomain.preimage
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h
  have hF : F = U - Q := by
    have h := hweak
    rw [laplacianOp_apply] at h
    change U - F = Q at h
    calc
      F = U - (U - F) := by abel
      _ = U - Q := congrArg (fun v => U - v) h
  have hq : Sobolev.Chart.MemWkpChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) k 2 q.toFun :=
    CalabiYau.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) (by norm_num) k q.smooth
  have hsub := Sobolev.Chart.MemWkpChart_sub (by norm_num : (1 : ℝ≥0∞) ≤ 2) hu hq
  have hQ : (Q : M → ℝ) =ᵐ[RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g] q.toFun :=
    MemLp.coeFn_toLp (SmoothScalar.memLp_two
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) (g := g) q)
  have hFae : (F : M → ℝ) =ᵐ[RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g]
      (fun x => (U : M → ℝ) x - q.toFun x) := by
    rw [hF]
    filter_upwards [Lp.coeFn_sub U Q, hQ] with x hx hqx
    exact hx.trans (congrArg (fun z : ℝ => (U : M → ℝ) x - z) hqx)
  apply (Sobolev.Chart.MemWkpChart_congr_chartPushed_ae
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (u := (F : M → ℝ))
    (v := fun x => (U : M → ℝ) x - q.toFun x) ?_).mpr hsub
  intro α
  exact Sobolev.Chart.chartPushed_aeEq_of_ae_eq_riemannianMeasure
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g α
    (Lp.stronglyMeasurable F).measurable
    ((Lp.stronglyMeasurable U).measurable.sub q.smooth.continuous.measurable) hFae

end CalabiYau
