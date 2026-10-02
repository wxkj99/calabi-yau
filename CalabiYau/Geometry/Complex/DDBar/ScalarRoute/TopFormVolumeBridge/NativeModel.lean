module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TopFormVolumeBridge.PiReindex
public import CalabiYau.Geometry.Manifold.DifferentialForm.Pullback
public import CalabiYau.Geometry.Complex.DDBar.FormFieldBridge
public import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# The genuine native-to-Pi model transport

The Pi atlas is the native atlas composed with the inverse of the existing
interleaved coordinate equivalence. Both geometric identity maps are smooth.
Form transport is the existing geometric pullback along that identity, not an
arbitrary real-linear map or a scalar normalization.

These declarations give the model, pointwise form, support, and derivative
formulas used in coefficient, cutoff, and volume calculations. They do
not construct an integral, assert a fixed-centre coefficient identity, or prove
Stokes. In particular no metric, volume, orientation, compactness or T2 premise
is needed. Degree zero is included and cannot be rescaled by this transport.

Sources: Lee, Introduction to Smooth Manifolds, second edition, Chapters 1-2
(charts and smooth coordinate changes), Chapter 14 (geometric pullback of forms);
Mathlib's ChartedSpace.comp and isManifold_of_contDiffOn; the project's public
DifferentialForm.pullbackLinearMap and exteriorDerivative_pullback. The reverse
Scalar and cutoff transport are treated separately.
-/

@[expose] public section

open scoped Manifold ContDiff

noncomputable section

namespace HTopFormVolumeBridge

/-- The canonical Pi atlas, leaving the existing native complex atlas unchanged. -/
@[instance_reducible] def nativePiCharts {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] :
    ChartedSpace (Fin (2 * n) → ℝ) M := by
  let e := (hTopPiToComplexEquiv n).symm.toHomeomorph.toOpenPartialHomeomorph
  letI : ChartedSpace (Fin (2 * n) → ℝ) (EuclideanSpace ℂ (Fin n)) :=
    e.singletonChartedSpace (by simp [e])
  exact ChartedSpace.comp (Fin (2 * n) → ℝ) (EuclideanSpace ℂ (Fin n)) M

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]

/-- The selected Pi chart is the native chart followed by the actual inverse coordinate map. -/
theorem nativePiChartAt (c : M) :
    (letI := nativePiCharts (n := n) (M := M)
     chartAt (Fin (2 * n) → ℝ) c) =
      (chartAt (EuclideanSpace ℂ (Fin n)) c).trans
        (hTopPiToComplexEquiv n).symm.toHomeomorph.toOpenPartialHomeomorph := by
  rfl

/-- The transformed and native selected charts have the same source. -/
theorem nativePiChartAt_source (c : M) :
    (letI := nativePiCharts (n := n) (M := M)
     (chartAt (Fin (2 * n) → ℝ) c).source) =
      (chartAt (EuclideanSpace ℂ (Fin n)) c).source := by
  change (chartAt (EuclideanSpace ℂ (Fin n)) c).source ∩
      (chartAt (EuclideanSpace ℂ (Fin n)) c) ⁻¹' Set.univ =
    (chartAt (EuclideanSpace ℂ (Fin n)) c).source
  simp

/-- Native real smoothness proves smoothness of the explicitly transformed Pi atlas. -/
theorem nativePiIsManifold
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] :
    letI := nativePiCharts (n := n) (M := M)
    IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := by
  let e := hTopPiToComplexEquiv n
  let p := e.symm.toHomeomorph.toOpenPartialHomeomorph
  let : ChartedSpace (Fin (2 * n) → ℝ) M := nativePiCharts
  apply isManifold_of_contDiffOn 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M
  rintro a' b' ⟨a, ha, p₁, hp₁, rfl⟩ ⟨b, hb, p₂, hp₂, rfl⟩
  have hp₁' : p₁ = p := p.singletonChartedSpace_mem_atlas_eq (by simp [p]) p₁ hp₁
  have hp₂' : p₂ = p := p.singletonChartedSpace_mem_atlas_eq (by simp [p]) p₂ hp₂
  subst p₁
  subst p₂
  have hlocal : ContDiffOn ℝ ∞ (a.symm.trans b) (a.symm.trans b).source := by
    have hcompat := (contDiffGroupoid ∞ 𝓘(ℝ, EuclideanSpace ℂ (Fin n))).compatible ha hb
    simpa only [contDiffPregroupoid, mfld_simps] using hcompat.1
  have hmaps : Set.MapsTo e ((a.trans p).symm.trans (b.trans p)).source
      (a.symm.trans b).source := by
    intro z hz
    simpa [p, OpenPartialHomeomorph.trans_source] using hz
  have hcomp := e.symm.contDiff.contDiffOn.comp
    (hlocal.comp e.contDiff.contDiffOn hmaps) (fun _ _ => Set.mem_univ _)
  simpa [p, Function.comp_def] using hcomp

/-- The identity from the actual Pi atlas to the native atlas is smooth. -/
theorem nativePiIdentitySmooth
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] :
    letI := nativePiCharts (n := n) (M := M)
    ContMDiff 𝓘(ℝ, Fin (2 * n) → ℝ) 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞
      (id : M → M) := by
  let : ChartedSpace (Fin (2 * n) → ℝ) M := nativePiCharts
  let : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
  let e := hTopPiToComplexEquiv n
  let p := e.symm.toHomeomorph.toOpenPartialHomeomorph
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuousAt_id, ?_⟩
  have heq :
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x ∘ id ∘
        (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) x).symm) =ᶠ[
          nhds (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) x x)] e := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ, Fin (2 * n) → ℝ)) x] with z hz
    have hz' : e z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).target := by
      simp only [mfld_simps] at hz
      change z ∈ ((chartAt (EuclideanSpace ℂ (Fin n)) x).trans p).target at hz
      simpa [p, OpenPartialHomeomorph.trans_target] using hz
    change chartAt (EuclideanSpace ℂ (Fin n)) x
      ((chartAt (EuclideanSpace ℂ (Fin n)) x).symm (e z)) = e z
    exact (chartAt (EuclideanSpace ℂ (Fin n)) x).right_inv hz'
  exact (e.contDiff.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The genuine geometric form transport is pullback along the actual smooth identity. -/
def nativeToPiForms
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] (k : ℕ) :
    letI := nativePiCharts (n := n) (M := M)
    letI : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
    CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M k →ₗ[ℝ]
      CalabiYau.DifferentialForm 𝓘(ℝ, Fin (2 * n) → ℝ) M k := by
  let : ChartedSpace (Fin (2 * n) → ℝ) M := nativePiCharts
  let : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
  exact CalabiYau.DifferentialForm.pullbackLinearMap (id : M → M) nativePiIdentitySmooth k

/-- Geometric transport commutes with the two actual exterior derivatives. -/
theorem nativeToPiForms_exteriorDerivative
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] {k : ℕ}
    (η : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M k) :
    letI := nativePiCharts (n := n) (M := M)
    letI : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
    nativeToPiForms (k + 1) (CalabiYau.DifferentialForm.exteriorDerivative η) =
      CalabiYau.DifferentialForm.exteriorDerivative (nativeToPiForms k η) := by
  let : ChartedSpace (Fin (2 * n) → ℝ) M := nativePiCharts
  let : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
  exact CalabiYau.DifferentialForm.exteriorDerivative_pullback
    (id : M → M) nativePiIdentitySmooth η

/-- The preferred-chart derivative of the actual identity is precisely the existing e_n. -/
theorem nativePiIdentityHasMFDeriv
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] (x : M) :
    letI := nativePiCharts (n := n) (M := M)
    letI : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
    HasMFDerivAt 𝓘(ℝ, Fin (2 * n) → ℝ) 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      (id : M → M) x
      (CalabiYau.tangentLinearMapOfModel
        (I := 𝓘(ℝ, Fin (2 * n) → ℝ)) (I' := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
        (x := x) (y := x) (hTopPiToComplexEquiv n).toContinuousLinearMap) := by
  let : ChartedSpace (Fin (2 * n) → ℝ) M := nativePiCharts
  let : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
  let e := hTopPiToComplexEquiv n
  let p := e.symm.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨continuousAt_id, ?_⟩
  change HasFDerivWithinAt
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x ∘ id ∘
      (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) x).symm)
    e.toContinuousLinearMap (Set.range 𝓘(ℝ, Fin (2 * n) → ℝ))
    (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) x x)
  have heq :
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x ∘ id ∘
        (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) x).symm) =ᶠ[
          nhds (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) x x)] e := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ, Fin (2 * n) → ℝ)) x] with z hz
    have hz' : e z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).target := by
      simp only [mfld_simps] at hz
      change z ∈ ((chartAt (EuclideanSpace ℂ (Fin n)) x).trans p).target at hz
      simpa [p, OpenPartialHomeomorph.trans_target] using hz
    change chartAt (EuclideanSpace ℂ (Fin n)) x
      ((chartAt (EuclideanSpace ℂ (Fin n)) x).symm (e z)) = e z
    exact (chartAt (EuclideanSpace ℂ (Fin n)) x).right_inv hz'
  exact (e.toContinuousLinearMap.hasFDerivAt.congr_of_eventuallyEq heq).hasFDerivWithinAt

/-- Pointwise unbundling is the actual pullback by e_n. This is not a fixed-centre chart law. -/
theorem nativeToPiForms_toFormField
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] {k : ℕ}
    (η : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M k) (x : M) :
    letI := nativePiCharts (n := n) (M := M)
    letI : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
    (nativeToPiForms k η).toFormField x =
      (η.toFormField x).compContinuousLinearMap (hTopPiToComplexEquiv n).toContinuousLinearMap := by
  let : ChartedSpace (Fin (2 * n) → ℝ) M := nativePiCharts
  let : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
  ext v
  change η x (fun i => mfderiv 𝓘(ℝ, Fin (2 * n) → ℝ)
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (id : M → M) x
        ((CalabiYau.tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, Fin (2 * n) → ℝ)) x).symm (v i))) = _
  rw [(nativePiIdentityHasMFDeriv x).mfderiv]
  rfl

end HTopFormVolumeBridge
