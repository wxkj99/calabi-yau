module

public import CalabiYau.Geometry.Complex.DDBar.Complexification
public import CalabiYau.Geometry.Complex.DDBar.TypeDecomposition
public import CalabiYau.Geometry.Kahler.Basic

import CalabiYau.Geometry.Complex.DDBar.ScalarRoute
import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.Componentwise
import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.Componentwise.RestrictOpen
import Comparator.PoissonSolvability

/-!
# The complex-valued `∂∂̄` lemma

The real and imaginary components of a complex form field are kept separately so that the existing
real chart calculus remains authoritative. The theorem below is the complex-valued H5 statement;
the final translation to the frozen real predicate lives in `RealOneOneBridge`.
-/

@[expose] public section

open scoped Manifold ContDiff

/-- A complex-valued function represented by its real and imaginary parts. -/
abbrev ComplexFunction (M : Type*) := (M → ℝ) × (M → ℝ)

/-- Smoothness of a complex-valued function is smoothness of its two real components. -/
def ComplexFunction.IsSmooth (n : ℕ) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] (f : ComplexFunction M) : Prop :=
  ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f.1 ∧
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f.2

/-- The complex-valued `i∂∂̄` of a pair of real functions, componentwise. -/
noncomputable def complexMddbar (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] (f : ComplexFunction M) :
    ComplexFormField (EuclideanSpace ℂ (Fin n)) M 2 :=
  (mddbar n f.1, mddbar n f.2)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem component_connected [CompactSpace M] (c : ConnectedComponents M) :
    ConnectedSpace (KahlerForm.componentOpen (n := n) c) := by
  let U := KahlerForm.componentOpen (n := n) c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hset : (U : Set M) = connectedComponent x := by
    ext y
    simp [U, KahlerForm.componentOpen, connectedComponent_eq_iff_mem]
  have hconn : IsConnected (U : Set M) := by
    rw [hset]
    exact isConnected_connectedComponent
  exact isConnected_iff_connectedSpace.mp hconn

private theorem component_poisson_solution [T2Space M] [CompactSpace M]
    (ω₀ : KahlerForm n M) {η : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hηsmooth : η.IsSmooth) (hηone : η.IsOneOne) (hηexact : η.IsExact)
    (c : ConnectedComponents M) :
    ∃ u : KahlerForm.componentOpen (n := n) c → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u ∧
      (ω₀.restrictOpen (KahlerForm.componentOpen (n := n) c)).laplacian u =
        fun x : KahlerForm.componentOpen (n := n) c =>
          ContinuousAlternatingMap.relTrace (ω₀ (x : M)) (η (x : M)) := by
  let U := KahlerForm.componentOpen (n := n) c
  let ωU := ω₀.restrictOpen U
  let ηU := η.restrictOpen U
  letI : CompactSpace U := by
    apply isCompact_iff_compactSpace.mp
    letI : LocallyPathConnectedSpace M :=
      ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℂ (Fin n)) M
    have hclopen : IsClopen (ConnectedComponents.mk ⁻¹' ({c} : Set (ConnectedComponents M))) :=
      (isClopen_discrete {c}).preimage ConnectedComponents.continuous_coe
    exact hclopen.isClosed.isCompact
  letI : ConnectedSpace U := component_connected (M := M) (n := n) c
  letI : MeasurableSpace U := borel U
  letI : BorelSpace U := ⟨rfl⟩
  have hηUsmooth : ηU.IsSmooth := (η.isSmooth_extDeriv_restrictOpen hηsmooth U).1
  have hηUone : ηU.IsOneOne := fun x => hηone x
  have hηUexact : ηU.IsExact := η.isExact_restrictOpen hηexact U
  obtain ⟨htraceSmooth, hmean⟩ :=
    ωU.trace_smooth_and_integral_eq_zero_of_isExact hηUsmooth hηUone hηUexact
  have hpoisson := CalabiYau.poissonSolvable_of_compact (n := n) (M := U) ωU
  obtain ⟨u, hu, hlap⟩ := hpoisson
    (fun x => ContinuousAlternatingMap.relTrace (ωU x) (ηU x)) htraceSmooth hmean
  refine ⟨u, hu, ?_⟩
  funext x
  simpa [ωU, ηU, KahlerForm.restrictOpen, FormField.restrictOpen] using congrFun hlap x

private theorem exists_realMddbar_eq_of_isExact [T2Space M] [CompactSpace M]
    (ω₀ : KahlerForm n M) {η : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hηsmooth : η.IsSmooth)
    (hηone : η.IsOneOne)
    (hηexact : η.IsExact) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f ∧
      η = mddbar n f := by
  let trace : M → ℝ := fun x => ContinuousAlternatingMap.relTrace (ω₀ x) (η x)
  obtain ⟨f, hf, hlap⟩ :=
    KahlerForm.exists_laplacian_eq_of_componentwise (ω₀ := ω₀) trace (by
      intro c
      obtain ⟨u, hu, hlapU⟩ := component_poisson_solution ω₀ hηsmooth hηone hηexact c
      refine ⟨u, hu, ?_⟩
      intro x
      have hx := congrFun hlapU x
      change ContinuousAlternatingMap.relTrace (ω₀ (x : M)) (mddbar n u x) = trace x
      simpa [trace, KahlerForm.laplacian, KahlerForm.restrictOpen,
        FormField.restrictOpen] using hx)
  let γ : FormField (EuclideanSpace ℂ (Fin n)) M 2 := η - mddbar n f
  have hγsmooth : γ.IsSmooth := hηsmooth.sub (isSmooth_mddbar hf)
  have hγone : γ.IsOneOne := fun x => (hηone x).sub (isOneOne_mddbar hf x)
  have hγexact : γ.IsExact := hηexact.sub (isExact_mddbar hf)
  have hγtrace : ∀ x, ContinuousAlternatingMap.relTrace (ω₀ x) (γ x) = 0 := by
    intro x
    have hx := congrFun hlap x
    change ContinuousAlternatingMap.relTrace (ω₀ x) (mddbar n f x) =
      ContinuousAlternatingMap.relTrace (ω₀ x) (η x) at hx
    change ContinuousAlternatingMap.relTrace (ω₀ x) (η x - mddbar n f x) = 0
    rw [ContinuousAlternatingMap.relTrace_sub, hx, sub_self]
  have hIntegral := ω₀.integral_primitive_sq_eq_zero hγsmooth hγone hγexact hγtrace
  have hγzero : γ = 0 := by
    rw [ω₀.volume_eq_riemannianVolumeMeasure] at hIntegral
    have h := (ComplexFormField.integral_pointwiseHermitianInner_self_eq_zero_iff
      ω₀.toRiemannianMetric 2 (γ, (0 : FormField (EuclideanSpace ℂ (Fin n)) M 2))
      ⟨hγsmooth, FormField.isSmooth_zero⟩).mp hIntegral
    exact congrArg Prod.fst h
  refine ⟨f, hf, ?_⟩
  exact sub_eq_zero.mp hγzero

/-- On a compact Kähler manifold, every smooth, exact complex-valued `(1,1)`-form is the complex
`i∂∂̄` of a smooth complex-valued function. The Kähler form supplies the Hermitian metric for the
Hodge-theoretic proof. -/
theorem exists_complexMddbar_eq_of_isExact [T2Space M] [CompactSpace M]
    (ω₀ : KahlerForm n M) {α : ComplexFormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hαsmooth : α.IsSmooth)
    (hαone : α.IsOneOne (complexTangentJ n))
    (hαexact : α.IsExact) :
    ∃ f : ComplexFunction M, ComplexFunction.IsSmooth n f ∧ α = complexMddbar n f := by
  obtain ⟨β, hβsmooth, hβext⟩ := hαexact
  have hαreExact : α.1.IsExact := by
    refine ⟨β.1, hβsmooth.1, ?_⟩
    exact congrArg Prod.fst hβext
  have hαimExact : α.2.IsExact := by
    refine ⟨β.2, hβsmooth.2, ?_⟩
    exact congrArg Prod.snd hβext
  have hαreOne : α.1.IsOneOne := by
    intro x
    change ∀ u v, (α.1 x) ![Complex.I • u, Complex.I • v] = (α.1 x) ![u, v]
    intro u v
    simpa [complexTangentJ] using (hαone x u v).1
  have hαimOne : α.2.IsOneOne := by
    intro x
    change ∀ u v, (α.2 x) ![Complex.I • u, Complex.I • v] = (α.2 x) ![u, v]
    intro u v
    simpa [complexTangentJ] using (hαone x u v).2
  obtain ⟨fRe, hfRe, hRe⟩ := exists_realMddbar_eq_of_isExact ω₀ hαsmooth.1
    hαreOne hαreExact
  obtain ⟨fIm, hfIm, hIm⟩ := exists_realMddbar_eq_of_isExact ω₀ hαsmooth.2
    hαimOne hαimExact
  refine ⟨(fRe, fIm), ⟨hfRe, hfIm⟩, ?_⟩
  exact Prod.ext hRe hIm
