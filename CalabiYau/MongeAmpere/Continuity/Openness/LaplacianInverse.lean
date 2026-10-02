module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces
public import CalabiYau.Geometry.Kahler.Poisson
public import CalabiYau.Analysis.Elliptic.Schauder
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.ForwardBound
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.PoissonInverse
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.ForwardEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.Completion

/-!
# The Laplacian on mean-zero little Hölder spaces

For a Kähler form, the complex Laplacian is an isomorphism from mean-zero `C^{2,α}` functions to
mean-zero `C^{0,α}` functions.  The chartwise estimate gives a closed range, smooth Poisson
solutions give a dense range in the little Hölder target, and the maximum principle gives a
trivial kernel after imposing mean zero.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/- The smooth Poisson solver becomes an inverse on the mean-zero subspace after fixing its
constant ambiguity.  This is the algebraic part of the linearized-operator argument; Hölder
boundedness and completeness are still needed before applying the Banach-space IFT. -/

/-- The Laplacian extends to a continuous linear equivalence between the mean-zero little Hölder
spaces. -/
theorem exists_laplacian_equiv (ω₁ : KahlerForm n M) (α : ℝ≥0)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hSch : InteriorSchauderEstimate n) (hPoisson : ω₁.PoissonSolvable)
    [P : ContinuityHolderPair ω₁ α]
    (hSmoothDense : closure (Set.range fun f :
      smoothMeanZeroChartHolderCore ω₁ P.finiteChartCover 0 α P.normedDataC0 =>
        ((f : SmoothChartHolderCore P.finiteChartCover 0 α) :
          LittleHolder P.finiteChartCover 0 α P.normedDataC0)) =
      (P.C0 : Set (LittleHolder P.finiteChartCover 0 α P.normedDataC0))) :
    ∃ L : P.C2 ≃L[ℝ] P.C0,
      ∀ u, P.evalC0 (L u) = ω₁.laplacian (P.evalC2 u) := by
  classical
  by_cases hM : IsEmpty M
  · have : Subsingleton (ContMDiffMap
        (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (modelWithCornersSelf ℝ ℝ) M ℝ ∞) := by
      refine ⟨fun f g ↦ ContMDiffMap.ext ?_⟩
      intro x
      exact (hM.false x).elim
    have : Subsingleton (SmoothChartHolderCore P.finiteChartCover 2 α) := by
      refine ⟨fun f g ↦ ?_⟩
      exact congrArg (fun h : ContMDiffMap
        (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (modelWithCornersSelf ℝ ℝ) M ℝ ∞ ↦
          (⟨h⟩ : SmoothChartHolderCore P.finiteChartCover 2 α))
        (Subsingleton.elim f.smoothMap g.smoothMap)
    have : Subsingleton (SmoothChartHolderCore P.finiteChartCover 0 α) := by
      refine ⟨fun f g ↦ ?_⟩
      exact congrArg (fun h : ContMDiffMap
        (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (modelWithCornersSelf ℝ ℝ) M ℝ ∞ ↦
          (⟨h⟩ : SmoothChartHolderCore P.finiteChartCover 0 α))
        (Subsingleton.elim f.smoothMap g.smoothMap)
    let : NormedAddCommGroup (SmoothChartHolderCore P.finiteChartCover 2 α) :=
      smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 2 α P.normedDataC2
    let : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 2 α) :=
      smoothChartHolderCoreNormedSpace P.finiteChartCover 2 α P.normedDataC2
    let : NormedAddCommGroup (SmoothChartHolderCore P.finiteChartCover 0 α) :=
      smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 0 α P.normedDataC0
    let : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 0 α) :=
      smoothChartHolderCoreNormedSpace P.finiteChartCover 0 α P.normedDataC0
    have hDense2 : Dense (Set.range fun f : SmoothChartHolderCore P.finiteChartCover 2 α =>
        (f : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) :=
      UniformSpace.Completion.denseRange_coe
    have hRange2 : Set.range (fun f : SmoothChartHolderCore P.finiteChartCover 2 α =>
        (f : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) = {0} := by
      ext x
      constructor
      · rintro ⟨f, rfl⟩
        have hf : f = 0 := Subsingleton.elim _ _
        rw [hf]
        simp
      · intro hx
        have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨0, by simp⟩
    have hDenseZero2 : Dense ({0} : Set (LittleHolder
        P.finiteChartCover 2 α P.normedDataC2)) := by
      simpa [hRange2] using hDense2
    have hZero2 : ∀ u : LittleHolder P.finiteChartCover 2 α P.normedDataC2, u = 0 := by
      intro u
      have hu : u ∈ closure ({0} : Set (LittleHolder
          P.finiteChartCover 2 α P.normedDataC2)) := by
        rw [hDenseZero2.closure_eq]
        exact Set.mem_univ u
      have hu' : u ∈ ({0} : Set (LittleHolder
          P.finiteChartCover 2 α P.normedDataC2)) := by
        rwa [isClosed_singleton.closure_eq] at hu
      exact Set.mem_singleton_iff.mp hu'
    have hDense0 : Dense (Set.range fun f : SmoothChartHolderCore P.finiteChartCover 0 α =>
        (f : LittleHolder P.finiteChartCover 0 α P.normedDataC0)) :=
      UniformSpace.Completion.denseRange_coe
    have hRange0 : Set.range (fun f : SmoothChartHolderCore P.finiteChartCover 0 α =>
        (f : LittleHolder P.finiteChartCover 0 α P.normedDataC0)) = {0} := by
      ext x
      constructor
      · rintro ⟨f, rfl⟩
        have hf : f = 0 := Subsingleton.elim _ _
        rw [hf]
        simp
      · intro hx
        have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨0, by simp⟩
    have hDenseZero0 : Dense ({0} : Set (LittleHolder
        P.finiteChartCover 0 α P.normedDataC0)) := by
      simpa [hRange0] using hDense0
    have hZero0 : ∀ u : LittleHolder P.finiteChartCover 0 α P.normedDataC0, u = 0 := by
      intro u
      have hu : u ∈ closure ({0} : Set (LittleHolder
          P.finiteChartCover 0 α P.normedDataC0)) := by
        rw [hDenseZero0.closure_eq]
        exact Set.mem_univ u
      have hu' : u ∈ ({0} : Set (LittleHolder
          P.finiteChartCover 0 α P.normedDataC0)) := by
        rwa [isClosed_singleton.closure_eq] at hu
      exact Set.mem_singleton_iff.mp hu'
    have : Subsingleton (LittleHolder P.finiteChartCover 2 α P.normedDataC2) :=
      ⟨fun u v ↦ by rw [hZero2 u, hZero2 v]⟩
    have : Subsingleton (LittleHolder P.finiteChartCover 0 α P.normedDataC0) :=
      ⟨fun u v ↦ by rw [hZero0 u, hZero0 v]⟩
    have : Subsingleton P.C2 := by
      exact ⟨fun u v ↦ Subtype.ext (Subsingleton.elim _ _)⟩
    have : Subsingleton P.C0 := by
      exact ⟨fun u v ↦ Subtype.ext (Subsingleton.elim _ _)⟩
    let L : P.C2 ≃L[ℝ] P.C0 := {
      toLinearEquiv := {
        toFun := fun _ ↦ 0
        invFun := fun _ ↦ 0
        left_inv := fun _ ↦ Subsingleton.elim _ _
        right_inv := fun _ ↦ Subsingleton.elim _ _
        map_add' := fun _ _ ↦ Subsingleton.elim _ _
        map_smul' := fun _ _ ↦ Subsingleton.elim _ _
      }
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const
    }
    refine ⟨L, ?_⟩
    intro u
    funext x
    exact (hM.false x).elim
  · let : Nonempty M := not_isEmpty_iff.mp hM
    have hvol : 0 < ω₁.volume.real Set.univ := by
      have hint : Integrable (fun x : M ↦ Real.exp ((0 : ℝ) : ℝ)) ω₁.volume := by
        simp
      simp
    have hGlobal := exists_global_meanZero_laplacian_holder_bound
      ω₁ P.finiteChartCover α hα₀ hα₁ hSch
    have hForward := exists_forward_laplacian_holder_bound
      ω₁ P.finiteChartCover α hα₁
    have hPoissonInverse := exists_bounded_smooth_meanZero_poisson_inverse
      ω₁ P.finiteChartCover α hPoisson hGlobal
    have hEvalC2CLM := littleHolderMeanZeroEvaluationC2CLM_injective
      ω₁ P.finiteChartCover α P.normedDataC2
    have hEvalC0CLM := littleHolderMeanZeroEvaluationC0CLM_injective
      ω₁ P.finiteChartCover α P.normedDataC0
    have hEvalC2 : Function.Injective P.evalC2 := by
      intro u v huv
      apply hEvalC2CLM
      ext x
      exact congrFun huv x
    have hEvalC0 : Function.Injective P.evalC0 := by
      intro u v huv
      apply hEvalC0CLM
      ext x
      exact congrFun huv x
    obtain ⟨A, hAeval⟩ := exists_completed_forward_laplacian
      ω₁ α hForward hvol
    obtain ⟨B, hBA, hAB⟩ := exists_completed_poisson_inverse_laws
      ω₁ α hEvalC2 hEvalC0 hPoissonInverse A hAeval hSmoothDense hvol
    let e : P.C2 ≃ₗ[ℝ] P.C0 := {
      toFun := A
      invFun := B
      left_inv := hBA
      right_inv := hAB
      map_add' := A.map_add
      map_smul' := A.map_smul
    }
    let L : P.C2 ≃L[ℝ] P.C0 := {
      toLinearEquiv := e
      continuous_toFun := A.continuous
      continuous_invFun := B.continuous
    }
    refine ⟨L, ?_⟩
    intro u
    change P.evalC0 (A u) = ω₁.laplacian (P.evalC2 u)
    exact hAeval u

end KahlerForm
