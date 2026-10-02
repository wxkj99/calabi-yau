module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Basic

/-!
# Zero extension of a form's coordinate representation

Lee, *Introduction to Smooth Manifolds*, 2nd ed., §16, proof of Stokes's theorem:
a form with closed support contained in a chart pulls back to a compactly supported
smooth form on Euclidean space, extended by zero outside the chart. The model
space here is the *standard* coordinate space, not an arbitrary normed space.
-/

@[expose] public section

open Set
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin (n + 1) → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ M]

/-- Coordinate representation on the chart target, extended by zero. The
trivialization is the one used in `exteriorDerivative_localRepresentation`;
thus no determinant or normalization is silently inserted. -/
def stokesChartRepresentation
    (α : DifferentialForm 𝓘(ℝ, Fin (n + 1) → ℝ) M k) (x : M) :
    (Fin (n + 1) → ℝ) →
      (Fin (n + 1) → ℝ) [⋀^Fin k]→L[ℝ] ℝ := by
  classical
  exact fun y => if y ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).target then
    (trivializationAt ((Fin (n + 1) → ℝ) [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) (Fin (n + 1) → ℝ)
        (TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ)) ℝ (Bundle.Trivial M ℝ)) x
      ⟨(extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).symm y,
        α ((extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).symm y)⟩).2 else 0

/-- A closed chart-supported smooth form has a globally C¹, compactly
supported zero-extended coordinate representative. The strict inclusion of
*closed* support inside the open chart is essential at the chart boundary. -/
theorem stokesChartRepresentation_contDiff_hasCompactSupport
    [T2Space M] [CompactSpace M] [BoundarylessManifold 𝓘(ℝ, Fin (n + 1) → ℝ) M]
    (α : DifferentialForm 𝓘(ℝ, Fin (n + 1) → ℝ) M k) (x : M)
    (hα : closure {z : M | α z ≠ 0} ⊆
      (chartAt (Fin (n + 1) → ℝ) x).source) :
    ContDiff ℝ 1 (stokesChartRepresentation α x) ∧
      HasCompactSupport (stokesChartRepresentation α x) := by
  classical
  let I := 𝓘(ℝ, Fin (n + 1) → ℝ)
  let E := Fin (n + 1) → ℝ
  let U := (extChartAt I x).target
  let rep : E → (E [⋀^Fin k]→L[ℝ] ℝ) := fun y =>
    (trivializationAt (E [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace I) ℝ
        (Bundle.Trivial M ℝ)) x
      ⟨(extChartAt I x).symm y, α ((extChartAt I x).symm y)⟩).2
  let K : Set M := closure {z : M | α z ≠ 0}
  have hK : IsCompact K := by
    exact IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (subset_univ _)
  have hKsrc : K ⊆ (extChartAt I x).source := by
    simpa [K, extChartAt_source] using hα
  have himage : IsCompact ((extChartAt I x) '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt x).mono hKsrc)
  have himageU : ((extChartAt I x) '' K) ⊆ U := by
    rintro y ⟨z, hz, rfl⟩
    exact (extChartAt I x).map_source (hKsrc hz)
  have hrepSmooth : ContDiffOn ℝ ∞ rep U := by
    dsimp [rep, U, I, E]
    exact localRep_contDiffOn α x
  have hiff {y : E} (hyt : y ∈ U) :
      rep y ≠ 0 ↔ α ((extChartAt I x).symm y) ≠ 0 := by
    let z := (extChartAt I x).symm y
    let T := trivializationAt (E [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace I) ℝ
          (Bundle.Trivial M ℝ)) x
    have hzsrc : z ∈ (extChartAt I x).source := (extChartAt I x).map_target hyt
    have hbase : z ∈ T.baseSet := by
      change z ∈ (trivializationAt E (TangentSpace I) x).baseSet ∩
        (trivializationAt ℝ (Bundle.Trivial M ℝ) x).baseSet
      exact ⟨by simpa [extChartAt_source] using hzsrc, trivial⟩
    let : Bundle.Trivialization.IsLinear ℝ T := by
      dsimp [T]
      infer_instance
    change (T ⟨z, α z⟩).2 ≠ 0 ↔ α z ≠ 0
    rw [← T.linearEquivAt_apply (R := ℝ) z hbase (α z)]
    exact (T.linearEquivAt (R := ℝ) z hbase).map_ne_zero_iff
  have hnonzero : {y : E | (if y ∈ U then rep y else 0) ≠ 0} ⊆
      (extChartAt I x) '' K := by
    intro y hy
    have hyt : y ∈ U := by
      by_contra hyU
      simp [hyU] at hy
    have hrep : rep y ≠ 0 := by simpa [hyt] using hy
    have hαy : α ((extChartAt I x).symm y) ≠ 0 := (hiff hyt).mp hrep
    refine ⟨(extChartAt I x).symm y, subset_closure hαy, ?_⟩
    exact (extChartAt I x).right_inv hyt
  have hclosure : closure {y : E | (if y ∈ U then rep y else 0) ≠ 0} ⊆
      (extChartAt I x) '' K :=
    closure_minimal hnonzero himage.isClosed
  have hrepSupport : closure {y : E | (if y ∈ U then rep y else 0) ≠ 0} ⊆ U :=
    hclosure.trans himageU
  have hglobal : ContDiff ℝ ∞ (fun y => if y ∈ U then rep y else 0) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hyt : y ∈ U
    · apply (hrepSmooth.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hyt)).congr_of_eventuallyEq
      filter_upwards [(isOpen_extChartAt_target x).mem_nhds hyt] with z hz
      change (if z ∈ U then rep z else 0) = rep z
      exact if_pos hz
    · have hyc : y ∉ closure {z | (if z ∈ U then rep z else 0) ≠ 0} := by
        intro hy
        exact hyt (hrepSupport hy)
      apply (contDiffAt_const (𝕜 := ℝ) (n := (∞ : ℕ∞ω)) (x := y) (c := (0 : E [⋀^Fin k]→L[ℝ] ℝ))).congr_of_eventuallyEq
      have hopen : IsOpen (closure {z | (if z ∈ U then rep z else 0) ≠ 0})ᶜ :=
        isClosed_closure.isOpen_compl
      have hycmem : y ∈ (closure {z | (if z ∈ U then rep z else 0) ≠ 0})ᶜ := by simpa using hyc
      filter_upwards [hopen.mem_nhds hycmem] with z hz
      have hznot : z ∉ closure {w | (if w ∈ U then rep w else 0) ≠ 0} := by simpa using hz
      have hzf : (if z ∈ U then rep z else 0) = 0 := by
        by_contra hne
        exact hznot (subset_closure hne)
      simp [hzf]
  constructor
  · exact hglobal.of_le (by norm_num)
  · change IsCompact (closure {y : E | (if y ∈ U then rep y else 0) ≠ 0})
    exact himage.of_isClosed_subset isClosed_closure hclosure

end CalabiYau.DifferentialForm
