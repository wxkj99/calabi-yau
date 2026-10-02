-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Bundle/PartialMfderiv/Basic.lean
-- Locally modified.
module
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.VectorField

@[expose] public section


set_option autoImplicit false

open scoped Topology Manifold ContDiff

namespace CalabiYau

noncomputable abbrev vderiv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> 𝕜) (X : (x : M) -> TangentSpace I x) : M -> 𝕜 :=
  fun x => mvfderiv (I := I) f x (X x)

@[simp] theorem vderiv_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> 𝕜) (X : (x : M) -> TangentSpace I x) (x : M) :
    vderiv (I := I) f X x = mvfderiv (I := I) f x (X x) := by
  rfl

theorem mdifferentiableAt_finset_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type*} (t : Finset ι) (f : ι → M → ℝ)
    {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      change MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M ↦ (0 : ℝ)) x
      exact mdifferentiableAt_const (I := I) (I' := 𝓘(ℝ, ℝ))
        (c := (0 : ℝ)) (x := x)
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(ℝ, ℝ) (t.sum f) x := ih hft
      simpa [Finset.sum_insert, hit] using hfi.add hsum

end CalabiYau
