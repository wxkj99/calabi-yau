module

public import CalabiYau.Geometry.Kahler.Laplacian
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Scalar Poisson solutions on connected components

This module assembles genuine smooth scalar solutions on the connected-component open
submanifolds of a compact Hausdorff complex manifold. It is not a global-mean-zero Poisson
solvability theorem: a source on a disconnected manifold must satisfy the solvability condition
on each component separately. It does not prove or import the `∂∂̄` lemma.

The component atlas is the induced open-submanifold atlas. Compactness supplies compact support
for zero-extension of each local solution, and the pointwise component choice is locally one
fixed smooth function. Germ locality of the chart-defined Hessian proves the global equation.
There is no matching condition on additive constants on different components, no finite-sum
normalization, and no factor inserted in the complex Laplacian convention.

Source: the scalar Poisson step in Székelyhidi, *An Introduction to Extremal Kähler Metrics*,
Lemma 1.14, applied separately on components. The assembly uses Mathlib's clopen-component,
induced-open-atlas, germ-locality, and smooth compact-support extension theorems.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set Filter ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]

private theorem ddbar_eq_of_eventuallyEq
    {f g : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (h : f =ᶠ[𝓝 z] g) : ddbar f z = ddbar g z := by
  have hform :
      (fun w => ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
        ((fderiv ℝ f w).comp (EuclideanSpace.complexStructure n))) =ᶠ[𝓝 z]
      (fun w => ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
        ((fderiv ℝ g w).comp (EuclideanSpace.complexStructure n))) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with w hw
    rw [hw]
  unfold ddbar
  rw [hform.extDeriv_eq]

private theorem mddbar_eq_of_eventuallyEq {f g : M → ℝ} {x : M}
    (h : f =ᶠ[𝓝 x] g) : mddbar n f x = mddbar n g x := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hx : e.symm (e x) = x := e.left_inv (mem_extChartAt_source x)
  have he : ContinuousAt e.symm (e x) :=
    continuousAt_extChartAt_symm'' (mem_extChartAt_target x)
  have hchart : (f ∘ e.symm) =ᶠ[𝓝 (e x)] (g ∘ e.symm) := by
    exact he.tendsto.eventually (hx ▸ h)
  exact ddbar_eq_of_eventuallyEq hchart

private theorem mddbar_restrict_open (U : TopologicalSpace.Opens M) (f : M → ℝ) (x : U) :
    mddbar n (fun y : U => f y) x = mddbar n f (x : M) := by
  have hc := U.chartAt_subtype_val_symm_eventuallyEq
    (H := EuclideanSpace ℂ (Fin n)) (x := x)
  have hg :
      (fun y : U => f y) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
      =ᶠ[𝓝 (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M) (x : M))]
      f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M)).symm := by
    simpa only [extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_def, id_eq] using hc.symm.fun_comp f
  have hcenter : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x =
      extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M) (x : M) := rfl
  unfold mddbar
  rw [hcenter]
  exact ddbar_eq_of_eventuallyEq hg

include n in
private theorem component_clopen (c : ConnectedComponents M) :
    IsClopen (ConnectedComponents.mk ⁻¹' ({c} : Set (ConnectedComponents M))) := by
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace
    (EuclideanSpace ℂ (Fin n)) M
  exact (isClopen_discrete {c}).preimage ConnectedComponents.continuous_coe

/-- An actual connected component, with its induced open-submanifold atlas. Openness follows
from the locally path-connected complex Euclidean chart model, not global connectedness. -/
def componentOpen (c : ConnectedComponents M) : TopologicalSpace.Opens M :=
  ⟨ConnectedComponents.mk ⁻¹' {c}, by
    let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℂ (Fin n)) M
    exact (isOpen_discrete {c}).preimage ConnectedComponents.continuous_coe⟩

include n in
private theorem component_compact [CompactSpace M] (c : ConnectedComponents M) :
    CompactSpace (ConnectedComponents.mk ⁻¹' ({c} : Set (ConnectedComponents M))) := by
  exact isCompact_iff_compactSpace.mp (component_clopen (n := n) c).isClosed.isCompact

private theorem extend_compact_open [T2Space M]
    (U : TopologicalSpace.Opens M) [CompactSpace U] (f : U → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (Subtype.val.extend f (fun _ : M => 0)) ∧
    ∀ x : U, Subtype.val.extend f (fun _ : M => 0) x = f x := by
  classical
  refine ⟨hf.extend_zero (HasCompactSupport.of_compactSpace f), ?_⟩
  intro x
  exact Subtype.val_injective.extend_apply f (fun _ : M => 0) x

variable [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem exists_laplacian_eq_of_component_representatives
    (ω₀ : KahlerForm n M) (f : M → ℝ)
    (h : ∀ c : ConnectedComponents M, ∃ u : M → ℝ,
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u
        (ConnectedComponents.mk ⁻¹' {c}) ∧
      ∀ x, ConnectedComponents.mk x = c → ω₀.laplacian u x = f x) :
    ∃ u : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u ∧
      ω₀.laplacian u = f := by
  classical
  choose u hu hΔ using h
  let v : M → ℝ := fun x => u (ConnectedComponents.mk x) x
  have hvlocal (x : M) : v =ᶠ[𝓝 x] u (ConnectedComponents.mk x) := by
    filter_upwards [(component_clopen (n := n) (ConnectedComponents.mk x)).isOpen.mem_nhds
      (show x ∈ ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x} from rfl)] with y hy
    change ConnectedComponents.mk y = ConnectedComponents.mk x at hy
    simp only [v, hy]
  refine ⟨v, ?_, ?_⟩
  · intro x
    have hx := (hu (ConnectedComponents.mk x)).contMDiffAt
      ((component_clopen (n := n) (ConnectedComponents.mk x)).isOpen.mem_nhds
        (show x ∈ ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x} from rfl))
    exact hx.congr_of_eventuallyEq (hvlocal x)
  · funext x
    change relTrace (ω₀ x) (mddbar n v x) = f x
    rw [mddbar_eq_of_eventuallyEq (hvlocal x)]
    exact hΔ (ConnectedComponents.mk x) x rfl

/-- Smooth scalar solutions on the connected-component submanifolds assemble into a smooth
solution of the global complex Poisson equation. The local equation is the trace of the local
`mddbar`, so no restricted Kähler-form construction or unconditional ddbar theorem is assumed. -/
theorem exists_laplacian_eq_of_componentwise [T2Space M] [CompactSpace M]
    (ω₀ : KahlerForm n M) (f : M → ℝ)
    (h : ∀ c : ConnectedComponents M,
      ∃ u : componentOpen (n := n) c → ℝ,
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u ∧
        ∀ x : componentOpen (n := n) c,
          relTrace (ω₀ (x : M)) (mddbar n u x) = f x) :
    ∃ u : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u ∧
      ω₀.laplacian u = f := by
  classical
  choose u hu hEq using h
  apply exists_laplacian_eq_of_component_representatives ω₀ f
  intro c
  let U := componentOpen (n := n) c
  let : CompactSpace U := component_compact (n := n) c
  let v : M → ℝ := Subtype.val.extend (u c) (fun _ => 0)
  obtain ⟨hv, hvEq⟩ := extend_compact_open U (u c) (hu c)
  refine ⟨v, hv.contMDiffOn, ?_⟩
  intro x hx
  let y : U := ⟨x, hx⟩
  have hrestriction : (fun z : U => v z) = u c := by
    funext z
    exact hvEq z
  have hmd := mddbar_restrict_open (n := n) U v y
  rw [hrestriction] at hmd
  change relTrace (ω₀ x) (mddbar n v x) = f x
  rw [← hmd]
  exact hEq c y

end KahlerForm
