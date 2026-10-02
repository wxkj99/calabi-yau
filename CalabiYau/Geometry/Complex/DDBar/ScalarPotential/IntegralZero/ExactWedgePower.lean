module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.Stokes
public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge.WedgePowers

/-!
# Exactness of the primitive square times a closed two-form power

For `2 ≤ n`, `γ = dβ` and `dω = 0` give
`d(β ∧ (γ ∧ ωⁿ⁻²)) = γ ∧ (γ ∧ ωⁿ⁻²)`.
The field powers are exactly the published continuous alternating-map powers,
including their degree-zero scalar unit. All casts preserve the ordered slots.
The degree-one minus term vanishes because `dγ = dω = 0`.

Source: Bott–Tu, *Differential Forms in Algebraic Topology*, Chapter I §1,
Proposition 1.3; Wells, *Differential Analysis on Complex Manifolds*, IV §5.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace FormField

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M]

private theorem smooth_cast {k l : ℕ} (h : k = l)
    {α : FormField (EuclideanSpace ℂ (Fin n)) M k} (hα : α.IsSmooth) :
    (cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) α).IsSmooth := by
  cases h
  exact hα

private theorem cast_extDeriv {k l : ℕ} (h : k = l)
    (α : FormField (EuclideanSpace ℂ (Fin n)) M k) :
    (cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) α).extDeriv =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (congrArg (fun r => r + 1) h)) α.extDeriv := by
  cases h
  rfl

private theorem closed_cast {k l : ℕ} (h : k = l)
    {α : FormField (EuclideanSpace ℂ (Fin n)) M k} (hα : α.IsClosed) :
    (cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) α).IsClosed := by
  cases h
  exact hα

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] in
private theorem cast_zero {k l : ℕ} (h : k = l) :
    cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h)
      (0 : FormField (EuclideanSpace ℂ (Fin n)) M k) = 0 := by
  cases h
  rfl

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] in
private theorem wedge_zero_left {k l : ℕ}
    (β : FormField (EuclideanSpace ℂ (Fin n)) M l) :
    wedge (0 : FormField (EuclideanSpace ℂ (Fin n)) M k) β = 0 := by
  have h := smul_wedge (0 : ℝ) (0 : FormField (EuclideanSpace ℂ (Fin n)) M k) β
  simpa only [zero_smul] using h

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] in
private theorem wedge_zero_right {k l : ℕ}
    (α : FormField (EuclideanSpace ℂ (Fin n)) M k) :
    wedge α (0 : FormField (EuclideanSpace ℂ (Fin n)) M l) = 0 := by
  have h := wedge_smul (0 : ℝ) α (0 : FormField (EuclideanSpace ℂ (Fin n)) M l)
  simpa only [zero_smul] using h

private theorem closed_wedge {k l : ℕ}
    {α : FormField (EuclideanSpace ℂ (Fin n)) M k}
    {β : FormField (EuclideanSpace ℂ (Fin n)) M l}
    (hα : α.IsSmooth) (hβ : β.IsSmooth) (hαc : α.IsClosed) (hβc : β.IsClosed) :
    (wedge α β).IsClosed := by
  change (wedge α β).extDeriv = 0
  rw [extDeriv_wedge hα hβ]
  unfold derivWedgeLeft derivWedgeRight
  rw [hαc, hβc, wedge_zero_left, wedge_zero_right,
    cast_zero (Nat.add_right_comm k 1 l), cast_zero (Nat.add_assoc k l 1).symm]
  simp

private theorem exact_wedge_closed {l : ℕ}
    {γ : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    {ζ : FormField (EuclideanSpace ℂ (Fin n)) M l}
    (hγ : γ.IsExact) (hζ : ζ.IsSmooth) (hζc : ζ.IsClosed) :
    ∃ θ : FormField (EuclideanSpace ℂ (Fin n)) M (1 + l), θ.IsSmooth ∧
      θ.extDeriv = cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (Nat.add_right_comm 1 1 l)) (wedge γ ζ) := by
  obtain ⟨β, hβ, hdβ⟩ := hγ
  refine ⟨wedge β ζ, hβ.wedge hζ, ?_⟩
  rw [extDeriv_wedge hβ hζ]
  unfold derivWedgeLeft derivWedgeRight
  rw [hdβ, hζc, wedge_zero_right, cast_zero (Nat.add_assoc 1 l 1).symm]
  simp

/-- Fieldwise raw powers of a two-form, using the existing fiber powers without
any new normalization or factorial. -/
noncomputable def wedgePow (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) (k : ℕ) :
    FormField (EuclideanSpace ℂ (Fin n)) M (2 * k) :=
  fun x => ContinuousAlternatingMap.wedgePow (α x) k

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] in
/-- The field power is exactly the published continuous alternating-map power. -/
theorem wedgePow_apply (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) (k : ℕ) (x : M) :
    FormField.wedgePow α k x = ContinuousAlternatingMap.wedgePow (α x) k := rfl

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] in
private theorem wedgePow_succ (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) (k : ℕ) :
    FormField.wedgePow α (k + 1) = cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
      (by omega : 2 + 2 * k = 2 * (k + 1))) (wedge α (FormField.wedgePow α k)) := by
  have hcast {a b : ℕ} (h : a = b)
      (β : FormField (EuclideanSpace ℂ (Fin n)) M a) (x : M) :
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) β x =
        (β x).domDomCongr (Fin.castOrderIso h) := by
    cases h
    ext v
    rfl
  funext x
  rw [hcast]
  rfl

/-- Smooth two-forms have smooth raw wedge powers, including the scalar unit. -/
theorem IsSmooth.wedgePow {α : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hα : α.IsSmooth) (k : ℕ) : (FormField.wedgePow α k).IsSmooth := by
  induction k with
  | zero =>
    intro x
    have hrep : (FormField.wedgePow α 0).chartRep x =
        fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin n))
          (Fin 0) 1 := by
      funext z
      exact CalabiYau.DifferentialForm.constOfIsEmpty_compContinuousLinearMap 1 _
    rw [hrep]
    exact contDiffOn_const
  | succ k ih =>
    rw [wedgePow_succ]
    exact smooth_cast (by omega : 2 + 2 * k = 2 * (k + 1)) (hα.wedge ih)

/-- Powers of a smooth closed two-form are closed. -/
theorem IsClosed.wedgePow {α : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hαc : α.IsClosed) (hα : α.IsSmooth) (k : ℕ) : (FormField.wedgePow α k).IsClosed := by
  induction k with
  | zero =>
    change (FormField.wedgePow α 0).extDeriv = 0
    funext x
    have hrep : (FormField.wedgePow α 0).chartRep x =
        fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin n))
          (Fin 0) 1 := by
      funext z
      exact CalabiYau.DifferentialForm.constOfIsEmpty_compContinuousLinearMap 1 _
    change _root_.extDeriv ((FormField.wedgePow α 0).chartRep x) _ = 0
    rw [hrep, _root_.extDeriv, fderiv_const_apply]
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM
      (n := 0) ℝ (EuclideanSpace ℂ (Fin n)) ℝ).map_zero
  | succ k ih =>
    rw [wedgePow_succ]
    exact closed_cast (by omega : 2 + 2 * k = 2 * (k + 1))
      (closed_wedge hα (hα.wedgePow k) hαc ih)

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] in
private theorem cast_cast {k l r : ℕ} (h : k = l) (h' : l = r)
    (α : FormField (EuclideanSpace ℂ (Fin n)) M k) :
    cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h')
      (cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) α) =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) (h.trans h')) α := by
  cases h
  cases h'
  rfl

/-- The square of a smooth exact real two-form times a smooth closed background
power has a smooth real degree-`2n-1` primitive. The dimension restriction is
explicit, and no primitivity, Hodge–Riemann, or vanishing assumption is used. -/
theorem exists_primitive_wedge_sq_wedgePow (hn : 2 ≤ n)
    (ω₀ γ : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hω : ω₀.IsSmooth) (hωc : ω₀.IsClosed) (hγ : γ.IsSmooth) (hγe : γ.IsExact) :
    ∃ θ : FormField (EuclideanSpace ℂ (Fin n)) M (2 * n - 1), θ.IsSmooth ∧
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : (2 * n - 1) + 1 = 2 * n)) θ.extDeriv =
        cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
          (by omega : 2 + (2 + 2 * (n - 2)) = 2 * n))
          (wedge γ (wedge γ (wedgePow ω₀ (n - 2)))) := by
  let ζ := wedge γ (wedgePow ω₀ (n - 2))
  have hζ : ζ.IsSmooth := hγ.wedge (hω.wedgePow (n - 2))
  have hζc : ζ.IsClosed := closed_wedge hγ (hω.wedgePow (n - 2)) hγe.isClosed
    (hωc.wedgePow hω (n - 2))
  obtain ⟨η, hη, hdη⟩ := exact_wedge_closed hγe hζ hζc
  let hdegree : 1 + (2 + 2 * (n - 2)) = 2 * n - 1 := by omega
  refine ⟨cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) hdegree) η,
    smooth_cast hdegree hη, ?_⟩
  rw [cast_extDeriv hdegree, hdη]
  rw [cast_cast (congrArg (fun r => r + 1) hdegree)
    (by omega : (2 * n - 1) + 1 = 2 * n)]
  rw [cast_cast (Nat.add_right_comm 1 1 (2 + 2 * (n - 2)))
    (by omega : (1 + (2 + 2 * (n - 2))) + 1 = 2 * n)]

end FormField
