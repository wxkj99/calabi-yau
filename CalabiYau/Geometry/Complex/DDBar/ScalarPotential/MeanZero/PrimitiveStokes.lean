module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.SignedTopFormIntegral
public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge
import CalabiYau.Geometry.Complex.Forms.DifferentialForm
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.IntegralZero.ExactWedgePower
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.NativeStokesConsumption

/-!
# Stokes witness for the mean-zero trace calculation

Székelyhidi, *An Introduction to Extremal Kähler Metrics*, Lemma 1.14:
apply Stokes to `β ∧ ω^(n-1)`, using `dω = 0`. For the Stokes step see
Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 16.11,
pp. 411–414. The native signed integral uses the complex orientation and
volume `ω^n/n!`; it is not the integral of an absolute value.

The witness retains both the mixed-wedge identity and its zero signed integral.
An arbitrary top form with this identity cannot be sent directly to Stokes
without retaining its primitive. The degree cast preserves ordered Fin slots.
There is no connectedness or `(1,1)` assumption on `dβ` at this Stokes step.
For `n = 0` the positive-dimension hypothesis fails: the parent instead uses
its empty-matrix trace identity. For `n = 1` the primitive is `β` itself.
On a flat complex torus this is the integral of `dβ`; for a linear holomorphic
coordinate change both top forms acquire the same positive real determinant.
-/

@[expose] public section

open scoped Manifold ContDiff
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*}

private theorem cast_cast {a b c : ℕ} (h : a = b) (h' : b = c)
    (α : FormField (EuclideanSpace ℂ (Fin n)) M a) :
    cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h')
      (cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) α) =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) (h.trans h')) α := by
  cases h
  cases h'
  rfl

private theorem cast_apply_domDomCongr {k l : ℕ} (h : k = l)
    (α : FormField (EuclideanSpace ℂ (Fin n)) M k) (x : M) :
    cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) α x =
      (α x).domDomCongr (Fin.castOrderIso h) := by
  cases h
  rfl

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem toFormField_cast_degree {k l : ℕ} (h : k = l)
    (θ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M k) :
    (cast (congrArg (CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M) h) θ).toFormField =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) θ.toFormField := by
  cases h
  rfl

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem extDeriv_wedge_eq_left_of_closed_right
    {k l : ℕ} (α : FormField (EuclideanSpace ℂ (Fin n)) M k)
    (β : FormField (EuclideanSpace ℂ (Fin n)) M l)
    (hα : α.IsSmooth) (hβ : β.IsSmooth) (hβc : β.IsClosed) :
    (FormField.wedge α β).extDeriv = FormField.derivWedgeLeft α β := by
  have hβzero : β.extDeriv = 0 := hβc
  have hwedgezero : FormField.wedge α (0 : FormField (EuclideanSpace ℂ (Fin n)) M (l + 1)) = 0 := by
    have h := FormField.wedge_add α (0 : FormField (EuclideanSpace ℂ (Fin n)) M (l + 1)) 0
    have h' : FormField.wedge α (0 : FormField (EuclideanSpace ℂ (Fin n)) M (l + 1)) =
        FormField.wedge α 0 + FormField.wedge α 0 := by simpa using h
    have h'' := congrArg (fun z => z - FormField.wedge α (0 : FormField (EuclideanSpace ℂ (Fin n)) M (l + 1))) h'
    have hzero : (0 : FormField (EuclideanSpace ℂ (Fin n)) M (k + (l + 1))) =
        FormField.wedge α 0 := by simpa using h''
    exact hzero.symm
  rw [FormField.extDeriv_wedge hα hβ]
  delta FormField.derivWedgeRight
  rw [hβzero, hwedgezero]
  simp

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
/-- The mixed wedge of `dβ` has a native top-form witness with zero signed integral. -/
theorem primitiveWedge_has_zero_signedIntegral (hn : 0 < n)
    (ω₀ : KahlerForm n M) (β : FormField (EuclideanSpace ℂ (Fin n)) M 1)
    (hβ : β.IsSmooth) :
    ∃ Θ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n),
      (∀ x, CalabiYau.DifferentialForm.toFormFieldLinearMap Θ x =
        mixedWedgeOfPos hn (β.extDeriv x) (ω₀ x)) ∧
      ω₀.signedTopFormIntegral Θ = 0 := by
  let k : ℕ := 1 + 2 * (n - 1)
  have htop : k + 1 = 2 * n := by omega
  let pow : FormField (EuclideanSpace ℂ (Fin n)) M (2 * (n - 1)) :=
    FormField.wedgePow ω₀.toFormField (n - 1)
  have hpowSmooth : pow.IsSmooth := by
    simpa [pow] using ω₀.isSmooth.wedgePow (n - 1)
  have hpowClosed : pow.IsClosed := by
    exact ω₀.isClosed.wedgePow ω₀.isSmooth (n - 1)
  have hmixed : 2 + 2 * (n - 1) = 2 * n := by omega
  have hcastWedge :
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) htop)
        (FormField.derivWedgeLeft β pow) =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) hmixed)
        (FormField.wedge β.extDeriv pow) := by
    unfold FormField.derivWedgeLeft
    rw [cast_cast (Nat.add_right_comm 1 1 (2 * (n - 1)))
      (by omega : (1 + 2 * (n - 1)) + 1 = 2 * n)]
  let raw : FormField (EuclideanSpace ℂ (Fin n)) M k := FormField.wedge β pow
  have hrawSmooth : raw.IsSmooth := by
    simpa [raw] using hβ.wedge hpowSmooth
  have hrawd : raw.extDeriv = FormField.derivWedgeLeft β pow := by
    simpa [raw] using extDeriv_wedge_eq_left_of_closed_right β pow hβ hpowSmooth hpowClosed
  let ηD : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M k :=
    raw.toDifferentialForm hrawSmooth
  let Θ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n) :=
    cast (congrArg (CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M)
      htop) (CalabiYau.DifferentialForm.exteriorDerivative ηD)
  have hΘ : ∀ x, CalabiYau.DifferentialForm.toFormFieldLinearMap Θ x =
      mixedWedgeOfPos hn (β.extDeriv x) (ω₀ x) := by
    intro x
    change (CalabiYau.DifferentialForm.toFormField Θ) x = _
    dsimp [Θ]
    rw [toFormField_cast_degree htop,
      CalabiYau.DifferentialForm.toFormField_exteriorDerivative,
      CalabiYau.DifferentialForm.toFormField_toDifferentialForm, hrawd, hcastWedge]
    rw [cast_apply_domDomCongr hmixed]
    rw [ContinuousAlternatingMap.mixedWedgeOfPos]
    have hIso : Fin.castOrderIso hmixed =
        Fin.castOrderIso (by omega : 2 + 2 * (n - 1) = 2 * n) := by
      ext i
      rfl
    exact congrArg
      (fun e : Fin (2 + 2 * (n - 1)) ≃o Fin (2 * n) =>
        (β.extDeriv x ∧[ℝ] ContinuousAlternatingMap.wedgePow (ω₀ x) (n - 1)).domDomCongr e.toEquiv)
      hIso
  exact ⟨Θ, hΘ, ω₀.signedTopFormIntegral_cast_exteriorDerivative_eq_zero hn htop ηD⟩

end KahlerForm
