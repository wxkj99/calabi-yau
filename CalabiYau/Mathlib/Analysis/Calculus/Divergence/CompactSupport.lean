module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

@[expose] public section

open MeasureTheory

namespace KahlerForm

variable {n : ℕ}
noncomputable def chartDivergence
    (V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
  LinearMap.trace ℝ (EuclideanSpace ℂ (Fin n)) (fderiv ℝ V z).toLinearMap

/-- The Euclidean product rule for divergence, used after writing a cutoff term as a divergence. -/
theorem chartDivergence_smul
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    (z : EuclideanSpace ℂ (Fin n)) (hu : DifferentiableAt ℝ u z)
    (hV : DifferentiableAt ℝ V z) :
    chartDivergence (fun w ↦ u w • V w) z =
      u z * chartDivergence V z + fderiv ℝ u z (V z) := by
  change LinearMap.trace ℝ (EuclideanSpace ℂ (Fin n))
      (fderiv ℝ (fun w ↦ u w • V w) z).toLinearMap = _
  have hderiv : fderiv ℝ (fun w ↦ u w • V w) z =
      u z • fderiv ℝ V z + (fderiv ℝ u z).smulRight (V z) := by
    exact fderiv_fun_smul hu hV
  rw [hderiv]
  simp [chartDivergence, LinearMap.trace_smulRight, smul_eq_mul]

/-- A compactly supported Euclidean vector field has zero integral divergence.
This is the chart-level Stokes step in the Kähler Green formula. -/
theorem euclidean_integral_divergence_eq_zero
    {V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    (hV : ContDiff ℝ 1 V) (hcompact : HasCompactSupport V) :
    ∫ z, chartDivergence V z ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (EuclideanSpace ℂ (Fin 0)) := by infer_instance
    have hdiv : ∀ z, chartDivergence V z = 0 := by
      intro z
      have hderiv : fderiv ℝ V z = 0 := Subsingleton.elim _ _
      simp [chartDivergence, hderiv]
    simp [hdiv]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let k := n + n - 1
    have hk : k + 1 = n + n := by dsimp [k]; omega
    let eIndex : (Sigma fun _ : Fin n ↦ Fin 2) ≃ Fin (k + 1) :=
      (Equiv.sigmaEquivProd (Fin n) (Fin 2)).trans
        ((finProdFinEquiv (m := n) (n := 2)).trans
          (Equiv.cast (congrArg Fin (show n * 2 = k + 1 by dsimp [k]; omega))))
    let eIso : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (k + 1)) :=
      (Pi.orthonormalBasis (fun _ : Fin n ↦ Complex.orthonormalBasisOneI)).repr.trans
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eIndex)
    let eL : EuclideanSpace ℂ (Fin n) ≃L[ℝ] (Fin (k + 1) → ℝ) :=
      eIso.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin (k + 1)) ℝ)
    have heVol : MeasurePreserving eL
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))
        (MeasureTheory.volume : Measure (Fin (k + 1) → ℝ)) := by
      change MeasurePreserving ((EuclideanSpace.equiv (Fin (k + 1)) ℝ) ∘ eIso)
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))
        (MeasureTheory.volume : Measure (Fin (k + 1) → ℝ))
      exact (PiLp.volume_preserving_ofLp (Fin (k + 1))).comp
        (LinearIsometryEquiv.measurePreserving eIso)
    let : Preorder (EuclideanSpace ℂ (Fin n)) :=
      { le := fun x y ↦ eL x ≤ eL y
        le_refl := fun _ ↦ le_rfl
        le_trans := fun _ _ _ hxy hyz ↦ le_trans hxy hyz }
    let K := eL '' tsupport V
    have hK : IsCompact K := hcompact.image eL.continuous
    obtain ⟨R, hRpos, hR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Fin (k + 1) → ℝ)
    have hcoord (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ tsupport V)
        (i : Fin (k + 1)) : -R < eL z i ∧ eL z i < R := by
      have hzK : eL z ∈ K := ⟨z, hz, rfl⟩
      have hzball := hR hzK
      have hnorm : ‖eL z‖ < R := by
        simpa [Metric.mem_ball] using hzball
      have hi : ‖eL z i‖ ≤ ‖eL z‖ := norm_le_pi_norm (eL z) i
      have habs : |eL z i| < R := by
        simpa [Real.norm_eq_abs] using hi.trans_lt hnorm
      exact abs_lt.mp habs
    let a : EuclideanSpace ℂ (Fin n) := eL.symm fun _ ↦ -R
    let b : EuclideanSpace ℂ (Fin n) := eL.symm fun _ ↦ R
    have hle : a ≤ b := by
      change eL a ≤ eL b
      simp only [a, b, ContinuousLinearEquiv.apply_symm_apply]
      intro i
      exact neg_le_self hRpos.le
    let f : Fin (k + 1) → EuclideanSpace ℂ (Fin n) → ℝ :=
      fun i z ↦ (eL (V z)) i
    let f' : Fin (k + 1) → EuclideanSpace ℂ (Fin n) →
        EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ := fun i z ↦
      (ContinuousLinearMap.proj i).comp
        (eL.toContinuousLinearMap.comp (fderiv ℝ V z))
    have hdiag (g : (Fin (k + 1) → ℝ) →ₗ[ℝ] Fin (k + 1) → ℝ) :
        LinearMap.trace ℝ _ g = ∑ i, g (Pi.single i (1 : ℝ)) i := by
      rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin (k + 1)))]
      simp [Matrix.trace]
    have hDF (z : EuclideanSpace ℂ (Fin n)) :
        chartDivergence V z = ∑ i, f' i z (eL.symm (Pi.single i (1 : ℝ))) := by
      let A := eL.toLinearEquiv.conj (fderiv ℝ V z).toLinearMap
      have hentry (i : Fin (k + 1)) :
          f' i z (eL.symm (Pi.single i (1 : ℝ))) = A (Pi.single i (1 : ℝ)) i := by
        simp [f', A, LinearEquiv.conj_apply, ContinuousLinearMap.comp_apply]
      rw [chartDivergence]
      calc
        _ = LinearMap.trace ℝ _ A := (LinearMap.trace_conj' _ _).symm
        _ = ∑ i, A (Pi.single i (1 : ℝ)) i := hdiag A
        _ = ∑ i, f' i z (eL.symm (Pi.single i (1 : ℝ))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hentry i).symm
    have hVderiv (z : EuclideanSpace ℂ (Fin n)) :
        HasFDerivAt V (fderiv ℝ V z) z :=
      ((hV.contDiffAt (x := z)).differentiableAt (by norm_num)).hasFDerivAt
    have hfCont (i : Fin (k + 1)) : Continuous (f i) := by
      change Continuous (fun z ↦ (eL (V z)) i)
      exact (continuous_apply i).comp (eL.continuous.comp hV.continuous)
    have hC : ∀ i, ContinuousOn (f i) (Set.Icc a b) := fun i ↦ (hfCont i).continuousOn
    have hD (i : Fin (k + 1)) (z : EuclideanSpace ℂ (Fin n)) :
        HasFDerivAt (f i) (f' i z) z := by
      change HasFDerivAt (fun y ↦ (eL (V y)) i) (f' i z) z
      have hcomp : HasFDerivAt (fun y ↦ eL (V y))
          (eL.toContinuousLinearMap.comp (fderiv ℝ V z)) z :=
        eL.toContinuousLinearMap.hasFDerivAt.comp z (hVderiv z)
      exact (ContinuousLinearMap.proj i).hasFDerivAt.comp z hcomp
    have hD' : ∀ z ∈ interior (Set.Icc a b) \ (∅ : Set (EuclideanSpace ℂ (Fin n))),
        ∀ i, HasFDerivAt (f i) (f' i z) z := by
      intro z hz i
      exact hD i z
    have hderivCont : Continuous (fderiv ℝ V) := by
      apply continuous_iff_continuousAt.2
      intro z
      exact (hV.contDiffAt (x := z)).continuousAt_fderiv (by norm_num)
    have hdivCont : Continuous (chartDivergence V) := by
      have hsumFun : chartDivergence V =
          fun z ↦ ∑ i, f' i z (eL.symm (Pi.single i (1 : ℝ))) := funext hDF
      rw [hsumFun]
      exact continuous_finsetSum Finset.univ fun i hi ↦ by
        dsimp [f']
        exact (continuous_apply i).comp
          (eL.continuous.comp (hderivCont.clm_apply continuous_const))
    have hdivZero (z : EuclideanSpace ℂ (Fin n)) (hz : z ∉ tsupport V) :
        chartDivergence V z = 0 := by
      have hloc : V =ᶠ[nhds z] fun _ ↦ (0 : EuclideanSpace ℂ (Fin n)) := by
        filter_upwards [(isClosed_tsupport V).isOpen_compl.mem_nhds hz] with y hy
        by_contra hne
        exact hy (subset_tsupport _ hne)
      have hderiv : fderiv ℝ V z = 0 :=
        (hasFDerivAt_zero_of_eventually_const (0 : EuclideanSpace ℂ (Fin n)) hloc).fderiv
      simp [chartDivergence, hderiv]
    have hdivCompact : HasCompactSupport (chartDivergence V) :=
      HasCompactSupport.intro hcompact (fun z hz ↦ hdivZero z hz)
    have hdivIntegrable : Integrable (chartDivergence V)
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) :=
      hdivCont.integrable_of_hasCompactSupport hdivCompact
    have hI : IntegrableOn (chartDivergence V) (Set.Icc a b)
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := hdivIntegrable.integrableOn
    have hsum := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_of_equiv
      eL (fun _ _ ↦ Iff.rfl) heVol f f' ∅ Set.countable_empty a b hle hC hD'
      (chartDivergence V) hDF hI
    have hVzero (z : EuclideanSpace ℂ (Fin n)) (i : Fin (k + 1))
        (hc : eL z i = R ∨ eL z i = -R) : V z = 0 := by
      by_contra hne
      have hz : z ∈ tsupport V := subset_tsupport _ hne
      rcases hc with hc | hc
      · linarith [(hcoord z hz i).2]
      · linarith [(hcoord z hz i).1]
    have hfrontzero (i : Fin (k + 1)) (y : Fin k → ℝ) :
        f i (eL.symm (i.insertNth (eL b i) y)) = 0 := by
      dsimp [f]
      have hz : V (eL.symm (i.insertNth (eL b i) y)) = 0 := by
        apply hVzero
        have heq : eL (eL.symm (i.insertNth (eL b i) y)) i = eL b i := by
          rw [ContinuousLinearEquiv.apply_symm_apply]
          exact Fin.insertNth_apply_same (α := fun _ : Fin (k + 1) ↦ ℝ)
            i (eL b i) (fun j ↦ y j)
        exact Or.inl (heq.trans (by simp [b]))
      simp [hz]
    have hbackzero (i : Fin (k + 1)) (y : Fin k → ℝ) :
        f i (eL.symm (i.insertNth (eL a i) y)) = 0 := by
      dsimp [f]
      have hz : V (eL.symm (i.insertNth (eL a i) y)) = 0 := by
        apply hVzero
        have heq : eL (eL.symm (i.insertNth (eL a i) y)) i = eL a i := by
          rw [ContinuousLinearEquiv.apply_symm_apply]
          exact Fin.insertNth_apply_same (α := fun _ : Fin (k + 1) ↦ ℝ)
            i (eL a i) (fun j ↦ y j)
        exact Or.inr (heq.trans (by simp [a]))
      simp [hz]
    have hfrontInt (i : Fin (k + 1)) :
        (∫ y in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
          f i (eL.symm (i.insertNth (eL b i) y))) = 0 :=
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun y hy ↦ hfrontzero i y)
    have hbackInt (i : Fin (k + 1)) :
        (∫ y in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
          f i (eL.symm (i.insertNth (eL a i) y))) = 0 :=
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun y hy ↦ hbackzero i y)
    have hbox :
        ∫ z in Set.Icc a b, chartDivergence V z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) = 0 := by
      rw [hsum]
      simp [hfrontInt, hbackInt]
    have hsupportBox : tsupport V ⊆ Set.Icc a b := by
      intro z hz
      change eL a ≤ eL z ∧ eL z ≤ eL b
      constructor
      · intro i
        have hi := (hcoord z hz i).1
        simpa [a] using hi.le
      · intro i
        have hi := (hcoord z hz i).2
        simpa [b] using hi.le
    have hglobal :
        ∫ z, chartDivergence V z ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
        ∫ z in Set.Icc a b, chartDivergence V z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      symm
      apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      apply hdivZero z
      intro hz'
      exact hz (hsupportBox hz')
    rw [hglobal]
    exact hbox

/-- Euclidean integration by parts, reduced to the divergence theorem for the compactly supported
product vector field. -/
theorem euclidean_integration_by_parts
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hV : ContDiff ℝ 1 V)
    (hproduct : ContDiff ℝ 1 fun z ↦ u z • V z)
    (hcompact : HasCompactSupport fun z ↦ u z • V z)
    (hleft : Integrable (fun z ↦ u z * chartDivergence V z)
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))))
    (hright : Integrable (fun z ↦ fderiv ℝ u z (V z))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))) :
    ∫ z, u z * chartDivergence V z ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      -∫ z, fderiv ℝ u z (V z) ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
  have hdiv := euclidean_integral_divergence_eq_zero hproduct hcompact
  have hpoint : (fun z ↦ chartDivergence (fun w ↦ u w • V w) z) =
      fun z ↦ u z * chartDivergence V z + fderiv ℝ u z (V z) := by
    funext z
    exact chartDivergence_smul z
      ((hu.contDiffAt (x := z)).differentiableAt (by norm_num))
      ((hV.contDiffAt (x := z)).differentiableAt (by norm_num))
  rw [hpoint, integral_add hleft hright] at hdiv
  linarith

end KahlerForm
