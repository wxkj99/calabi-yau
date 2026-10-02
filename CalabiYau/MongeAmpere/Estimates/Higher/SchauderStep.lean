module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Complex.Schauder
import CalabiYau.Geometry.Complex.Forms.Positive
import CalabiYau.MongeAmpere.Estimates.Higher.LinearizedMongeAmpere
import CalabiYau.Mathlib.Analysis.Matrix.Order
import CalabiYau.LinearAlgebra.Hermitian.EigenvalueBound
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.InverseHolder
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.LinearizedContinuation
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.UniformEllipticity

/-!
# One-order local Schauder bootstrap step

Given uniform `C^{r,α}` chart bounds on every compact subset, the Monge–Ampère equation and
interior Schauder theory give `C^{r+1,α}` bounds. The prior Hölder bound controls the inverse
perturbed metric in `C^{r-2,α}`. Differentiate the logarithmic determinant equation once and apply
the local estimate to each first coordinate derivative.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §2.3, Theorem 2.8, p. 28;
§3.3, proof of Proposition 3.11, p. 47; Yau, “On the Ricci curvature of a compact Kähler
manifold and the complex Monge–Ampère equation”, §4.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- One Schauder bootstrap step, uniformly over a family of Monge–Ampère solutions and over
compact chart pieces. -/
theorem exists_uniform_chart_holder_bound_succ (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : ∀ k, HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) k 0 (Prod.fst '' S))
    {K Λ : ℝ} (hφ : ∀ p ∈ S, ∀ x, |p.2 x| ≤ K)
    (hΛ : ∀ p ∈ S, ∀ x, relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ Λ)
    (x : M) (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (r : ℕ) (hr : 2 ≤ r)
    (hCurrent : ∀ K' : Set (EuclideanSpace ℂ (Fin n)), IsCompact K' →
      K' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target →
      ∃ C : ℝ≥0, ∀ p ∈ S,
        HolderBoundOn r α C K' (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm))
    (K' : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K')
    (hKt : K' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ C : ℝ≥0, ∀ p ∈ S,
      HolderBoundOn (r + 1) α C K' (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) := by
  by_cases hSempty : S = ∅
  · subst S
    exact ⟨0, by simp⟩
  · by_cases hn : n = 0
    · subst n
      have hE : Subsingleton (EuclideanSpace ℂ (Fin 0)) := by infer_instance
      have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSempty
      obtain ⟨p₀, hp₀⟩ := hSne
      have hKnonneg : 0 ≤ K := (abs_nonneg (p₀.2 x)).trans (hφ p₀ hp₀ x)
      let C : ℝ≥0 := ⟨K, hKnonneg⟩
      refine ⟨C, ?_⟩
      intro p hp
      let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin 0)) x
      let f := p.2 ∘ e.symm
      have hconst : f = fun _ : EuclideanSpace ℂ (Fin 0) ↦ p.2 (e.symm 0) := by
        funext z
        exact congrArg (p.2 ∘ e.symm) (hE.elim z 0)
      have hval (z : EuclideanSpace ℂ (Fin 0)) : |f z| ≤ K := hφ p hp (e.symm z)
      change HolderBoundOn (r + 1) α C K' f
      refine ⟨?_, ?_⟩
      · intro j hj z hz
        change ‖iteratedFDeriv ℝ j f z‖ ≤ (C : ℝ)
        by_cases hj0 : j = 0
        · subst j
          calc
            ‖iteratedFDeriv ℝ 0 f z‖ = |f z| := by simp
            _ ≤ K := hval z
            _ = (C : ℝ) := rfl
        · rw [hconst]
          have hderiv : iteratedFDeriv ℝ j
              (fun _ : EuclideanSpace ℂ (Fin 0) ↦ p.2 (e.symm 0)) = 0 :=
            iteratedFDeriv_const_of_ne hj0 _
          rw [hderiv]
          simp
      · change HolderOnWith C α (iteratedFDeriv ℝ (r + 1) f) K'
        intro z hz w hw
        have hderiv : iteratedFDeriv ℝ (r + 1) f = 0 := by
          rw [hconst]
          exact iteratedFDeriv_const_of_ne (by omega) _
        simp [hderiv]
    · by_cases hKempty : K' = ∅
      · subst K'
        refine ⟨0, ?_⟩
        intro p hp
        refine ⟨?_, ?_⟩
        · intro j hj z hz
          exact hz.elim
        · exact holderOnWith_empty 0 α _
      · have hKne : K'.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
        obtain ⟨ρ, hρ, hρtarget⟩ :=
          hK.exists_thickening_subset_open (isOpen_extChartAt_target x) hKt
        let δ : ℝ := ρ / 2
        let δouter : ℝ := 3 * ρ / 4
        let U : Set (EuclideanSpace ℂ (Fin n)) := Metric.thickening δ K'
        let L : Set (EuclideanSpace ℂ (Fin n)) := closure (Metric.thickening δouter K')
        have hδ : 0 < δ := by dsimp [δ]; linarith
        have hδouter : δ < δouter := by dsimp [δ, δouter]; linarith
        have hδouterρ : δouter < ρ := by dsimp [δouter]; linarith
        have hδρ : δ < ρ := by dsimp [δ]; linarith
        have hUopen : IsOpen U := by dsimp [U]; exact Metric.isOpen_thickening
        have hKU : K' ⊆ U := by
          dsimp [U]
          exact Metric.self_subset_thickening hδ K'
        have hUtarget : closure U ⊆
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
          calc
            closure U ⊆ Metric.cthickening δ K' := by
              dsimp [U]
              exact Metric.closure_thickening_subset_cthickening δ K'
            _ ⊆ Metric.thickening ρ K' :=
              Metric.cthickening_subset_thickening' hρ hδρ K'
            _ ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := hρtarget
        have hUcompact : IsCompact (closure U) := by
          apply (hK.cthickening (r := δ)).of_isClosed_subset isClosed_closure
          exact Metric.closure_thickening_subset_cthickening δ K'
        have hLcompact : IsCompact L := by
          apply (hK.cthickening (r := δouter)).of_isClosed_subset isClosed_closure
          exact Metric.closure_thickening_subset_cthickening δouter K'
        have hLtarget : L ⊆
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
          calc
            L ⊆ Metric.cthickening δouter K' :=
              Metric.closure_thickening_subset_cthickening δouter K'
            _ ⊆ Metric.thickening ρ K' :=
              Metric.cthickening_subset_thickening' hρ hδouterρ K'
            _ ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := hρtarget
        have hBuffer : closure U ⊆ interior L := by
          calc
            closure U ⊆ Metric.cthickening δ K' :=
              Metric.closure_thickening_subset_cthickening δ K'
            _ ⊆ Metric.thickening δouter K' :=
              Metric.cthickening_subset_thickening' (lt_trans hδ hδouter) hδouter K'
            _ ⊆ interior L :=
              interior_maximal subset_closure Metric.isOpen_thickening
        let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
        have hTraceContinuous :
            ContinuousOn (fun z ↦ RCLike.re ((ω₀.metricInChart x z).trace)) (closure U) := by
          have hsum : ContinuousOn
              (fun z ↦ ∑ i : Fin n, Complex.re (ω₀.metricInChart x z i i)) (closure U) := by
            apply continuousOn_finsetSum Finset.univ
            intro i hi
            exact Complex.continuous_re.continuousOn.comp
              (((ω₀.contDiffOn_metricInChart x i i).continuousOn).mono hUtarget)
              (fun _ _ ↦ Set.mem_univ _)
          have hEq : ∀ z, RCLike.re ((ω₀.metricInChart x z).trace) =
              ∑ i : Fin n, Complex.re (ω₀.metricInChart x z i i) := by
            intro z
            simp [Matrix.trace]
          exact hsum.congr (fun z _ ↦ hEq z)
        obtain ⟨Tref, hTref⟩ := hUcompact.exists_bound_of_continuousOn hTraceContinuous
        let Cref : ℝ := max 1 Tref
        have hCref : 0 < Cref := by dsimp [Cref]; positivity
        obtain ⟨Cφ, hCφOuter⟩ := hCurrent L hLcompact hLtarget
        have hCφ : ∀ p ∈ S,
            HolderBoundOn r α Cφ (closure U) (p.2 ∘
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) := by
          intro p hp
          exact (hCφOuter p hp).mono_set (hBuffer.trans interior_subset)
        obtain ⟨CG, hCG⟩ := hG (r + 2) x L hLcompact hLtarget
        have hGouter (p : (M → ℝ) × (M → ℝ)) (hp : p ∈ S) :
            HolderBoundOn (r + 2) 0 CG L (p.1 ∘ e.symm) :=
          hCG p.1 (Set.mem_image_of_mem Prod.fst hp)
        have hGlocal (p : (M → ℝ) × (M → ℝ)) (hp : p ∈ S) :
            HolderBoundOn (r + 2) 0 CG (closure U) (p.1 ∘ e.symm) :=
          (hGouter p hp).mono_set (hBuffer.trans interior_subset)
        have hLinearized : ∀ p ∈ S, ∀ z ∈ U, ∀ v : EuclideanSpace ℂ (Fin n),
            complexEllipticOp (fun _ ↦
              (ω₀.metricInChart x z +
                complexHessian (p.2 ∘ e.symm) z)⁻¹)
              (fun u ↦ fderiv ℝ (p.2 ∘ e.symm) u v) z =
            fderiv ℝ (p.1 ∘ e.symm) z v -
              RCLike.re (((ω₀.metricInChart x z +
                complexHessian (p.2 ∘ e.symm) z)⁻¹ *
                  (Matrix.of fun j k ↦
                    fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v)).trace) +
              RCLike.re ((ω₀.metricInChart x z)⁻¹ *
                (Matrix.of fun j k ↦
                  fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v)).trace := by
          intro p hp z hz v
          exact complexEllipticOp_eq_fderiv_chart_G ω₀ (hS p hp).1
            (hS p hp).2.1.1 (hS p hp).2 x (hUtarget (subset_closure hz))
        obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr hSempty
        let : NeZero n := ⟨hn⟩
        have hΛpos : 0 < Λ := by
          have hPos := ((hS p₀ hp₀).2.1.2 x)
          exact (relTrace_pos (ω₀.isPositive x) hPos).trans_le (hΛ p₀ hp₀ x)
        have hTraceBound : ∀ z ∈ closure U,
            RCLike.re ((ω₀.metricInChart x z).trace) ≤ Cref := by
          intro z hz
          calc
            RCLike.re ((ω₀.metricInChart x z).trace) ≤
                |RCLike.re ((ω₀.metricInChart x z).trace)| := le_abs_self _
            _ = ‖RCLike.re ((ω₀.metricInChart x z).trace)‖ := by simp [Real.norm_eq_abs]
            _ ≤ Tref := hTref z hz
            _ ≤ Cref := le_max_right _ _
        obtain ⟨lam, hlam, hUniformElliptic⟩ := exists_uniform_inverse_metric_ellipticity
          ω₀ S hS hΛpos hCref hΛ hUtarget hTraceBound
        exact KahlerForm.exists_uniform_chart_holder_bound_succ_of_linearized
          hSch ω₀ S hS hα₀ hα₁ hr hUopen hUcompact hUtarget
          hLcompact hBuffer hLtarget hCφOuter hCφ hGouter hGlocal
          K' hK hKU lam hlam hUniformElliptic hLinearized

end KahlerForm
