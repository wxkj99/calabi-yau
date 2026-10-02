module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.TraceMatrixJets
public import CalabiYau.Mathlib.Geometry.Manifold.Holder

/-!
# Mixed Wirtinger derivatives of a bounded family

A chartwise C³ bound for smooth functions bounds their mixed second derivatives
on any fixed compact chart piece. This is the local analytic input, without any
metric or curvature estimate. Source: Székelyhidi, *An Introduction to Extremal
Kähler Metrics*, §3.3, Lemma 3.10, pp. 45–46. Each Wirtinger derivative has a
factor 1/2; the real two-plane Laplacian has an overall factor 1/4.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

/-- A chartwise C³ bound on a smooth family gives a uniform bound for the
mixed Wirtinger derivatives of its members on a compact piece of a fixed chart.
No positivity of the potential and no comparison of metrics is needed. -/
private theorem refinedTrace_mixedPotentialDerivative_eq_complexHessian
    {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ) {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 2 u z) (i j : Fin n) :
    wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar (fun v ↦ (u v : ℂ)) w j) z i =
      complexHessian u z i j := by
  let ei : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let ej : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ u) z :=
    hu.fderiv_right (m := 1) (by norm_num)
  have hfdDiff : DifferentiableAt ℝ (fderiv ℝ u) z :=
    hfd.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w ej) z :=
    hfdDiff.clm_apply (differentiableAt_const _)
  have hB : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w (Complex.I • ej)) z :=
    hfdDiff.clm_apply (differentiableAt_const _)
  have hAcomplex : DifferentiableAt ℝ (fun w ↦ (fderiv ℝ u w ej : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hA
  have hBcomplex : DifferentiableAt ℝ (fun w ↦
      (fderiv ℝ u w (Complex.I • ej) : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hB
  have hD (v q : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ u w q) z v =
        fderiv ℝ (fderiv ℝ u) z v q := by
    have h := fderiv_clm_apply (u := fun _ : EuclideanSpace ℂ (Fin n) ↦ q)
      hfdDiff (differentiableAt_const _)
    have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L v) h
    simpa using h'
  have hAc (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (fderiv ℝ u w ej : ℂ)) z v =
        (fderiv ℝ (fderiv ℝ u) z v ej : ℂ) := by
    have hcomp := (Complex.ofRealCLM.hasFDerivAt.comp z hA.hasFDerivAt).fderiv
    have heval := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hcomp
    simpa [Function.comp_def, hD v ej] using heval
  have hBc (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (fderiv ℝ u w (Complex.I • ej) : ℂ)) z v =
        (fderiv ℝ (fderiv ℝ u) z v (Complex.I • ej) : ℂ) := by
    have hcomp := (Complex.ofRealCLM.hasFDerivAt.comp z hB.hasFDerivAt).fderiv
    have heval := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hcomp
    simpa [Function.comp_def, hD v (Complex.I • ej)] using heval
  have hnum : DifferentiableAt ℝ (fun w ↦
      (fderiv ℝ u w ej : ℂ) + Complex.I * fderiv ℝ u w (Complex.I • ej)) z :=
    hAcomplex.add (hBcomplex.const_mul Complex.I)
  have hbar : (fun w ↦ c3RefinedTracePartialBar
      (fun v ↦ (u v : ℂ)) w j) =ᶠ[nhds z]
      fun w ↦ (2 : ℂ)⁻¹ * ((fderiv ℝ u w ej : ℂ) +
        Complex.I * fderiv ℝ u w (Complex.I • ej)) := by
    have hnear₂ : ∀ᶠ w in nhds z, ContDiffAt ℝ 2 u w := hu.eventually (by norm_num)
    have hnear : ∀ᶠ w in nhds z, ContDiffAt ℝ 1 u w :=
      hnear₂.mono (fun _ hw => hw.of_le (by norm_num))
    filter_upwards [hnear] with w hw
    have hdiff : DifferentiableAt ℝ u w := hw.differentiableAt (by norm_num)
    have hcomp (d : EuclideanSpace ℂ (Fin n)) :
        fderiv ℝ (fun v ↦ (u v : ℂ)) w d = (fderiv ℝ u w d : ℂ) := by
      have h := (Complex.ofRealCLM.hasFDerivAt.comp w hdiff.hasFDerivAt).fderiv
      have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
      simpa [Function.comp_def] using h'
    simp only [c3RefinedTracePartialBar, hcomp, div_eq_mul_inv]
    ring
  have hpartial (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ c3RefinedTracePartialBar
        (fun v ↦ (u v : ℂ)) w j) z v =
        (2 : ℂ)⁻¹ * ((fderiv ℝ (fderiv ℝ u) z v ej : ℂ) +
          Complex.I * fderiv ℝ (fderiv ℝ u) z v (Complex.I • ej) : ℂ) := by
    have hfderiv := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hbar
    have heval := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hfderiv
    rw [heval, fderiv_const_mul hnum (2 : ℂ)⁻¹,
      fderiv_fun_add hAcomplex (hBcomplex.const_mul Complex.I),
      fderiv_const_mul hBcomplex Complex.I]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hAc, hBc]
  unfold wirtingerDerivInChart
  rw [hpartial ei, hpartial (Complex.I • ei)]
  rw [complexHessian_apply hu i j]
  simp only [ei, ej, div_eq_mul_inv]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

omit [T2Space M] [CompactSpace M] in
theorem exists_uniform_c3RefinedTrace_mixedPotentialDerivative_bound
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1)
    (hG : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S))
    (x₀ : M) (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ z ∈ K, ∀ i j : Fin n,
      ‖wirtingerDerivInChart
        (fun w ↦ c3RefinedTracePartialBar
          (fun v ↦ ((p.1 ∘ (extChartAt
            𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) v : ℂ)) w j) z i‖ ≤ C := by
  obtain ⟨C, hC⟩ := hG x₀ K hK hKt
  refine ⟨(C : ℝ), by positivity, ?_⟩
  intro p hp z hz i j
  let ψ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
  let u : EuclideanSpace ℂ (Fin n) → ℝ := p.1 ∘ ψ.symm
  have hzK : z ∈ K := hz
  have hpimg : p.1 ∈ Prod.fst '' S := ⟨p, hp, rfl⟩
  have hOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 Set.univ :=
    (hS p hp).contMDiffOn
  have hsymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ ψ.symm ψ.target :=
    contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀
  have huOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u ψ.target := by
    exact hOn.comp hsymm (by intro w hw; exact Set.mem_univ _)
  have hu : ContDiffAt ℝ 2 u z := by
    have hu' := (huOn.contDiffOn.contDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀).mem_nhds
        (hKt hzK))).of_le (WithTop.coe_le_coe.mpr
          (show (2 : ℕ∞) ≤ ⊤ from le_top))
    exact hu'
  have hbound := hC p.1 hpimg
  have hjet : ‖iteratedFDeriv ℝ 2 u z‖ ≤ (C : ℝ) := by
    have h := hbound.1 2 (by norm_num) z hzK
    simpa [u, ψ] using h
  have hsingle (k : Fin n) : ‖EuclideanSpace.single k (1 : ℂ)‖ = 1 := by
    simp
  have hIsingle (k : Fin n) :
      ‖Complex.I • EuclideanSpace.single k (1 : ℂ)‖ = 1 := by
    rw [norm_smul, Complex.norm_I, hsingle]
    norm_num
  have hD2 (a b : EuclideanSpace ℂ (Fin n)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
      ‖fderiv ℝ (fderiv ℝ u) z a b‖ ≤ (C : ℝ) := by
    let D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) ℝ :=
      iteratedFDeriv ℝ 2 u z
    have htuple : ‖![a, b]‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro k
      fin_cases k
      · simp [ha]
      · simp [hb]
    have hEval := D.le_opNorm_mul_pow_of_le (m := ![a, b]) (b := 1) htuple
    have hDval : ‖D ![a, b]‖ ≤ (C : ℝ) := by
      calc
        ‖D ![a, b]‖ ≤ ‖D‖ * 1 ^ 2 := by simpa using hEval
        _ ≤ (C : ℝ) := by simpa [D] using hjet
    have heq : fderiv ℝ (fderiv ℝ u) z a b = iteratedFDeriv ℝ 2 u z ![a, b] := by
      rw [iteratedFDeriv_two_apply (𝕜 := ℝ) u z ![a, b]]
      rfl
    rw [heq]
    simpa [D] using hDval
  have hAA := hD2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    (hsingle i) (hsingle j)
  have hBB := hD2 (Complex.I • EuclideanSpace.single i 1)
    (Complex.I • EuclideanSpace.single j 1) (hIsingle i) (hIsingle j)
  have hAB := hD2 (EuclideanSpace.single i 1)
    (Complex.I • EuclideanSpace.single j 1) (hsingle i) (hIsingle j)
  have hBA := hD2 (Complex.I • EuclideanSpace.single i 1)
    (EuclideanSpace.single j 1) (hIsingle i) (hsingle j)
  have hhess : ‖complexHessian u z i j‖ ≤ (C : ℝ) := by
    rw [complexHessian_apply hu i j]
    have hA : ‖(fderiv ℝ (fderiv ℝ u) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)‖ ≤ (C : ℝ) := by
      simpa using hAA
    have hB : ‖(fderiv ℝ (fderiv ℝ u) z
        (Complex.I • EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1) : ℂ)‖ ≤
        (C : ℝ) := by simpa using hBB
    have hE : ‖(fderiv ℝ (fderiv ℝ u) z
        (EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1) : ℂ)‖ ≤
        (C : ℝ) := by simpa using hAB
    have hF : ‖(fderiv ℝ (fderiv ℝ u) z
        (Complex.I • EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)‖ ≤
        (C : ℝ) := by simpa using hBA
    have hnum : ‖(fderiv ℝ (fderiv ℝ u) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) +
        fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
          (Complex.I • EuclideanSpace.single j 1) + Complex.I *
        (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single i 1)
          (Complex.I • EuclideanSpace.single j 1) -
          fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1))‖ ≤ 4 * (C : ℝ) := by
      calc
        _ ≤ ‖(fderiv ℝ (fderiv ℝ u) z
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) +
              fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
                (Complex.I • EuclideanSpace.single j 1)‖ +
            ‖Complex.I * (fderiv ℝ (fderiv ℝ u) z
              (EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1) -
              fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
                (EuclideanSpace.single j 1))‖ := norm_add_le _ _
        _ ≤ (‖(fderiv ℝ (fderiv ℝ u) z
                (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)‖ +
              ‖(fderiv ℝ (fderiv ℝ u) z
                (Complex.I • EuclideanSpace.single i 1)
                (Complex.I • EuclideanSpace.single j 1) : ℂ)‖ +
            (‖(fderiv ℝ (fderiv ℝ u) z
                (EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1) : ℂ)‖ +
              ‖(fderiv ℝ (fderiv ℝ u) z
                (Complex.I • EuclideanSpace.single i 1)
                (EuclideanSpace.single j 1) : ℂ)‖)) := by
          have hsub := norm_sub_le
            (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single i 1)
              (Complex.I • EuclideanSpace.single j 1) : ℂ)
            (fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1) : ℂ)
          have hmul : ‖Complex.I * ((fderiv ℝ (fderiv ℝ u) z
              (EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1) : ℂ) -
              fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
                (EuclideanSpace.single j 1))‖ ≤
              ‖(fderiv ℝ (fderiv ℝ u) z
                (EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1) : ℂ)‖ +
              ‖(fderiv ℝ (fderiv ℝ u) z
                (Complex.I • EuclideanSpace.single i 1)
                (EuclideanSpace.single j 1) : ℂ)‖ := by
            rw [norm_mul, Complex.norm_I]
            simpa using hsub
          exact add_le_add (norm_add_le _ _) hmul
        _ ≤ (C : ℝ) + (C : ℝ) + ((C : ℝ) + (C : ℝ)) := by linarith [hA, hB, hE, hF]
        _ = 4 * (C : ℝ) := by ring
    calc
      _ = ‖(fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
            (Complex.I • EuclideanSpace.single j 1) + Complex.I *
          (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single i 1)
            (Complex.I • EuclideanSpace.single j 1) -
            fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1))) / 4‖ := by simp [div_eq_mul_inv]
      _ ≤ (4 * (C : ℝ)) / 4 := by
        rw [norm_div]
        have hdiv := div_le_div_of_nonneg_right hnum (by norm_num : (0 : ℝ) ≤ 4)
        simpa using hdiv
      _ = (C : ℝ) := by ring
  change ‖wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
    (fun v ↦ (u v : ℂ)) w j) z i‖ ≤ (C : ℝ)
  rw [refinedTrace_mixedPotentialDerivative_eq_complexHessian u hu i j]
  simpa [u, ψ] using hhess

end KahlerForm
