module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderNorm
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Passing the complex Laplacian to a C² jet limit

GT, Lemma 6.36, p. 136, in the fixed Kähler-coordinate convention. The C² chart formula
is used for the limit; smoothness of the limit is not assumed. At each point the second jet
is contracted with a fixed inverse metric, a continuous finite-dimensional linear operation.
The finite order-zero gauge tending to zero then identifies the Laplacian limit as zero.
-/

set_option autoImplicit false

@[expose] public section

open Filter
open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

/-- Only pointwise convergence of the second jets is needed for passing `Δ` to the limit.
Uniform convergence of derivatives from compactness supplies this hypothesis. Finiteness of
the order-zero gauges is explicit, since `toReal ⊤ = 0` would otherwise invalidate the argument.
No interchange of `Δ` with a merely C⁰ limit occurs. -/
theorem laplacian_eq_zero_of_second_jet_limit
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M]
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (u : ℕ → M → ℝ) (s : ℕ → ℕ) (hs : StrictMono s)
    (hu : ∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (u j))
    (f : M → ℝ)
    (hformula : ∀ i : cover.ι, ∀ z ∈ cover.piece i,
      ω₁.laplacian f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z) =
        RCLike.re ((ω₁.metricInChart (cover.base i) z)⁻¹ *
          complexHessian (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (cover.base i)).symm) z).trace)
    (hjets : ∀ i : cover.ι, ∀ z ∈ cover.piece i, Tendsto
      (fun j => iteratedFDeriv ℝ 2
        (u (s j) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z)
      atTop (𝓝 (iteratedFDeriv ℝ 2
        (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z)))
    (hfinite : ∀ j, finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j)) < ⊤)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j, N ≤ j →
      (finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j))).toReal < ε) :
    ω₁.laplacian f = 0 := by
  classical
  let E := EuclideanSpace ℂ (Fin n)
  let J : E →L[ℝ] E := EuclideanSpace.complexStructure n
  have hJapply (v : E) : J v = Complex.I • v := by
    change (Complex.I • ContinuousLinearMap.id ℝ E) v = _
    simp
  have hJ2 (v : E) : J (J v) = -v := by
    calc
      J (J v) = Complex.I • (Complex.I • v) := by rw [hJapply, hJapply]
      _ = -v := by rw [smul_smul, Complex.I_mul_I]; simp
  let JEquiv : E ≃L[ℝ] E := {
    toLinearEquiv := {
      toFun := J
      invFun := -J
      left_inv := by
        intro v
        change -(J (J v)) = v
        rw [hJ2]
        exact neg_neg v
      right_inv := by
        intro v
        change J (-(J v)) = v
        rw [J.map_neg, hJ2]
        exact neg_neg v
      map_add' := J.map_add
      map_smul' := J.map_smul }
    continuous_toFun := J.continuous
    continuous_invFun := (-J).continuous }
  let oneFormEquiv : (E →L[ℝ] ℝ) ≃L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) :=
    (JEquiv.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans
      (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).toContinuousLinearEquiv
  have hOneForm {g : E → ℝ} :
      (fun z => ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
        ((fderiv ℝ g z).comp J)) = oneFormEquiv ∘ (fun z => fderiv ℝ g z) := by
    funext z
    change ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
        ((fderiv ℝ g z).comp J) =
      (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1))
        ((fderiv ℝ g z).comp J)
    rfl
  let H : (E [×2]→L[ℝ] ℝ) → Matrix (Fin n) (Fin n) ℂ := fun T =>
    Matrix.of fun j k =>
      ((((T ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ) : ℂ) +
        ((T ![Complex.I • EuclideanSpace.single k 1, Complex.I • EuclideanSpace.single j 1] : ℝ) : ℂ) +
        Complex.I * (((T ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ) -
          ((T ![EuclideanSpace.single k 1, Complex.I • EuclideanSpace.single j 1] : ℝ) : ℂ)))) / 4
  have hddbarApply {g : E → ℝ} {x : E}
      (hD : DifferentiableAt ℝ (fderiv ℝ g) x) (a b : E) :
      ddbar g x ![a, b] =
        (fderiv ℝ (fderiv ℝ g) x b (J a) - fderiv ℝ (fderiv ℝ g) x a (J b)) / 2 := by
    let Ω := fun w => ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
      ((fderiv ℝ g w).comp J)
    have hΩ : DifferentiableAt ℝ Ω x := by
      rw [show Ω = oneFormEquiv ∘ (fun w => fderiv ℝ g w) from hOneForm]
      exact oneFormEquiv.differentiableAt.comp x hD
    have hEvalFderiv (b : Fin 1 → E) (a : E) :
        fderiv ℝ (fun w => Ω w b) x a = fderiv ℝ (fderiv ℝ g) x a (J (b 0)) := by
      have hEval : (fun w => Ω w b) = fun w => fderiv ℝ g w (J (b 0)) := by
        funext w
        simp [Ω, J, EuclideanSpace.complexStructure]
      rw [hEval, fderiv_clm_apply hD (differentiableAt_const _)]
      simp
    change (-(1 / 2 : ℝ) • extDeriv Ω x) ![a, b] = _
    rw [ContinuousAlternatingMap.smul_apply, extDeriv_apply hΩ]
    simp only [Fin.removeNth, hEvalFderiv]
    simp [J, EuclideanSpace.complexStructure]
    ring_nf
  have hcomplexHessian {g : E → ℝ} {x : E} :
      complexHessian g x = H (iteratedFDeriv ℝ 2 g x) := by
    let D := fun w => fderiv ℝ g w
    let Ω := fun w => ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
      ((fderiv ℝ g w).comp J)
    have hΩeq : Ω = oneFormEquiv ∘ D := by
      simpa [D, Ω] using (hOneForm (g := g))
    by_cases hD : DifferentiableAt ℝ D x
    · ext j k
      simp only [complexHessian, ContinuousAlternatingMap.coeffMatrix, Matrix.of_apply]
      rw [hddbarApply hD (EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1)]
      rw [hddbarApply hD (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)]
      simp only [H, Matrix.of_apply, iteratedFDeriv_two_apply, hJapply]
      simp [smul_smul, Complex.I_mul_I]
      ring_nf
    · have hΩnot : ¬ DifferentiableAt ℝ Ω x := by
        intro hΩd
        have hD' : DifferentiableAt ℝ D x := by
          apply oneFormEquiv.comp_differentiableAt_iff.mp
          simpa [hΩeq] using hΩd
        exact hD hD'
      have hDzero : fderiv ℝ D x = 0 := fderiv_zero_of_not_differentiableAt hD
      have hΩzero : fderiv ℝ Ω x = 0 := fderiv_zero_of_not_differentiableAt hΩnot
      have hjet : iteratedFDeriv ℝ 2 g x = 0 := by
        ext v
        rw [iteratedFDeriv_two_apply, hDzero]
        rfl
      have hΩext : extDeriv Ω x = 0 := by
        unfold extDeriv
        rw [hΩzero]
        change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ) 0 = 0
        exact map_zero _
      have hddbar : ddbar g x = 0 := by
        change -(1 / 2 : ℝ) • extDeriv Ω x = 0
        rw [hΩext]
        simp
      ext j k
      simp [complexHessian, hddbar, H, hjet]
  let lapOp (G : Matrix (Fin n) (Fin n) ℂ)
      (T : E [×2]→L[ℝ] ℝ) : ℝ := RCLike.re (G⁻¹ * H T).trace
  have hLcont (G : Matrix (Fin n) (Fin n) ℂ) : Continuous (lapOp G) := by
    dsimp [lapOp, H]
    fun_prop
  have hsmallLap (p : M) : Tendsto (fun j => ω₁.laplacian (u (s j)) p) atTop (𝓝 0) := by
    obtain ⟨i, hz⟩ := cover.interior_covers p
    rcases hz with ⟨z, hz, hp⟩
    let ψ := extChartAt 𝓘(ℝ, E) (cover.base i)
    let γ (j : ℕ) := finiteChartHolderGauge cover 0 α (ω₁.laplacian (u (s j)))
    have hzPiece : z ∈ cover.piece i := interior_subset hz
    have hcoord (j : ℕ) : ENNReal.ofReal ‖iteratedFDeriv ℝ 0
        ((ω₁.laplacian (u (s j))) ∘ ψ.symm) z‖ ≤ γ j := by
      have hspatial := CalabiYau.Schauder.spatialJet_le_eContDiffHolderGaugeOn
        0 α (cover.piece i) ((ω₁.laplacian (u (s j))) ∘ ψ.symm)
        (j := 0) (by norm_num) z hzPiece
      change ENNReal.ofReal ‖iteratedFDeriv ℝ 0
        ((ω₁.laplacian (u (s j))) ∘ ψ.symm) z‖ ≤
          ⨆ q, CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α (cover.piece q)
            ((ω₁.laplacian (u (s j))) ∘
              (extChartAt 𝓘(ℝ, E) (cover.base q)).symm)
      exact hspatial.trans (le_iSup (fun q =>
        CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α (cover.piece q)
          ((ω₁.laplacian (u (s j))) ∘ (extChartAt 𝓘(ℝ, E) (cover.base q)).symm)) i)
    have hcoordReal (j : ℕ) : ‖ω₁.laplacian (u (s j)) p‖ ≤ (γ j).toReal := by
      have hreal := ENNReal.toReal_mono (ne_of_lt (hfinite (s j))) (hcoord j)
      rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
      have hreal' : ‖ω₁.laplacian (u (s j)) (ψ.symm z)‖ ≤ (γ j).toReal := by
        simpa [norm_iteratedFDeriv_zero, γ] using hreal
      have hpEq : ψ.symm z = p := by simpa [ψ] using hp
      rw [← hpEq]
      exact hreal'
    have hid (j : ℕ) : j ≤ s j := by
      induction j with
      | zero => omega
      | succ j ih =>
        have hlt : s j < s (Nat.succ j) := hs (Nat.lt_succ_self j)
        exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt hlt)
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hsmall ε hε
    have hTail : ∀ᶠ j : ℕ in atTop, N ≤ j :=
      eventually_atTop.2 ⟨N, fun j hj => hj⟩
    filter_upwards [hTail] with j hj
    rw [dist_eq_norm, sub_zero]
    have hsmall' : (γ j).toReal < ε := by
      simpa [γ] using hN (s j) (le_trans hj (hid j))
    exact (hcoordReal j).trans_lt hsmall'
  funext p
  obtain ⟨i, hz⟩ := cover.interior_covers p
  rcases hz with ⟨z, hz, hp⟩
  let ψ := extChartAt 𝓘(ℝ, E) (cover.base i)
  let p₀ := ψ.symm z
  have hzPiece : z ∈ cover.piece i := interior_subset hz
  have hzTarget : z ∈ ψ.target := cover.piece_in_target i hzPiece
  have hpEq : p₀ = p := by simpa [p₀, ψ] using hp
  have hpSource : p₀ ∈ (chartAt E (cover.base i)).source := by
    simpa only [← extChartAt_source (I := 𝓘(ℝ, E))] using ψ.map_target hzTarget
  have hcoord : ψ p₀ = z := by
    dsimp [p₀]
    exact ψ.right_inv hzTarget
  let G := ω₁.metricInChart (cover.base i) z
  have hformF := hformula i z hzPiece
  rw [hcomplexHessian] at hformF
  have hformF' : ω₁.laplacian f p₀ =
      lapOp G (iteratedFDeriv ℝ 2 (f ∘ ψ.symm) z) := by
    simpa [p₀, ψ, G, lapOp] using hformF
  have hformU (j : ℕ) : ω₁.laplacian (u (s j)) p₀ =
      lapOp G (iteratedFDeriv ℝ 2 (u (s j) ∘ ψ.symm) z) := by
    have h := ω₁.laplacian_eq_inChart (hu (s j)) (cover.base i)
      (y := p₀) hpSource
    rw [hcoord, hcomplexHessian] at h
    simpa [ψ, G, lapOp] using h
  have hseqEq : (fun j => ω₁.laplacian (u (s j)) p₀) =
      fun j => lapOp G (iteratedFDeriv ℝ 2 (u (s j) ∘ ψ.symm) z) := by
    funext j
    exact hformU j
  have hjetConv := hjets i z hzPiece
  have hopConv : Tendsto (fun j => lapOp G (iteratedFDeriv ℝ 2 (u (s j) ∘ ψ.symm) z))
      atTop (𝓝 (lapOp G (iteratedFDeriv ℝ 2 (f ∘ ψ.symm) z))) := by
    exact (hLcont G).continuousAt.tendsto.comp hjetConv
  have hsmallConv := hsmallLap p₀
  rw [hseqEq] at hsmallConv
  have hzero : lapOp G (iteratedFDeriv ℝ 2 (f ∘ ψ.symm) z) = 0 :=
    tendsto_nhds_unique hopConv hsmallConv
  calc
    ω₁.laplacian f p = ω₁.laplacian f p₀ := by rw [hpEq]
    _ = lapOp G (iteratedFDeriv ℝ 2 (f ∘ ψ.symm) z) := hformF'
    _ = 0 := hzero

end KahlerForm
