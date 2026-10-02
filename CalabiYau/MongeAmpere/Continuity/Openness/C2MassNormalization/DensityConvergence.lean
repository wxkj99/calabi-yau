module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation

/-!
# Uniform convergence of C² Monge–Ampère densities

Uniform convergence of the real chart jets through order two gives uniform convergence of the complex
Hessian matrices.  The chart formula for the relative determinant then gives uniform convergence of
the Monge–Ampère densities, including in complex dimension zero.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

/-- Chartwise C² convergence of smooth positive potentials implies uniform convergence of their
Monge–Ampère densities to that of the limiting C² potential.  The conclusion also records
continuity of the limiting density, so it is integrable on a compact manifold. -/
private theorem continuousOn_complexHessian_of_contDiffOn_two
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℂ (Fin n) → ℝ} (hf : ContDiffOn ℝ 2 f U) :
    ContinuousOn (fun z ↦ complexHessian f z) U := by
  have hfirst : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (by norm_num)
  have hsecond : ContinuousOn (fun z ↦ fderiv ℝ (fderiv ℝ f) z) U :=
    hfirst.continuousOn_fderiv_of_isOpen hU (by norm_num)
  refine continuousOn_pi' ?_
  intro j
  refine continuousOn_pi' ?_
  intro k
  have hformula : ∀ z ∈ U, complexHessian f z j k =
      ((fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) : ℂ) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) +
        Complex.I * (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) -
          fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
            (EuclideanSpace.single k 1))) / 4 := by
    intro z hz
    exact complexHessian_apply (hf.contDiffAt (hU.mem_nhds hz)) j k
  have hcont : ContinuousOn (fun z : EuclideanSpace ℂ (Fin n) =>
      ((fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1) : ℂ) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) +
        Complex.I * (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) -
          fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
            (EuclideanSpace.single k 1))) / 4) U := by
    fun_prop
  exact hcont.congr hformula

omit [T2Space M] [CompactSpace M] in
private theorem continuous_mongeAmpere_of_isC2Potential
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsC2Potential φ) :
    Continuous (ω₀.mongeAmpere φ) := by
  rw [continuous_iff_continuousAt]
  intro x
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let e := extChartAt I x
  let z := e x
  have hφon : ContMDiffOn I 𝓘(ℝ) 2 φ Set.univ := contMDiffOn_univ.mpr hφ.1
  have hφsymm : ContMDiffOn I 𝓘(ℝ) 2 (φ ∘ e.symm) e.target := by
    exact hφon.comp (contMDiffOn_extChartAt_symm x) (by intro w hw; simp)
  have hφchart : ContDiffOn ℝ 2 (φ ∘ e.symm) e.target := hφsymm.contDiffOn
  have hHcont : ContinuousOn (fun w ↦ complexHessian (φ ∘ e.symm) w) e.target :=
    continuousOn_complexHessian_of_contDiffOn_two (isOpen_extChartAt_target x) hφchart
  have hmetricEntry (j k : Fin n) :
      ContDiffOn ℝ ∞ (fun w ↦ ω₀.metricInChart x w j k) e.target :=
    ω₀.contDiffOn_metricInChart x j k
  have hmetric : ContinuousOn (ω₀.metricInChart x) e.target := by
    refine continuousOn_pi' ?_
    intro j
    refine continuousOn_pi' ?_
    intro k
    exact (hmetricEntry j k).continuousOn
  let num : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦
    RCLike.re (ω₀.metricInChart x w + complexHessian (φ ∘ e.symm) w).det
  let den : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦
    RCLike.re (ω₀.metricInChart x w).det
  have hnum : ContinuousOn num e.target := by
    dsimp [num]
    have hmat : ContinuousOn (fun w ↦ ω₀.metricInChart x w +
        complexHessian (φ ∘ e.symm) w) e.target := hmetric.add hHcont
    fun_prop
  have hden : ContinuousOn den e.target := by
    dsimp [den]
    fun_prop
  have hdenpos {w : EuclideanSpace ℂ (Fin n)} (hw : w ∈ e.target) : 0 < den w := by
    dsimp [den]
    exact (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hw).det_pos).1
  have hratio : ContinuousOn (fun w ↦ num w / den w) e.target :=
    hnum.div hden (fun w hw ↦ ne_of_gt (hdenpos hw))
  have hz : z ∈ e.target := mem_extChartAt_target x
  have hzN : e.target ∈ 𝓝 z := (isOpen_extChartAt_target x).mem_nhds hz
  have hratioAt : ContinuousAt (fun w ↦ num w / den w) z := hratio.continuousAt hzN
  have hcomp : ContinuousAt (fun y : M ↦ num (e y) / den (e y)) x :=
    hratioAt.comp (continuousAt_extChartAt (I := I) x)
  have hsourceN : e.source ∈ 𝓝 x :=
    (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
  have heq : (fun y : M ↦ ω₀.mongeAmpere φ y) =ᶠ[𝓝 x]
      (fun y ↦ num (e y) / den (e y)) := by
    filter_upwards [hsourceN] with y hy
    have hyx : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
      rw [← extChartAt_source (I := I)]
      exact hy
    have hlocal := mongeAmpere_eq_inChart_of_contMDiff_two (ω₀ := ω₀) hφ.1 x hyx
    simpa [num, den, e, extChartAt, I, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm] using hlocal
  exact hcomp.congr_of_eventuallyEq heq

omit [T2Space M] [CompactSpace M] in
/-- The determinant-density convergence estimate on one compact chart piece.  Its proof uses the
uniform convergence of the second chart jets and continuity of the finite-dimensional relative
determinant on the bounded chartwise range. -/
private theorem uniform_mongeAmpere_on_compactChartCover_piece
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsC2Potential φ)
    (A : SmoothC2PotentialApproximationData ω₀ φ hφ) (i : A.cover.ι)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ j, N ≤ j → ∀ z ∈ A.cover.piece i,
      |ω₀.mongeAmpere (A.approx j)
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (A.cover.base i)).symm z) -
        ω₀.mongeAmpere φ
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (A.cover.base i)).symm z)| ≤ ε := by
  classical
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  let : FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ) := by
    change FiniteDimensional ℝ (Fin n → Fin n → ℂ)
    infer_instance
  let : ProperSpace (Matrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.proper (𝕜 := ℝ) (Matrix (Fin n) (Fin n) ℂ)
  let : CompactSpace (A.cover.piece i) :=
    isCompact_iff_compactSpace.mp (A.cover.isCompact_piece i)
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let e := extChartAt I (A.cover.base i)
  let g : A.cover.piece i → Matrix (Fin n) (Fin n) ℂ := fun z ↦
    ω₀.metricInChart (A.cover.base i) z
  let Hlim : A.cover.piece i → Matrix (Fin n) (Fin n) ℂ := fun z ↦
    complexHessian (φ ∘ e.symm) z
  let Hj : ℕ → A.cover.piece i → Matrix (Fin n) (Fin n) ℂ := fun j z ↦
    complexHessian (A.approx j ∘ e.symm) z
  have hmetricEntry (a b : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ ω₀.metricInChart (A.cover.base i) z a b) e.target :=
    ω₀.contDiffOn_metricInChart (A.cover.base i) a b
  have hmetricOn : ContinuousOn (ω₀.metricInChart (A.cover.base i))
      (A.cover.piece i) := by
    refine continuousOn_pi' ?_
    intro a
    refine continuousOn_pi' ?_
    intro b
    exact (hmetricEntry a b).continuousOn.mono (A.cover.piece_in_target i)
  have hg : Continuous g := by
    change Continuous ((A.cover.piece i).domRestrict
      (ω₀.metricInChart (A.cover.base i)))
    exact hmetricOn.domRestrict
  have hφon : ContMDiffOn I 𝓘(ℝ) 2 φ Set.univ := contMDiffOn_univ.mpr hφ.1
  have hφsymm : ContMDiffOn I 𝓘(ℝ) 2 (φ ∘ e.symm) e.target := by
    exact hφon.comp (contMDiffOn_extChartAt_symm (A.cover.base i))
      (by intro w hw; simp)
  have hφchart : ContDiffOn ℝ 2 (φ ∘ e.symm) e.target := hφsymm.contDiffOn
  have hHlimOn : ContinuousOn (fun z ↦ complexHessian (φ ∘ e.symm) z)
      (A.cover.piece i) :=
    (continuousOn_complexHessian_of_contDiffOn_two (isOpen_extChartAt_target _)
      hφchart).mono (A.cover.piece_in_target i)
  have hHlimContinuous : Continuous Hlim := hHlimOn.domRestrict
  obtain ⟨C, hC⟩ := (isCompact_univ.image hHlimContinuous).isBounded.exists_norm_le
  have hHbound : ∀ z, ‖Hlim z‖ ≤ C :=
    fun z ↦ hC (Hlim z) ⟨z, Set.mem_univ _, rfl⟩
  let G : Set (Matrix (Fin n) (Fin n) ℂ) := g '' Set.univ
  have hG : IsCompact G := by
    dsimp [G]
    exact isCompact_univ.image hg
  have hgG (z : A.cover.piece i) : g z ∈ G := ⟨z, Set.mem_univ _, rfl⟩
  have hden (z : A.cover.piece i) : 0 < RCLike.re (g z).det := by
    dsimp [g]
    exact (RCLike.pos_iff.mp
      (ω₀.posDef_metricInChart (A.cover.base i)
        (A.cover.piece_in_target i z.property)).det_pos).1
  have hdenG : ∀ m ∈ G, 0 < RCLike.re m.det := by
    rintro m ⟨z, hz, hm⟩
    rw [← hm]
    exact hden z
  have hconv : ∀ δ : ℝ, 0 < δ → ∃ N, ∀ j, N ≤ j → ∀ z,
      ‖Hj j z - Hlim z‖ ≤ δ := by
    intro δ hδ
    let δnn : ℝ≥0 := ⟨δ, hδ.le⟩
    have hδnn : 0 < δnn := by exact_mod_cast hδ
    obtain ⟨N, hN⟩ := A.convergesInC2 δnn hδnn
    refine ⟨N, ?_⟩
    intro j hj z
    have hHolder := hN j hj i
    have hsecond := hHolder.1 2 le_rfl z z.property
    have hA2 : ContMDiff I 𝓘(ℝ) 2 (A.approx j) := by
      have hbound : (2 : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) :=
        WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
      exact (A.smooth j).of_le hbound
    have hAon : ContMDiffOn I 𝓘(ℝ) 2 (A.approx j) Set.univ :=
      contMDiffOn_univ.mpr hA2
    have hAsymm : ContMDiffOn I 𝓘(ℝ) 2 (A.approx j ∘ e.symm) e.target := by
      exact hAon.comp (contMDiffOn_extChartAt_symm (A.cover.base i))
        (by intro w hw; simp)
    have hAchart : ContDiffOn ℝ 2 (A.approx j ∘ e.symm) e.target := hAsymm.contDiffOn
    let fA : EuclideanSpace ℂ (Fin n) → ℝ := (A.approx j) ∘ e.symm
    let fφ : EuclideanSpace ℂ (Fin n) → ℝ := φ ∘ e.symm
    let f : EuclideanSpace ℂ (Fin n) → ℝ := (A.approx j - φ) ∘ e.symm
    have hfEq : f = fA - fφ := by
      funext w
      simp [f, fA, fφ]
    have hfchart : ContDiffOn ℝ 2 f e.target := by
      rw [hfEq]
      exact hAchart.sub hφchart
    have hfAt : ContDiffAt ℝ 2 f z :=
      hfchart.contDiffAt ((isOpen_extChartAt_target (A.cover.base i)).mem_nhds
        (A.cover.piece_in_target i z.property))
    have hsecondR : ‖iteratedFDeriv ℝ 2 f z‖ ≤ δ := by
      have hδcoe : (δnn : ℝ) = δ := rfl
      simpa [f, e, I, extChartAt, modelWithCornersSelf_coe_symm] using
        hδcoe ▸ hsecond
    let D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) ℝ :=
      iteratedFDeriv ℝ 2 f z
    have htuple (u v : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
        ‖![u, v]‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro k
      fin_cases k
      · simpa using hu
      · simpa using hv
    have hderiv (u v : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
        ‖fderiv ℝ (fderiv ℝ f) z u v‖ ≤ δ := by
      have hEval := D.le_opNorm_mul_pow_of_le (m := ![u, v]) (b := 1)
        (htuple u v hu hv)
      have hDval : ‖D ![u, v]‖ ≤ δ := by
        calc
          ‖D ![u, v]‖ ≤ ‖D‖ * 1 ^ 2 := by simpa using hEval
          _ ≤ δ := by simpa [D] using hsecondR
      have heq : fderiv ℝ (fderiv ℝ f) z u v =
          iteratedFDeriv ℝ 2 f z ![u, v] := by
        rw [iteratedFDeriv_two_apply]
        rfl
      rw [heq]
      simpa [D] using hDval
    have hsingle (a : Fin n) : ‖EuclideanSpace.single a (1 : ℂ)‖ ≤ 1 := by simp
    have hIsingle (a : Fin n) :
        ‖Complex.I • EuclideanSpace.single a (1 : ℂ)‖ ≤ 1 := by
      rw [norm_smul, Complex.norm_I, one_mul]
      exact hsingle a
    have hentry (a b : Fin n) : ‖complexHessian f z a b‖ ≤ δ := by
      rw [complexHessian_apply hfAt a b]
      let p : ℝ := fderiv ℝ (fderiv ℝ f) z
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
      let q : ℝ := fderiv ℝ (fderiv ℝ f) z
          (Complex.I • EuclideanSpace.single a 1) (Complex.I • EuclideanSpace.single b 1)
      let r : ℝ := fderiv ℝ (fderiv ℝ f) z
          (EuclideanSpace.single a 1) (Complex.I • EuclideanSpace.single b 1)
      let s : ℝ := fderiv ℝ (fderiv ℝ f) z
          (Complex.I • EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
      have hp : ‖p‖ ≤ δ := hderiv _ _ (hsingle a) (hsingle b)
      have hq : ‖q‖ ≤ δ := hderiv _ _ (hIsingle a) (hIsingle b)
      have hr : ‖r‖ ≤ δ := hderiv _ _ (hsingle a) (hIsingle b)
      have hs : ‖s‖ ≤ δ := hderiv _ _ (hIsingle a) (hsingle b)
      have hpC : ‖(p : ℂ)‖ ≤ δ := by simpa using hp
      have hqC : ‖(q : ℂ)‖ ≤ δ := by simpa using hq
      have hrC : ‖(r : ℂ)‖ ≤ δ := by simpa using hr
      have hsC : ‖(s : ℂ)‖ ≤ δ := by simpa using hs
      calc
        ‖((p : ℂ) + q + Complex.I * ((r : ℂ) - s)) / 4‖
            = ‖(p : ℂ) + q + Complex.I * ((r : ℂ) - s)‖ / 4 := by simp
        _ ≤ (‖(p : ℂ)‖ + ‖(q : ℂ)‖ + ‖(r : ℂ)‖ + ‖(s : ℂ)‖) / 4 := by
          apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
          calc
            ‖(p : ℂ) + q + Complex.I * ((r : ℂ) - s)‖
                ≤ ‖(p : ℂ) + q‖ + ‖Complex.I * ((r : ℂ) - s)‖ := norm_add_le _ _
            _ ≤ ‖(p : ℂ)‖ + ‖(q : ℂ)‖ + (‖(r : ℂ)‖ + ‖(s : ℂ)‖) := by
              gcongr
              · exact norm_add_le _ _
              · simpa [Complex.norm_I] using norm_sub_le (r : ℂ) s
            _ = ‖(p : ℂ)‖ + ‖(q : ℂ)‖ + ‖(r : ℂ)‖ + ‖(s : ℂ)‖ := by ring_nf
        _ ≤ (δ + δ + δ + δ) / 4 := by gcongr
        _ = δ := by ring
    have hcomplexMatrix : ‖complexHessian f z‖ ≤ δ := by
      change ‖fun a b ↦ complexHessian f z a b‖ ≤ δ
      rw [pi_norm_le_iff_of_nonneg hδ.le]
      intro a
      rw [pi_norm_le_iff_of_nonneg hδ.le]
      intro b
      exact hentry a b
    have hddsub : ddbar f z = ddbar fA z - ddbar fφ z := by
      rw [hfEq]
      exact ddbar_sub
        (hAchart.contDiffAt ((isOpen_extChartAt_target (A.cover.base i)).mem_nhds
          (A.cover.piece_in_target i z.property)))
        (hφchart.contDiffAt ((isOpen_extChartAt_target (A.cover.base i)).mem_nhds
          (A.cover.piece_in_target i z.property)))
    have hHsub : complexHessian f z = Hj j z - Hlim z := by
      change (ddbar f z).coeffMatrix = (ddbar fA z).coeffMatrix - (ddbar fφ z).coeffMatrix
      rw [hddsub]
      simp [ContinuousAlternatingMap.coeffMatrix_sub]
    have hmatrix : ‖Hj j z - Hlim z‖ ≤ δ := by
      rw [← hHsub]
      exact hcomplexMatrix
    exact hmatrix
  have hratio : ∀ ε' : ℝ, 0 < ε' → ∃ N, ∀ j, N ≤ j → ∀ z,
      |RCLike.re (g z + Hj j z).det / RCLike.re (g z).det -
        RCLike.re (g z + Hlim z).det / RCLike.re (g z).det| ≤ ε' := by
    intro ε' hε'
    let B : ℝ := |C| + 1
    let K : Set (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :=
      G ×ˢ Metric.closedBall 0 B
    have hKcompact : IsCompact K := by
      dsimp [K]
      exact hG.prod (isCompact_closedBall 0 B)
    let F : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℝ := fun p ↦
      RCLike.re (p.1 + p.2).det / RCLike.re p.1.det
    have hnum : ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ ×
        Matrix (Fin n) (Fin n) ℂ ↦ RCLike.re (p.1 + p.2).det) K := by
      simp_rw [Matrix.det_apply]
      fun_prop
    have hdencont : ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ ×
        Matrix (Fin n) (Fin n) ℂ ↦ RCLike.re p.1.det) K := by
      simp_rw [Matrix.det_apply]
      fun_prop
    have hdenne : ∀ p ∈ K, RCLike.re p.1.det ≠ 0 := by
      rintro ⟨a, b⟩ hp
      exact ne_of_gt (hdenG a hp.1)
    have hFcont : ContinuousOn F K := by
      dsimp [F]
      exact hnum.div hdencont hdenne
    have hFunif : UniformContinuousOn F K :=
      hKcompact.uniformContinuousOn_of_continuous hFcont
    obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hFunif ε' hε'
    let η : ℝ := min (δ / 2) (1 / 2)
    have hηpos : 0 < η := by dsimp [η]; positivity
    have hηlt : η < δ :=
      (min_le_left _ _).trans_lt (by linarith)
    obtain ⟨N, hN⟩ := hconv η hηpos
    refine ⟨N, ?_⟩
    intro j hj z
    have hHlimnorm : ‖Hlim z‖ ≤ |C| := (hHbound z).trans (le_abs_self C)
    have hB : |C| ≤ B := by dsimp [B]; linarith
    have hHjnorm : ‖Hj j z‖ ≤ B := by
      calc
        ‖Hj j z‖ = ‖(Hj j z - Hlim z) + Hlim z‖ := by
          congr 1
          abel
        _ ≤ ‖Hj j z - Hlim z‖ + ‖Hlim z‖ := norm_add_le _ _
        _ ≤ η + |C| := add_le_add (hN j hj z) hHlimnorm
        _ ≤ B := by
          dsimp [B]
          have hηone : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
          linarith
    have hBallH : Hlim z ∈ Metric.closedBall (0 : Matrix (Fin n) (Fin n) ℂ) B := by
      simpa only [Metric.mem_closedBall, dist_eq_norm_sub, sub_zero] using hHlimnorm.trans hB
    have hBallJ : Hj j z ∈ Metric.closedBall (0 : Matrix (Fin n) (Fin n) ℂ) B := by
      simpa only [Metric.mem_closedBall, dist_eq_norm_sub, sub_zero] using hHjnorm
    have hp : (g z, Hj j z) ∈ K := ⟨hgG z, hBallJ⟩
    have hq : (g z, Hlim z) ∈ K := ⟨hgG z, hBallH⟩
    have hdist : dist (g z, Hj j z) (g z, Hlim z) < δ := by
      rw [dist_prod_same_left, dist_eq_norm]
      exact (hN j hj z).trans_lt hηlt
    have hout := hδ (g z, Hj j z) hp (g z, Hlim z) hq hdist
    rw [Real.dist_eq] at hout
    exact le_of_lt (by simpa [F] using hout)
  obtain ⟨N, hN⟩ := hratio ε hε
  have hA2 (j : ℕ) : ContMDiff I 𝓘(ℝ) 2 (A.approx j) := by
    have hbound : (2 : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) :=
      WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
    exact (A.smooth j).of_le hbound
  have hformulaA (j : ℕ) (z : A.cover.piece i) :
      ω₀.mongeAmpere (A.approx j) (e.symm z) =
        RCLike.re (g z + Hj j z).det / RCLike.re (g z).det := by
    have hz : (z : EuclideanSpace ℂ (Fin n)) ∈ e.target :=
      A.cover.piece_in_target i z.property
    have hyx : e.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (A.cover.base i)).source := by
      rw [← extChartAt_source (I := I)]
      exact e.map_target hz
    have hlocal := mongeAmpere_eq_inChart_of_contMDiff_two (ω₀ := ω₀)
      (hA2 j) (A.cover.base i) hyx
    rw [e.right_inv hz] at hlocal
    simpa [g, Hj, e, I, extChartAt, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm] using hlocal
  have hformulaφ (z : A.cover.piece i) :
      ω₀.mongeAmpere φ (e.symm z) =
        RCLike.re (g z + Hlim z).det / RCLike.re (g z).det := by
    have hz : (z : EuclideanSpace ℂ (Fin n)) ∈ e.target :=
      A.cover.piece_in_target i z.property
    have hyx : e.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (A.cover.base i)).source := by
      rw [← extChartAt_source (I := I)]
      exact e.map_target hz
    have hlocal := mongeAmpere_eq_inChart_of_contMDiff_two (ω₀ := ω₀)
      hφ.1 (A.cover.base i) hyx
    rw [e.right_inv hz] at hlocal
    simpa [g, Hlim, e, I, extChartAt, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm] using hlocal
  refine ⟨N, ?_⟩
  intro j hj z hz
  let z' : A.cover.piece i := ⟨z, hz⟩
  have h := hN j hj z'
  rw [hformulaA j z', hformulaφ z']
  exact h

theorem SmoothC2PotentialApproximationData.uniform_mongeAmpere_converges
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsC2Potential φ)
    (A : SmoothC2PotentialApproximationData ω₀ φ hφ) :
    Continuous (ω₀.mongeAmpere φ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N, ∀ j, N ≤ j → ∀ x,
        |ω₀.mongeAmpere (A.approx j) x - ω₀.mongeAmpere φ x| ≤ ε := by
  classical
  refine ⟨continuous_mongeAmpere_of_isC2Potential ω₀ hφ, ?_⟩
  intro ε hε
  have hlocal (i : A.cover.ι) :=
    uniform_mongeAmpere_on_compactChartCover_piece ω₀ hφ A i ε hε
  let Nᵢ : A.cover.ι → ℕ := fun i ↦ Classical.choose (hlocal i)
  let N : ℕ := ∑ i : A.cover.ι, Nᵢ i
  refine ⟨N, ?_⟩
  intro j hj x
  obtain ⟨i, ⟨z, hz, hx⟩⟩ := A.cover.interior_covers x
  have hNi : Nᵢ i ≤ N := by
    dsimp [N]
    exact Finset.single_le_sum (fun k hk ↦ Nat.zero_le (Nᵢ k)) (Finset.mem_univ i)
  have hpiece : z ∈ A.cover.piece i := interior_subset hz
  have hchart := (Classical.choose_spec (hlocal i)) j (le_trans hNi hj) z hpiece
  simpa only [hx] using hchart

end KahlerForm
