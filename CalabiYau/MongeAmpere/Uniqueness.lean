module

public import CalabiYau.MongeAmpere.Operator

/-!
# Uniqueness of solutions of the complex Monge–Ampère equation (Calabi)

On a compact connected Kähler manifold, two Kähler potentials with the same Monge–Ampère measure
differ by a constant. No analytic input beyond Green's formula is needed.

## Proof (Calabi 1957; Yau 1978, §1; Székelyhidi, Exercise 3.16; Błocki, *The Calabi–Yau theorem*)

Let `u = ψ - φ` and `ω_s = ω_φ + s i∂∂̄u = ω₀ + i∂∂̄((1 - s)φ + sψ)`, Kähler for `s ∈ [0, 1]`
(`IsPotential.convex_comb`). By the segment formula for `ω_φ`
(`mongeAmpere_sub_one_eq_integral`, `mongeAmpere_add`, `volume_perturb`),

  `0 = ∫ u (ω_ψⁿ - ω_φⁿ) = ∫₀¹ ∫ u Δ_{ω_s} u ω_sⁿ ds = -∫₀¹ ∫ |∂u|²_{ω_s} ω_sⁿ ds`

(Green's formula `integral_mul_laplacian_self` for each `ω_s`). Hence `∂u = 0`
(`gradNormSq_eq_zero_iff`, continuity in `s`) and `u` is constant on the connected `M`.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M]

/-- **Calabi's uniqueness theorem.** Two Kähler potentials with the same Monge–Ampère measure
differ by a constant. -/
theorem eq_add_const_of_mongeAmpere_eq {ω₀ : KahlerForm n M} {φ ψ : M → ℝ}
    (hφ : ω₀.IsPotential φ) (hψ : ω₀.IsPotential ψ)
    (h : ω₀.mongeAmpere φ = ω₀.mongeAmpere ψ) : ∃ c : ℝ, ∀ x, ψ x = φ x + c := by
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have : BorelSpace (ℝ × M) := inferInstance
  let ωφ := ω₀.perturb φ hφ
  let u : M → ℝ := ψ - φ
  have hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u := hψ.1.sub hφ.1
  have hsum : φ + u = ψ := by
    funext x
    simp [u]
  have huPot : ωφ.IsPotential u := by
    apply (isPotential_perturb_iff hφ).2
    simpa [u] using hψ
  have huMA : ωφ.mongeAmpere u = 1 := by
    funext x
    have hfactor := mongeAmpere_add hφ hu x
    have hpoint := congrFun h x
    rw [← hsum] at hpoint
    rw [hfactor] at hpoint
    exact mul_left_cancel₀ (ne_of_gt (mongeAmpere_pos hφ x))
      (by simpa [ωφ, u] using hpoint.symm)
  let t : ℝ → ℝ := fun s ↦ max 0 (min 1 s)
  have ht0 (s : ℝ) : 0 ≤ t s := le_max_left _ _
  have ht1 (s : ℝ) : t s ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have htid (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) 1) : t s = s := by
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by simpa using hs
    simp [t, hs'.1, hs'.2]
  let hpot (s : ℝ) := huPot.smul (ht0 s) (ht1 s)
  let ωs (s : ℝ) := ωφ.perturb (t s • u) (hpot s)
  let F : ℝ → M → ℝ := fun s x ↦
    u x * ωφ.mongeAmpere (t s • u) x * (ωs s).laplacian u x
  have htu (s : ℝ) : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (t s • u) := by
    have hmul : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 * p.2) := contDiff_fst.mul contDiff_snd
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (fun x ↦ t s * u x)
    simpa [Function.comp_def, smul_eq_mul] using
      hmul.comp_contMDiff (contMDiff_const.prodMk_space hu)
  have hHsmul (s : ℝ) (x : M) {z : EuclideanSpace ℂ (Fin n)}
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      complexHessian ((t s • u) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z =
        t s • complexHessian (u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
    change (ddbar ((t s • u) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z).coeffMatrix =
      t s • (ddbar (u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z).coeffMatrix
    rw [← chartRep_mddbar (htu s) x hz, ← chartRep_mddbar hu x hz]
    rw [mddbar_smul hu (t s), FormField.chartRep_smul]
    simp [ContinuousAlternatingMap.coeffMatrix_smul]
  have hHcont (x : M) :
      ContinuousOn (fun z => complexHessian (u ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    have hrep : ContDiffOn ℝ ∞ ((mddbar n u).chartRep x) c.target := isSmooth_mddbar hu x
    have hcoeff : Continuous fun α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ => α.coeffMatrix := by
      fun_prop [ContinuousAlternatingMap.coeffMatrix]
    have hc : ContinuousOn (fun z => ((mddbar n u).chartRep x z).coeffMatrix) c.target := by
      exact hcoeff.continuousOn.comp hrep.continuousOn (fun _ _ => Set.mem_univ _)
    refine hc.congr ?_
    intro z hz
    change (ddbar (u ∘ c.symm) z).coeffMatrix = _
    rw [← chartRep_mddbar hu x hz]
  have hGcont (x : M) :
      ContinuousOn (ωφ.metricInChart x)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    refine continuousOn_pi' ?_
    intro j
    refine continuousOn_pi' ?_
    intro k
    exact (ωφ.contDiffOn_metricInChart x j k).continuousOn
  have hmetric_path (s : ℝ) (x : M) {z : EuclideanSpace ℂ (Fin n)}
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      (ωs s).metricInChart x z = ωφ.metricInChart x z + t s •
        complexHessian (u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
    rw [KahlerForm.metricInChart_perturb (hpot s) x hz, hHsmul s x hz]
  have hFchart (s : ℝ) (x₀ y : M) (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source) :
      F s y = u y *
        (RCLike.re ((ωs s).metricInChart x₀ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).det /
          RCLike.re (ωφ.metricInChart x₀
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).det) *
        RCLike.re ((((ωs s).metricInChart x₀
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y))⁻¹ *
          complexHessian (u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).trace) := by
    have hyE : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).source := by
      simpa only [extChartAt_source] using hy
    dsimp [F, ωs]
    rw [mongeAmpere_eq_inChart (htu s) x₀ hy,
      (ωs s).laplacian_eq_inChart hu x₀ hy,
      ← KahlerForm.metricInChart_perturb (hpot s) x₀
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).map_source hyE)]
    rw [extChartAt_coe, extChartAt_coe_symm]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
      Function.comp_id, id_eq]
    dsimp [ωs]
  have htcont : Continuous t := by
    change Continuous (fun s : ℝ ↦ max 0 (min 1 s))
    fun_prop
  have hAcont (x₀ : M) :
      ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) ↦
        ωφ.metricInChart x₀ p.2 + t p.1 •
          complexHessian (u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) p.2)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) := by
    have hg : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        ωφ.metricInChart x₀ p.2)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :=
      (hGcont x₀).comp continuousOn_snd (fun (p : ℝ × EuclideanSpace ℂ (Fin n)) hp => hp.2)
    have hh : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        complexHessian (u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) p.2)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :=
      (hHcont x₀).comp continuousOn_snd (fun (p : ℝ × EuclideanSpace ℂ (Fin n)) hp => hp.2)
    have ht : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) => t p.1)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :=
      htcont.continuousOn.comp continuousOn_fst (fun (_ : ℝ × EuclideanSpace ℂ (Fin n)) _ => Set.mem_univ _)
    exact hg.add (ht.smul hh)
  have hApath_cont (x₀ : M) :
      ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) => (ωs p.1).metricInChart x₀ p.2)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) := by
    refine (hAcont x₀).congr ?_
    rintro ⟨s, z⟩ ⟨_, hz⟩
    exact hmetric_path s x₀ hz
  let Q : M → (ℝ × EuclideanSpace ℂ (Fin n)) → ℝ := fun x₀ p ↦
    u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm p.2) *
      (RCLike.re ((ωs p.1).metricInChart x₀ p.2).det /
        RCLike.re (ωφ.metricInChart x₀ p.2).det) *
      RCLike.re (((ωs p.1).metricInChart x₀ p.2)⁻¹ *
        complexHessian (u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) p.2).trace
  have hQcont (x₀ : M) :
      ContinuousOn (Q x₀)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) := by
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
    let S : Set (ℝ × EuclideanSpace ℂ (Fin n)) := (Set.univ : Set ℝ) ×ˢ c.target
    let A : ℝ × EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun p ↦ (ωs p.1).metricInChart x₀ p.2
    have hA : ContinuousOn A S := by
      change ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        (ωs p.1).metricInChart x₀ p.2)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target)
      exact hApath_cont x₀
    have hH : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        complexHessian (u ∘ c.symm) p.2) S := by
      exact (hHcont x₀).comp continuousOn_snd (fun _ hp => hp.2)
    have hG : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        ωφ.metricInChart x₀ p.2) S := by
      exact (hGcont x₀).comp continuousOn_snd (fun _ hp => hp.2)
    have hdetA : ContinuousOn (fun p => (A p).det) S := by
      fun_prop
    have hdetG : ContinuousOn (fun p => (ωφ.metricInChart x₀ p.2).det) S := by
      fun_prop
    have hdetAinv : ContinuousOn (fun p => ((A p).det)⁻¹) S := by
      apply hdetA.inv₀
      intro p hp
      have hpos := (ωs p.1).posDef_metricInChart x₀ hp.2
      exact ((Matrix.isUnit_iff_isUnit_det (A p)).1 (by simpa [A] using hpos.isUnit)).ne_zero
    have hAdj : ContinuousOn (fun p => (A p).adjugate) S := by fun_prop
    have hAinv : ContinuousOn (fun p => (A p)⁻¹) S := by
      have h := hdetAinv.smul hAdj
      convert h using 1
      ext p i j
      simp [Matrix.inv_def]
    have htrace : ContinuousOn (fun p =>
        RCLike.re (((A p)⁻¹ * (fun z => complexHessian (u ∘ c.symm) z) p.2).trace)) S := by
      have hm := hAinv.mul hH
      fun_prop
    have hnum : ContinuousOn (fun p => RCLike.re (A p).det) S := by fun_prop
    have hden : ContinuousOn (fun p => RCLike.re (ωφ.metricInChart x₀ p.2).det) S := by fun_prop
    have hdenNe : ∀ p ∈ S, RCLike.re (ωφ.metricInChart x₀ p.2).det ≠ 0 := by
      rintro ⟨s, z⟩ ⟨_, hz⟩
      have h := ωφ.volumeDensityInChart_pos x₀ hz
      dsimp [KahlerForm.volumeDensityInChart] at h
      exact ne_of_gt ((mul_pos_iff_of_pos_left (by positivity : 0 < (2 : ℝ) ^ n)).mp h)
    have hdenInv : ContinuousOn (fun p => (RCLike.re (ωφ.metricInChart x₀ p.2).det)⁻¹) S :=
      hden.inv₀ hdenNe
    have hratio : ContinuousOn (fun p => RCLike.re (A p).det *
        (RCLike.re (ωφ.metricInChart x₀ p.2).det)⁻¹) S := hnum.mul hdenInv
    have huC : ContinuousOn (fun p =>
        u (c.symm p.2)) S := by
      have hc := (continuousOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀)
      have hc' := hc.comp continuousOn_snd
        (fun (p : ℝ × EuclideanSpace ℂ (Fin n)) (hp : p ∈ S) => hp.2)
      exact hu.continuous.continuousOn.comp hc' (fun _ _ => Set.mem_univ _)
    change ContinuousOn (fun p =>
      u (c.symm p.2) *
        (RCLike.re (A p).det / RCLike.re (ωφ.metricInChart x₀ p.2).det) *
        RCLike.re ((A p)⁻¹ * complexHessian (u ∘ c.symm) p.2).trace) S
    have hprod := huC.mul (hratio.mul htrace)
    convert hprod using 1 ; ext p ;
      simp only [Pi.mul_apply, div_eq_mul_inv] ; ring
  have hFcont : Continuous (Function.uncurry F) := by
    rw [continuous_iff_continuousAt]
    intro p
    rcases p with ⟨s₀, x₀⟩
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
    have hqOpen : IsOpen (Set.univ ×ˢ c.target) :=
      (isOpen_prod_iff' (s := (Set.univ : Set ℝ)) (t := c.target)).2 (Or.inl ⟨isOpen_univ,
        isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩)
    have hqmem : Set.univ ×ˢ c.target ∈ nhds (s₀, c x₀) :=
      hqOpen.mem_nhds ⟨Set.mem_univ _, mem_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩
    have hq : ContinuousAt (Q x₀) (s₀, c x₀) :=
      (hQcont x₀).continuousAt hqmem
    have hcomp : ContinuousAt (fun p : ℝ × M => Q x₀ (p.1, c p.2)) (s₀, x₀) :=
      hq.comp₂ continuousAt_fst
        ((continuousAt_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀).comp
          continuousAt_snd)
    have hsourceOpen : IsOpen (Set.univ ×ˢ c.source) :=
      (isOpen_prod_iff' (s := (Set.univ : Set ℝ)) (t := c.source)).2 (Or.inl ⟨isOpen_univ,
        isOpen_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩)
    have hsource : Set.univ ×ˢ c.source ∈ nhds (s₀, x₀) :=
      hsourceOpen.mem_nhds ⟨Set.mem_univ _, mem_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩
    have heq : Function.uncurry F =ᶠ[nhds (s₀, x₀)]
        (fun p : ℝ × M => Q x₀ (p.1, c p.2)) := by
      filter_upwards [hsource] with p hp
      rcases p with ⟨s, y⟩
      have hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := by
        simpa [c, extChartAt_source] using hp.2
      change F s y = Q x₀ (s, c y)
      have hr : (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm
          ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) y) = y :=
        (chartAt (EuclideanSpace ℂ (Fin n)) x₀).left_inv hy
      simpa [Q, c, hr] using hFchart s x₀ y hy
    exact hcomp.congr_of_eventuallyEq heq
  have hFsegment (s : ℝ) (x : M) :
      F s x = u x * (ContinuousAlternatingMap.relDet (ωφ x)
        (ωφ x + t s • mddbar n u x) * ContinuousAlternatingMap.relTrace
        (ωφ x + t s • mddbar n u x) (mddbar n u x)) := by
    simp [F, ωs, mongeAmpere, laplacian, perturb_apply,
      mddbar_smul huPot.1 (t s)]
    ring
  have hpoint (x : M) : u x * (ωφ.mongeAmpere u x - 1) =
      ∫ s in (0 : ℝ)..1, F s x := by
    rw [mongeAmpere_sub_one_eq_integral huPot x]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    change u x * (ContinuousAlternatingMap.relDet (ωφ x)
      (ωφ x + s • mddbar n u x) * ContinuousAlternatingMap.relTrace
      (ωφ x + s • mddbar n u x) (mddbar n u x)) = F s x
    calc
      _ = u x * (ContinuousAlternatingMap.relDet (ωφ x)
          (ωφ x + t s • mddbar n u x) * ContinuousAlternatingMap.relTrace
          (ωφ x + t s • mddbar n u x) (mddbar n u x)) := by rw [htid s hs]
      _ = F s x := by rw [hFsegment s x]
  have hFint : MeasureTheory.Integrable (Function.uncurry F)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod ωφ.volume) := by
    let ν := (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod ωφ.volume
    have hcompact : IsCompact
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := isCompact_Icc.prod isCompact_univ
    obtain ⟨C, hC⟩ :=
      (hcompact.image_of_continuousOn hFcont.continuousOn).isBounded.exists_norm_le
    have hsubset : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
      simpa using (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 1))
    have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) 1, ∀ x, F s x ∈ Set.Icc (-C) C := by
      intro s hs x
      have hs' := hsubset hs
      have himage : Function.uncurry F (s, x) ∈
          Function.uncurry F '' (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
        ⟨(s, x), ⟨hs', Set.mem_univ x⟩, rfl⟩
      have hnorm := hC (F s x) himage
      have habs : |F s x| ≤ C := by simpa [Real.norm_eq_abs] using hnorm
      exact abs_le.mp habs
    have hvol : MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) < ⊤ := by
      have hsubset' : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
        simpa using (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 1))
      calc
        MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) ≤ MeasureTheory.volume (Set.Icc 0 1) :=
          MeasureTheory.measure_mono hsubset'
        _ = ENNReal.ofReal (1 - 0) := by rw [Real.volume_Icc]
        _ < ⊤ := ENNReal.ofReal_lt_top
    let : Fact (MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) < ⊤) := ⟨hvol⟩
    have : MeasureTheory.IsFiniteMeasure ν := by
      dsimp [ν]
      infer_instance
    have hmeas : AEMeasurable (Function.uncurry F) ν := hFcont.measurable.aemeasurable
    have hset : MeasurableSet {z : ℝ × M | Function.uncurry F z ∈ Set.Icc (-C) C} :=
      isClosed_Icc.measurableSet.preimage hFcont.measurable
    have hboundAE : ∀ᵐ z ∂ν, Function.uncurry F z ∈ Set.Icc (-C) C := by
      rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hset]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
      exact Filter.Eventually.of_forall fun x => hbound s hs x
    exact MeasureTheory.Integrable.of_mem_Icc (-C) C hmeas hboundAE
  have hweighted :
      ∫ x, u x * (ωφ.mongeAmpere u x - 1) ∂ωφ.volume =
        ∫ s in (0 : ℝ)..1, ∫ x, F s x ∂ωφ.volume ∂MeasureTheory.volume := by
    calc
      ∫ x, u x * (ωφ.mongeAmpere u x - 1) ∂ωφ.volume =
          ∫ x, ∫ s in (0 : ℝ)..1, F s x ∂MeasureTheory.volume ∂ωφ.volume := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = ∫ s in (0 : ℝ)..1, ∫ x, F s x ∂ωφ.volume ∂MeasureTheory.volume :=
        (MeasureTheory.intervalIntegral_integral_swap hFint).symm
  have hzero : ∫ x, u x * (ωφ.mongeAmpere u x - 1) ∂ωφ.volume = 0 := by
    calc
      ∫ x, u x * (ωφ.mongeAmpere u x - 1) ∂ωφ.volume = ∫ x, (0 : ℝ) ∂ωφ.volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [show ωφ.mongeAmpere u x = 1 from congrFun huMA x]
        ring
      _ = 0 := MeasureTheory.integral_zero M ℝ
  have hFenergy : ∫ s in (0 : ℝ)..1, ∫ x, F s x ∂ωφ.volume ∂MeasureTheory.volume = 0 :=
    hweighted ▸ hzero
  have hPhiCont : Continuous (fun s => ∫ x, F s x ∂ωφ.volume) := by
    apply continuousOn_univ.mp
    exact continuousOn_integral_of_compact_support isCompact_univ hFcont.continuousOn
      (fun _ x _ hx => False.elim (hx (Set.mem_univ x)))
  have hvolumeIntegral (s : ℝ) (g : M → ℝ) :
      ∫ x, g x ∂(ωs s).volume =
        ∫ x, g x * ωφ.mongeAmpere (t s • u) x ∂ωφ.volume := by
    have hden : Measurable (fun x => ENNReal.ofReal (ωφ.mongeAmpere (t s • u) x)) :=
      ENNReal.measurable_ofReal.comp
        (ωφ.contMDiff_mongeAmpere (hpot s).1).continuous.measurable
    rw [ωφ.volume_perturb (hpot s),
      integral_withDensity_eq_integral_toReal_smul hden
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal
      (le_of_lt (ωφ.mongeAmpere_pos (hpot s) x))]
    change ωφ.mongeAmpere (t s • u) x * g x = g x * ωφ.mongeAmpere (t s • u) x
    ring
  have henergy (s : ℝ) :
      ∫ x, F s x ∂ωφ.volume =
        -∫ x, (ωs s).gradNormSq u x ∂(ωs s).volume := by
    calc
      ∫ x, F s x ∂ωφ.volume =
          ∫ x, (u x * (ωs s).laplacian u x) * ωφ.mongeAmpere (t s • u) x
            ∂ωφ.volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [F]
        ring
      _ = ∫ x, u x * (ωs s).laplacian u x ∂(ωs s).volume :=
        (hvolumeIntegral s (fun x => u x * (ωs s).laplacian u x)).symm
      _ = -∫ x, (ωs s).gradNormSq u x ∂(ωs s).volume :=
        (ωs s).integral_mul_laplacian_self hu
  have henergyIntegral :
      ∫ s in (0 : ℝ)..1, ∫ x, F s x ∂ωφ.volume ∂MeasureTheory.volume =
        -∫ s in (0 : ℝ)..1, ∫ x, (ωs s).gradNormSq u x ∂(ωs s).volume
          ∂MeasureTheory.volume := by
    calc
      _ = ∫ s in (0 : ℝ)..1,
          -∫ x, (ωs s).gradNormSq u x ∂(ωs s).volume ∂MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact henergy s
      _ = -∫ s in (0 : ℝ)..1,
          ∫ x, (ωs s).gradNormSq u x ∂(ωs s).volume ∂MeasureTheory.volume := by
        rw [intervalIntegral.integral_neg]
  have henergyZero :
      ∫ s in (0 : ℝ)..1, ∫ x, (ωs s).gradNormSq u x ∂(ωs s).volume
        ∂MeasureTheory.volume = 0 := by
    rw [henergyIntegral] at hFenergy
    linarith
  have hPhi_le (s : ℝ) : (∫ x, F s x ∂ωφ.volume) ≤ 0 := by
    rw [henergy s]
    exact neg_nonpos.mpr (MeasureTheory.integral_nonneg fun x =>
      (ωs s).gradNormSq_nonneg u x)
  have hPhiInt : IntervalIntegrable (fun s => ∫ x, F s x ∂ωφ.volume)
      MeasureTheory.volume 0 1 :=
    hPhiCont.continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hnegPhiInt : ∫ s in (0 : ℝ)..1, -(∫ x, F s x ∂ωφ.volume)
      ∂MeasureTheory.volume = 0 := by
    rw [intervalIntegral.integral_neg, hFenergy]
    simp
  have hPhi_ae : (fun s => -(∫ x, F s x ∂ωφ.volume)) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)] (0 : ℝ → ℝ) := by
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict
        (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioc (1 : ℝ) 0)]
        (fun s => -(∫ x, F s x ∂ωφ.volume)) :=
      Filter.Eventually.of_forall fun s => neg_nonneg.mpr (hPhi_le s)
    have hae := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae hnn hPhiInt.neg).mp
      hnegPhiInt
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (fun _ hs => Or.inl hs) hae
  have hPhi_aeIoo : (fun s => -(∫ x, F s x ∂ωφ.volume)) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)] (0 : ℝ → ℝ) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (by
        intro s hs
        exact ⟨hs.1, hs.2.le⟩) hPhi_ae
  have hPhi_zero : ∀ s ∈ Set.Ioo (0 : ℝ) 1, ∫ x, F s x ∂ωφ.volume = 0 := by
    have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hPhi_aeIoo isOpen_Ioo
      hPhiCont.neg.continuousOn continuousOn_const
    intro s hs
    exact neg_eq_zero.mp (heq hs)
  let s₀ : ℝ := 1 / 2
  have hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1 := by norm_num [s₀]
  have hgradIntZero :
      ∫ x, (ωs s₀).gradNormSq u x ∂(ωs s₀).volume = 0 := by
    have h := hPhi_zero s₀ hs₀
    rw [henergy s₀] at h
    linarith
  have hgradCont : Continuous (fun x => (ωs s₀).gradNormSq u x) :=
    ((ωs s₀).contMDiff_gradNormSq hu).continuous
  have hgradIntegrable : MeasureTheory.Integrable
      (fun x => (ωs s₀).gradNormSq u x) (ωs s₀).volume :=
    hgradCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgradAE : (fun x => (ωs s₀).gradNormSq u x) =ᵐ[(ωs s₀).volume] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => (ωs s₀).gradNormSq_nonneg u x)
      hgradIntegrable).mp hgradIntZero
  have hgradEq := MeasureTheory.Measure.eq_of_ae_eq hgradAE hgradCont continuous_zero
  have hgradZero (x : M) : (ωs s₀).gradNormSq u x = 0 := congrFun hgradEq x
  have hmfZero (x : M) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℝ) u x = 0 :=
    ((ωs s₀).gradNormSq_eq_zero_iff hu x).mp (hgradZero x)
  have hloc : IsLocallyConstant u := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let F : EuclideanSpace ℂ (Fin n) → ℝ := fun z => u (e.symm z)
    have hFdiff : DifferentiableOn ℝ F e.target := by
      have hFmd : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) 𝓘(ℝ, ℝ) ∞ F e.target := by
        exact (contMDiffOn_univ.mpr hu).comp
          (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x)
          (by intro z hz; simp)
      exact hFmd.contDiffOn.differentiableOn (by simp)
    have hFzero : e.target.EqOn (fderiv ℝ F) 0 := by
      intro z hz
      let p : M := e.symm z
      have hg : MDifferentiableWithinAt (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
          𝓘(ℝ, ℝ) u Set.univ p :=
        (hu.mdifferentiableAt (by simp)).mdifferentiableWithinAt
      have hf : MDifferentiableWithinAt (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
          (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) e.symm
          (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) z :=
        mdifferentiableWithinAt_extChartAt_symm hz
      have huniq : UniqueMDiffWithinAt (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
          (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) z := by
        exact ((𝓘(ℝ, EuclideanSpace ℂ (Fin n))).uniqueDiffOn.uniqueDiffWithinAt
          (by exact extChartAt_target_subset_range x hz)).uniqueMDiffWithinAt
      have hchain := mfderivWithin_comp
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
        (I' := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (I'' := 𝓘(ℝ, ℝ))
        (x := z) (g := u) (f := e.symm) hg hf
        (fun _ _ => Set.mem_univ _) huniq
      rw [mfderivWithin_univ] at hchain
      change mfderivWithin (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) 𝓘(ℝ, ℝ)
          (u ∘ e.symm) (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) z =
        (mfderiv (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) 𝓘(ℝ, ℝ) u p) ∘L
          mfderivWithin (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
            (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) e.symm
            (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) z at hchain
      have hfd : fderiv ℝ F z = 0 := by
        have hfd' (v : EuclideanSpace ℂ (Fin n)) :
            fderivWithin ℝ
              (writtenInExtChartAt (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) 𝓘(ℝ, ℝ) x u)
              (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) z v = 0 := by
          calc
            fderivWithin ℝ (writtenInExtChartAt (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
                𝓘(ℝ, ℝ) x u) (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) z v =
                NormedSpace.fromTangentSpace (𝕜 := ℝ) (u p)
                ((mfderivWithin (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) 𝓘(ℝ, ℝ)
                    (u ∘ e.symm) (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) z) v) := by
                  rw [mfderivWithin_eq_fderivWithin]
                  rw [writtenInExtChartAt, extChartAt_model_space_eq_id]
                  rfl
            _ = NormedSpace.fromTangentSpace (𝕜 := ℝ) (u p)
                ((mfderiv (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) 𝓘(ℝ, ℝ) u p)
                  ((mfderivWithin (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
                    (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) e.symm
                    (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) z) v)) := by
              have hv :
                  (mfderivWithin (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) 𝓘(ℝ, ℝ)
                    (u ∘ e.symm) (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) z) v =
                  (mfderiv (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) 𝓘(ℝ, ℝ) u p)
                      ((mfderivWithin (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
                        (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) e.symm
                        (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) z) v) := by
                exact (congrArg (fun L => L v) hchain).trans
                  (ContinuousLinearMap.comp_apply _ _ v)
              exact congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (u p)) hv
            _ = 0 := by rw [hmfZero p]; simp
        have hfd' : fderivWithin ℝ
            (writtenInExtChartAt (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) 𝓘(ℝ, ℝ) x u)
            (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) z = 0 := by
          ext v
          exact hfd' v
        rw [ModelWithCorners.Boundaryless.range_eq_univ
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))), fderivWithin_univ] at hfd'
        have hreal :
            writtenInExtChartAt (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) 𝓘(ℝ, ℝ) x u = F := by
          funext y
          rw [writtenInExtChartAt, extChartAt_model_space_eq_id]
          rfl
        rw [hreal] at hfd'
        exact hfd'
      simpa using hfd
    have hopen : IsOpen (e.target ∩ F ⁻¹' ({F (e x)} : Set ℝ)) :=
      (isOpen_extChartAt_target x).isOpen_inter_preimage_of_fderiv_eq_zero
        hFdiff hFzero ({F (e x)} : Set ℝ)
    have hxmem : e x ∈ e.target ∩ F ⁻¹' ({F (e x)} : Set ℝ) := by
      exact ⟨mem_extChartAt_target x, by simp [F]⟩
    have hpre : e ⁻¹' (e.target ∩ F ⁻¹' ({F (e x)} : Set ℝ)) ∈ nhds x :=
      (continuousAt_extChartAt x).preimage_mem_nhds (hopen.mem_nhds hxmem)
    filter_upwards [hpre,
      extChartAt_source_mem_nhds (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x] with y hy hysource
    have heq : F (e y) = F (e x) := hy.2
    change u (e.symm (e y)) = u (e.symm (e x)) at heq
    simpa [e.left_inv hysource,
      e.left_inv (mem_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x)] using heq
  obtain ⟨c, hc⟩ := hloc.exists_eq_const
  exact ⟨c, fun x => by
    have hux : u x = c := by simpa using congrFun hc x
    calc
      ψ x = φ x + u x := (congrFun hsum x).symm
      _ = φ x + c := by rw [hux]⟩

/-- Uniqueness for the Monge–Ampère equation with a given right-hand side. -/
theorem SolvesMongeAmpere.eq_add_const {ω₀ : KahlerForm n M} {G φ ψ : M → ℝ}
    (hφ : ω₀.SolvesMongeAmpere G φ) (hψ : ω₀.SolvesMongeAmpere G ψ) :
    ∃ c : ℝ, ∀ x, ψ x = φ x + c :=
  eq_add_const_of_mongeAmpere_eq hφ.1 hψ.1 (funext fun x ↦ (hφ.2 x).trans (hψ.2 x).symm)

end KahlerForm

private theorem interval_product_integrable_of_continuous_bounded
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [BorelSpace (ℝ × X)] {μ : MeasureTheory.Measure X} [MeasureTheory.IsFiniteMeasure μ]
    {f : ℝ → X → ℝ} (hf : Continuous (Function.uncurry f))
    (hbound : ∃ C : ℝ, ∀ s ∈ Set.uIoc (0 : ℝ) 1, ∀ x, f s x ∈ Set.Icc (-C) C) :
    MeasureTheory.Integrable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod μ) := by
  let ν := (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod μ
  obtain ⟨C, hC⟩ := hbound
  have hvol : MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) < ⊤ := by
    have hsubset : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
      simpa using (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 1))
    calc
      MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) ≤ MeasureTheory.volume (Set.Icc 0 1) :=
        MeasureTheory.measure_mono hsubset
      _ = ENNReal.ofReal (1 - 0) := by rw [Real.volume_Icc]
      _ < ⊤ := ENNReal.ofReal_lt_top
  let : Fact (MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) < ⊤) := ⟨hvol⟩
  have : MeasureTheory.IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  have hfmeas : AEMeasurable (Function.uncurry f) ν :=
    hf.measurable.aemeasurable
  have hset : MeasurableSet {z : ℝ × X | Function.uncurry f z ∈ Set.Icc (-C) C} :=
    isClosed_Icc.measurableSet.preimage hf.measurable
  have hboundAE : ∀ᵐ z ∂ν, Function.uncurry f z ∈ Set.Icc (-C) C := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
    exact Filter.Eventually.of_forall fun x ↦ hC s hs x
  exact MeasureTheory.Integrable.of_mem_Icc (-C) C hfmeas hboundAE

private theorem interval_product_integrable_of_continuous
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [BorelSpace (ℝ × X)] [CompactSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ] {f : ℝ → X → ℝ}
    (hf : Continuous (Function.uncurry f)) :
    MeasureTheory.Integrable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod μ) := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set X)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ :=
    (hcompact.image_of_continuousOn hf.continuousOn).isBounded.exists_norm_le
  have hsubset : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
    simpa using (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 1))
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) 1, ∀ x, f s x ∈ Set.Icc (-C) C := by
    intro s hs x
    have hs' := hsubset hs
    have himage : Function.uncurry f (s, x) ∈
        Function.uncurry f '' (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set X)) :=
      ⟨(s, x), ⟨hs', Set.mem_univ x⟩, rfl⟩
    have hnorm := hC (f s x) himage
    have habs : |f s x| ≤ C := by simpa [Real.norm_eq_abs] using hnorm
    exact abs_le.mp habs
  exact interval_product_integrable_of_continuous_bounded hf ⟨C, hbound⟩
