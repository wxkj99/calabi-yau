module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Mathlib.Geometry.Manifold.Holder
import CalabiYau.MongeAmpere.Estimates.C3.MetricEquivalence
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian
import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian
import CalabiYau.MongeAmpere.Estimates.C3.ChartDerivative

/-!
# The third-order estimate (Calabi)

Let `S` be a family of solutions `(G, φ)` of `(ω₀ + i∂∂̄φ)ⁿ = e^G ω₀ⁿ` such that the right-hand
sides `G` are bounded in `C³` and the metrics `ω_φ = ω₀ + i∂∂̄φ` are uniformly bounded above,
`tr_ω₀ ω_φ ≤ Λ` (the output of the `C²` estimate; the lower bound `ω_φ ≥ c ω₀` then follows from
the equation). Then the complex Hessians `i∂∂̄φ` are bounded in `C¹`, uniformly on `S`, in every
chart.

Uniformity over the family is how the dependence of the constant is expressed: the bound depends
only on `(M, ω₀)`, on `Λ` and on the `C³` bounds of the `G`s (`HolderBoundedInCharts … 3 0`).
Since `C^k` norms on `M` are only defined up to equivalence, families are the atlas-free way to
state this (see `CalabiYau.Geometry.Complex.Holder`).

## Proof sketch (Calabi 1957; Yau 1978, §3; Székelyhidi, Lemmas 3.9–3.10; Aubin, *Some nonlinear
problems in Riemannian geometry*, §7.5; Phong–Sesum–Sturm, *Multiplier ideal sheaves and the
Kähler–Ricci flow*, §2)

Let `S = |∇_ω₀ i∂∂̄φ|²_{ω_φ} = g'^{ir̄} g'^{sj̄} g'^{kt̄} φ_{ij̄k} φ̄_{rs̄t}` (covariant derivatives
of `ω₀`, computed in charts from `KahlerForm.metricInChart` and `complexHessian`). Differentiating
the equation `log det(g + φ_{jk̄}) = G + log det g` three times gives, with `C` depending on
`(M, ω₀)`, `Λ` and `‖G‖_{C³}`,

  `Δ_{ω_φ} S ≥ -C S - C`, and `Δ_{ω_φ} tr_ω₀ ω_φ ≥ c S - C`

(Calabi's identity; the second is the refined Aubin–Yau inequality). Hence
`Δ_{ω_φ} (S + A tr_ω₀ ω_φ) ≥ S - C'` for large `A`, and the maximum principle
(`relTrace_mddbar_nonpos_of_isLocalMax` with `α = ω_φ`) gives `S ≤ C''`. Uniform equivalence of
`ω_φ` and `ω₀` turns this into a chartwise bound on the derivatives of `φ_{jk̄}`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] in
private theorem exists_bound_of_laplacian_pair (ω₀ : KahlerForm n M) [Nonempty M]
    {u v : M → ℝ} {Λ C c : ℝ}
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ v)
    (hv_nonneg : ∀ x, 0 ≤ v x)
    (hv_le : ∀ x, v x ≤ Λ) (hC : 0 ≤ C) (hc : 0 < c)
    (hLap_u : ∀ x, -(C * u x + C) ≤ ω₀.laplacian u x)
    (hLap_v : ∀ x, c * u x - C ≤ ω₀.laplacian v x) :
    ∀ x, u x ≤ C + ((C + 1) / c) * C + ((C + 1) / c) * Λ := by
  let A : ℝ := (C + 1) / c
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (by linarith) hc.le
  have hAc : A * c = C + 1 := by
    dsimp [A]
    field_simp [ne_of_gt hc]
  have hAconst : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (fun _ : M ↦ A) :=
    contMDiff_const
  have hpoint : (fun _ : M ↦ A) • v = fun x : M ↦ A * v x := by
    funext x
    simp [smul_eq_mul]
  have hAv : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x : M ↦ A * v x) := by
    rw [← hpoint]
    exact hAconst.smul hv
  let P : M → ℝ := fun x ↦ u x + A * v x
  have hP : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ P := by
    exact hu.add hAv
  obtain ⟨x₀, hx₀, hmax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMaxOn Set.univ_nonempty
      hP.continuous.continuousOn
  have hlocal : IsLocalMax P x₀ := hmax.isLocalMax Filter.univ_mem
  have hLapP : ω₀.laplacian P x₀ =
      ω₀.laplacian u x₀ + A * ω₀.laplacian v x₀ := by
    calc
      ω₀.laplacian P x₀ = ω₀.laplacian (u + fun x ↦ A * v x) x₀ := rfl
      _ = ω₀.laplacian u x₀ + ω₀.laplacian (fun x ↦ A * v x) x₀ :=
        congrFun (ω₀.laplacian_add hu hAv) x₀
      _ = ω₀.laplacian u x₀ + A * ω₀.laplacian v x₀ := by
        have hfun : (fun x : M ↦ A * v x) = A • v := by
          funext x
          simp [smul_eq_mul]
        rw [hfun, ω₀.laplacian_smul hv A]
        simp [smul_eq_mul]
  have hLapP_nonpos := ω₀.laplacian_nonpos_of_isLocalMax hP hlocal
  have hu_max : u x₀ ≤ C + A * C := by
    have hlower : -(C * u x₀ + C) + A * (c * u x₀ - C) ≤ 0 := by
      calc
        _ ≤ ω₀.laplacian u x₀ + A * ω₀.laplacian v x₀ :=
          add_le_add (hLap_u x₀) (mul_le_mul_of_nonneg_left (hLap_v x₀) hA_nonneg)
        _ = ω₀.laplacian P x₀ := hLapP.symm
        _ ≤ 0 := hLapP_nonpos
    have hlinear : (A * c - C) * u x₀ ≤ C + A * C := by
      nlinarith [hlower]
    have hcoef : A * c - C = 1 := by rw [hAc]; ring
    rw [hcoef] at hlinear
    simpa using hlinear
  intro y
  have hu_le_P : u y ≤ P y := by
    dsimp [P]
    exact le_add_of_nonneg_right (mul_nonneg hA_nonneg (hv_nonneg y))
  have hP_le : P y ≤ P x₀ := hmax (Set.mem_univ y)
  have hP_at_max : P x₀ ≤ C + A * C + A * Λ := by
    dsimp [P]
    have hAv_le := mul_le_mul_of_nonneg_left (hv_le x₀) hA_nonneg
    nlinarith [hu_max, hAv_le]
  exact hu_le_P.trans (hP_le.trans hP_at_max)

omit [T2Space M] [CompactSpace M] in
private theorem exists_fderiv_ddbar_bound_on_compact (φ : M → ℝ) (x₀ : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) :
    ∃ C, ∀ z ∈ K,
      ‖fderiv ℝ (ddbar (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)) z‖ ≤ C := by
  have hφ_on : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ Set.univ :=
    hφ.contMDiffOn
  have hsymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target :=
    contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀
  have hchart_md : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target :=
    hφ_on.comp hsymm (fun _ _ ↦ Set.mem_univ _)
  have hchart : ContDiffOn ℝ ∞
      (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target := hchart_md.contDiffOn
  have hddbar : ContDiffOn ℝ ∞
      (ddbar (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target :=
    ContDiffOn.ddbar
      (isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀) hchart
  have hderiv : ContinuousOn
      (fderiv ℝ (ddbar (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target :=
    hddbar.continuousOn_fderiv_of_isOpen
      (isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀) (by simp)
  exact hK.exists_bound_of_continuousOn (hderiv.mono hKt)

open scoped ComplexOrder in
omit [T2Space M] [CompactSpace M] in
private theorem exists_metricInvChart_entry_bound_on_compact
    (ω₀ : KahlerForm n M) (x₀ : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :
    ∃ C, ∀ z ∈ K, ∀ j k,
      ‖(ω₀.metricInChart x₀ z)⁻¹ j k‖ ≤ C := by
  classical
  let T := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target
  have hmatrix : ContinuousOn (fun z ↦ ω₀.metricInChart x₀ z) T := by
    refine continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦ ?_
    exact (ω₀.contDiffOn_metricInChart x₀ j k).continuousOn
  have hmatrix' : Continuous (fun z : T ↦ ω₀.metricInChart x₀ z.1) :=
    continuousOn_iff_continuous_domRestrict.1 hmatrix
  have hdet : Continuous (fun z : T ↦ (ω₀.metricInChart x₀ z.1).det) :=
    hmatrix'.matrix_det
  have hadjugate : Continuous (fun z : T ↦ (ω₀.metricInChart x₀ z.1).adjugate) :=
    hmatrix'.matrix_adjugate
  have hinv_entry : ∀ j k, Continuous (fun z : T ↦ (ω₀.metricInChart x₀ z.1)⁻¹ j k) := by
    intro j k
    have hdet_ne : ∀ z : T, (ω₀.metricInChart x₀ z.1).det ≠ 0 := by
      intro z
      have hpos := ω₀.posDef_metricInChart x₀ z.2
      have hdet_pos : 0 < RCLike.re (ω₀.metricInChart x₀ z.1).det :=
        (RCLike.pos_iff.mp hpos.det_pos).1
      intro hdet_zero
      exact hdet_pos.ne' (by simp [hdet_zero])
    have hentry (z : T) : (ω₀.metricInChart x₀ z.1)⁻¹ j k =
        ((ω₀.metricInChart x₀ z.1).det)⁻¹ *
          (ω₀.metricInChart x₀ z.1).adjugate j k := by
      rw [Matrix.inv_def]
      simp [Matrix.smul_apply, Ring.inverse_eq_inv']
    have hfun : (fun z : T ↦ (ω₀.metricInChart x₀ z.1)⁻¹ j k) =
        fun z ↦ ((ω₀.metricInChart x₀ z.1).det)⁻¹ *
          (ω₀.metricInChart x₀ z.1).adjugate j k := by
      funext z
      exact hentry z
    rw [hfun]
    exact (hdet.inv₀ hdet_ne).mul (hadjugate.matrix_elem j k)
  have hinv : ContinuousOn (fun z ↦ (ω₀.metricInChart x₀ z)⁻¹) T := by
    refine continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦ ?_
    exact continuousOn_iff_continuous_domRestrict.2 (hinv_entry j k)
  have hentry_bound : ∀ j k, ∃ C, ∀ z ∈ K,
      ‖(ω₀.metricInChart x₀ z)⁻¹ j k‖ ≤ C := by
    intro j k
    have hentry_cont : ContinuousOn (fun z ↦ (ω₀.metricInChart x₀ z)⁻¹ j k) T :=
      (continuousOn_pi.1 (continuousOn_pi.1 hinv j) k)
    exact hK.exists_bound_of_continuousOn (hentry_cont.mono hKt)
  let Cjk : Fin n × Fin n → ℝ := fun jk ↦ Classical.choose (hentry_bound jk.1 jk.2)
  have hCjk (jk : Fin n × Fin n) : ∀ z ∈ K,
      ‖(ω₀.metricInChart x₀ z)⁻¹ jk.1 jk.2‖ ≤ Cjk jk :=
    Classical.choose_spec (hentry_bound jk.1 jk.2)
  obtain ⟨C, hC⟩ := (Set.finite_range Cjk).bddAbove
  refine ⟨C, ?_⟩
  intro z hz j k
  exact (hCjk (j, k) z hz).trans (hC (Set.mem_range_self (j, k)))

private theorem fderiv_second_apply_comm {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z a b c : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 3 f z) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a b) z c =
      fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b a) z c := by
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w a b
  let r : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w b a
  have hfd1 : ContDiffAt ℝ 2 (fderiv ℝ f) z := hf.fderiv_right (m := 2) (by norm_num)
  have hfd2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) z :=
    hfd1.fderiv_right (m := 1) (by norm_num)
  have hqcont : ContDiffAt ℝ 1 q z := by
    dsimp [q]
    exact (hfd2.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hrcont : ContDiffAt ℝ 1 r z := by
    dsimp [r]
    exact (hfd2.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hq : HasFDerivAt q (fderiv ℝ q z) z :=
    (hqcont.differentiableAt (by norm_num)).hasFDerivAt
  have hr : HasFDerivAt r (fderiv ℝ r z) z :=
    (hrcont.differentiableAt (by norm_num)).hasFDerivAt
  have hsymm := hf.eventually (by norm_num : (3 : ℕ∞ω) ≠ ∞)
  have heq : q =ᶠ[nhds z] r := by
    filter_upwards [hsymm] with w hw
    exact hw.isSymmSndFDerivAt (by norm_num) a b
  have hq' := hq.congr_of_eventuallyEq heq.symm
  have hderivEq : fderiv ℝ q z = fderiv ℝ r z := hq'.unique hr
  exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L c) hderivEq

private theorem fderiv_second_apply_comm_outer {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z a b c : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 3 f z) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a b) z c =
      fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w c b) z a := by
  let F2 : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ :=
    fun w ↦ fderiv ℝ (fderiv ℝ f) w
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ F2 w a b
  let r : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ F2 w c b
  have hfd1 : ContDiffAt ℝ 2 (fderiv ℝ f) z := hf.fderiv_right (m := 2) (by norm_num)
  have hfd2 : ContDiffAt ℝ 1 F2 z := by
    simpa [F2] using hfd1.fderiv_right (m := 1) (by norm_num)
  have hF2 : HasFDerivAt F2 (fderiv ℝ F2 z) z :=
    (hfd2.differentiableAt (by norm_num)).hasFDerivAt
  have hq := (hF2.clm_apply (hasFDerivAt_const a z)).clm_apply (hasFDerivAt_const b z)
  have hr := (hF2.clm_apply (hasFDerivAt_const c z)).clm_apply (hasFDerivAt_const b z)
  have hqder (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ q z u = (fderiv ℝ F2 z u a) b := by
    have hq' := hq.fderiv
    simpa [q, F2] using congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L u) hq'
  have hrder (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ r z u = (fderiv ℝ F2 z u c) b := by
    have hr' := hr.fderiv
    simpa [r, F2] using congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L u) hr'
  have hSymm : IsSymmSndFDerivAt ℝ (fderiv ℝ f) z :=
    hfd1.isSymmSndFDerivAt (by norm_num)
  have hthird : (fderiv ℝ F2 z c a) b = (fderiv ℝ F2 z a c) b := by
    exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L b) (hSymm c a)
  calc
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a b) z c = fderiv ℝ q z c := by
      rfl
    _ = (fderiv ℝ F2 z c a) b := hqder c
    _ = (fderiv ℝ F2 z a c) b := hthird
    _ = fderiv ℝ r z a := (hrder a).symm
    _ = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w c b) z a := by rfl

private theorem fderiv_second_apply_cyclic {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z a b c : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 3 f z) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a b) z c =
      fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b c) z a := by
  calc
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a b) z c =
        fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b a) z c :=
      fderiv_second_apply_comm hf
    _ = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w c a) z b :=
      fderiv_second_apply_comm_outer hf
    _ = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a c) z b :=
      fderiv_second_apply_comm hf
    _ = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b c) z a :=
      fderiv_second_apply_comm_outer hf

private theorem fderiv_second_directionalDerivative {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z a b v : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 3 f z) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b v) z a =
      fderiv ℝ (fderiv ℝ (fun w ↦ fderiv ℝ f w v)) z a b := by
  let g : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ f w v
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w b v
  let r : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ g w b
  have hfd1 : ContDiffAt ℝ 2 (fderiv ℝ f) z := hf.fderiv_right (m := 2) (by norm_num)
  have hfd2 : ContDiffAt ℝ 1 (fun w ↦ fderiv ℝ (fderiv ℝ f) w) z :=
    hfd1.fderiv_right (m := 1) (by norm_num)
  have hg : ContDiffAt ℝ 2 g z := by
    exact hfd1.clm_apply contDiffAt_const
  have hqcont : ContDiffAt ℝ 1 q z := by
    dsimp [q]
    exact (hfd2.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hrcont : ContDiffAt ℝ 1 r z := by
    exact hg.fderiv_right (m := 1) (by norm_num) |>.clm_apply contDiffAt_const
  have hq : HasFDerivAt q (fderiv ℝ q z) z :=
    (hqcont.differentiableAt (by norm_num)).hasFDerivAt
  have hr : HasFDerivAt r (fderiv ℝ r z) z :=
    (hrcont.differentiableAt (by norm_num)).hasFDerivAt
  have hsame : q =ᶠ[nhds z] r := by
    filter_upwards [hf.eventually (by norm_num : (3 : ℕ∞ω) ≠ ∞)] with w hw
    have hF1 : DifferentiableAt ℝ (fderiv ℝ f) w :=
      (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hconst : DifferentiableAt ℝ (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) w :=
      differentiableAt_const _
    have h := fderiv_clm_apply hF1 hconst
    change fderiv ℝ (fderiv ℝ f) w b v = fderiv ℝ g w b
    rw [h]
    simp
  have hq' := hq.congr_of_eventuallyEq hsame.symm
  have hderivEq : fderiv ℝ q z = fderiv ℝ r z := hq'.unique hr
  have hrg : fderiv ℝ r z a = fderiv ℝ (fderiv ℝ g) z a b := by
    have hG : DifferentiableAt ℝ (fderiv ℝ g) z :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    rw [fderiv_clm_apply hG (differentiableAt_const b)]
    simp
  calc
    fderiv ℝ q z a = fderiv ℝ r z a := congrArg (fun L :
      EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L a) hderivEq
    _ = fderiv ℝ (fderiv ℝ g) z a b := hrg
    _ = fderiv ℝ (fderiv ℝ (fun w ↦ fderiv ℝ f w v)) z a b := by rfl

private theorem fderiv_complexHessian_direction {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z v : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 3 f z) (j k : Fin n) :
    fderiv ℝ (fun w ↦ complexHessian f w j k) z v =
      complexHessian (fun w ↦ fderiv ℝ f w v) z j k := by
  let a : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let b : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single k 1
  let ia := Complex.I • a
  let ib := Complex.I • b
  let g : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ f w v
  let q₁ : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w a b
  let q₂ : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w ia ib
  let q₃ : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w a ib
  let q₄ : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w ia b
  let S : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦
    (4 : ℂ)⁻¹ * ((q₁ w : ℂ) + q₂ w + Complex.I * ((q₃ w : ℂ) - q₄ w))
  let D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ := (4 : ℂ)⁻¹ •
    (Complex.ofRealCLM.comp (fderiv ℝ q₁ z) +
      Complex.ofRealCLM.comp (fderiv ℝ q₂ z) +
      Complex.I • (Complex.ofRealCLM.comp (fderiv ℝ q₃ z) -
        Complex.ofRealCLM.comp (fderiv ℝ q₄ z)))
  have hfd1 : ContDiffAt ℝ 2 (fderiv ℝ f) z := hf.fderiv_right (m := 2) (by norm_num)
  have hfd2 : ContDiffAt ℝ 1 (fun w ↦ fderiv ℝ (fderiv ℝ f) w) z :=
    hfd1.fderiv_right (m := 1) (by norm_num)
  have hg : ContDiffAt ℝ 2 g z :=
    hfd1.clm_apply (contDiffAt_const (x := z) (c := v))
  have hq₁ : HasFDerivAt q₁ (fderiv ℝ q₁ z) z := by
    have hc := (hfd2.clm_apply (contDiffAt_const (x := z) (c := a))).clm_apply
      (contDiffAt_const (x := z) (c := b))
    simpa [q₁] using (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hq₂ : HasFDerivAt q₂ (fderiv ℝ q₂ z) z := by
    have hc := (hfd2.clm_apply (contDiffAt_const (x := z) (c := ia))).clm_apply
      (contDiffAt_const (x := z) (c := ib))
    simpa [q₂] using (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hq₃ : HasFDerivAt q₃ (fderiv ℝ q₃ z) z := by
    have hc := (hfd2.clm_apply (contDiffAt_const (x := z) (c := a))).clm_apply
      (contDiffAt_const (x := z) (c := ib))
    simpa [q₃] using (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hq₄ : HasFDerivAt q₄ (fderiv ℝ q₄ z) z := by
    have hc := (hfd2.clm_apply (contDiffAt_const (x := z) (c := ia))).clm_apply
      (contDiffAt_const (x := z) (c := b))
    simpa [q₄] using (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hq₁c : HasFDerivAt (fun w ↦ (q₁ w : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ q₁ z)) z := by
    have hCLM : HasFDerivAt Complex.ofRealCLM Complex.ofRealCLM (q₁ z) :=
      Complex.ofRealCLM.hasFDerivAt
    simpa [Function.comp_def] using HasFDerivAt.comp z hCLM hq₁
  have hq₂c : HasFDerivAt (fun w ↦ (q₂ w : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ q₂ z)) z := by
    have hCLM : HasFDerivAt Complex.ofRealCLM Complex.ofRealCLM (q₂ z) :=
      Complex.ofRealCLM.hasFDerivAt
    simpa [Function.comp_def] using HasFDerivAt.comp z hCLM hq₂
  have hq₃c : HasFDerivAt (fun w ↦ (q₃ w : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ q₃ z)) z := by
    have hCLM : HasFDerivAt Complex.ofRealCLM Complex.ofRealCLM (q₃ z) :=
      Complex.ofRealCLM.hasFDerivAt
    simpa [Function.comp_def] using HasFDerivAt.comp z hCLM hq₃
  have hq₄c : HasFDerivAt (fun w ↦ (q₄ w : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ q₄ z)) z := by
    have hCLM : HasFDerivAt Complex.ofRealCLM Complex.ofRealCLM (q₄ z) :=
      Complex.ofRealCLM.hasFDerivAt
    simpa [Function.comp_def] using HasFDerivAt.comp z hCLM hq₄
  have h34 := (hq₃c.sub hq₄c).const_mul Complex.I
  have h1234 := (hq₁c.add hq₂c).add h34
  have hdiv := h1234.const_mul (4 : ℂ)⁻¹
  have hS : HasFDerivAt S D z := by
    change HasFDerivAt (fun w : EuclideanSpace ℂ (Fin n) ↦
      (4 : ℂ)⁻¹ * ((q₁ w : ℂ) + q₂ w + Complex.I * ((q₃ w : ℂ) - q₄ w))) D z
    exact hdiv
  have hEq : (fun w ↦ complexHessian f w j k) =ᶠ[nhds z] S := by
    filter_upwards [hf.eventually (by norm_num : (3 : ℕ∞ω) ≠ ∞)] with w hw
    have hw2 : ContDiffAt ℝ 2 f w := hw.of_le (by norm_num)
    rw [complexHessian_apply hw2 j k]
    simp only [S, q₁, q₂, q₃, q₄, a, b, ia, ib, div_eq_mul_inv]
    ring
  have hComplex := hS.congr_of_eventuallyEq hEq
  have hleft : fderiv ℝ (fun w ↦ complexHessian f w j k) z v = D v :=
    congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hComplex.fderiv
  have hq₁eq : fderiv ℝ q₁ z v = fderiv ℝ (fderiv ℝ g) z a b := by
    calc
      fderiv ℝ q₁ z v = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b v) z a := by
        exact fderiv_second_apply_cyclic hf
      _ = fderiv ℝ (fderiv ℝ g) z a b := by
        simpa [q₁, g] using fderiv_second_directionalDerivative
          (f := f) (z := z) (a := a) (b := b) (v := v) hf
  have hq₂eq : fderiv ℝ q₂ z v = fderiv ℝ (fderiv ℝ g) z ia ib := by
    calc
      fderiv ℝ q₂ z v = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w ib v) z ia := by
        exact fderiv_second_apply_cyclic hf
      _ = fderiv ℝ (fderiv ℝ g) z ia ib := by
        simpa [q₂, g] using fderiv_second_directionalDerivative
          (f := f) (z := z) (a := ia) (b := ib) (v := v) hf
  have hq₃eq : fderiv ℝ q₃ z v = fderiv ℝ (fderiv ℝ g) z a ib := by
    calc
      fderiv ℝ q₃ z v = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w ib v) z a := by
        exact fderiv_second_apply_cyclic hf
      _ = fderiv ℝ (fderiv ℝ g) z a ib := by
        simpa [q₃, g] using fderiv_second_directionalDerivative
          (f := f) (z := z) (a := a) (b := ib) (v := v) hf
  have hq₄eq : fderiv ℝ q₄ z v = fderiv ℝ (fderiv ℝ g) z ia b := by
    calc
      fderiv ℝ q₄ z v = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b v) z ia := by
        exact fderiv_second_apply_cyclic hf
      _ = fderiv ℝ (fderiv ℝ g) z ia b := by
        simpa [q₄, g] using fderiv_second_directionalDerivative
          (f := f) (z := z) (a := ia) (b := b) (v := v) hf
  have hright : D v = complexHessian g z j k := by
    rw [complexHessian_apply hg j k]
    simp [D, Complex.ofRealCLM_apply, hq₁eq, hq₂eq, hq₃eq, hq₄eq, a, b, ia, ib]
    ring_nf
  exact hleft.trans hright

/-- **Calabi's third-order estimate.** For a family of solutions with `G` bounded in `C³` and
`tr_ω₀ ω_φ` bounded, the complex Hessians `i∂∂̄φ` are uniformly bounded in `C¹` in every chart. -/
theorem exists_fderiv_ddbar_le_of_solvesMongeAmpere (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S))
    {Λ : ℝ} (hΛ : ∀ p ∈ S, ∀ x, relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ Λ)
    (x₀ : M) (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :
    ∃ C : ℝ, ∀ p ∈ S, ∀ z ∈ K,
      ‖fderiv ℝ (ddbar (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)) z‖ ≤ C := by
  classical
  by_cases hK_nonempty : K.Nonempty
  · by_cases hS_nonempty : S.Nonempty
    · by_cases hn : n = 0
      · subst n
        refine ⟨0, ?_⟩
        intro p hp z hz
        simp
      · by_cases hΛpos : 0 < Λ
        · by_cases hS_sub : S.Subsingleton
          · obtain ⟨p₀, hp₀⟩ := hS_nonempty
            have hφsmooth :
                ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p₀.2 :=
              (hS p₀ hp₀).2.1.1
            obtain ⟨C, hC⟩ :=
              exists_fderiv_ddbar_bound_on_compact p₀.2 x₀ K hK hKt hφsmooth
            refine ⟨C, ?_⟩
            intro p hp z hz
            have hp_eq : p = p₀ := hS_sub hp hp₀
            subst p
            exact hC z hz
          · by_cases hS_finite : S.Finite
            · have hEach : ∀ p ∈ S, ∃ C, ∀ z ∈ K,
                  ‖fderiv ℝ (ddbar
                    (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)) z‖ ≤ C := by
                intro p hp
                exact exists_fderiv_ddbar_bound_on_compact p.2 x₀ K hK hKt
                  (hS p hp).2.1.1
              let c : (M → ℝ) × (M → ℝ) → ℝ := fun p ↦
                if hp : p ∈ S then Classical.choose (hEach p hp) else 0
              have hc : ∀ p ∈ S, ∀ z ∈ K,
                  ‖fderiv ℝ (ddbar
                    (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)) z‖ ≤ c p := by
                intro p hp z hz
                dsimp [c]
                rw [dite_eq_left hp]
                exact (Classical.choose_spec (hEach p hp)) z hz
              have hc_finite : (c '' S).Finite := hS_finite.image c
              obtain ⟨C, hC⟩ := hc_finite.bddAbove
              refine ⟨C, ?_⟩
              intro p hp z hz
              exact (hc p hp z hz).trans (hC (Set.mem_image_of_mem c hp))
            · obtain ⟨p₀, hp₀⟩ := hS_nonempty
              by_cases hS_const : ∀ p ∈ S, ∃ c, ∀ x, p.2 x = p₀.2 x + c
              ·
                obtain ⟨C, hC⟩ := exists_fderiv_ddbar_bound_on_compact p₀.2 x₀ K hK hKt
                  (hS p₀ hp₀).2.1.1
                refine ⟨C, ?_⟩
                intro p hp z hz
                obtain ⟨c, hc⟩ := hS_const p hp
                have hfun : p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm =
                    fun y ↦ (p₀.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) y + c := by
                  funext y
                  exact hc ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm y)
                have hddbar_eq :
                    ddbar (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) =
                      ddbar (p₀.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) := by
                  rw [hfun]
                  funext y
                  exact ddbar_add_const c
                rw [hddbar_eq]
                exact hC z hz
              · by_cases hS_modFinite : ∃ R : Set ((M → ℝ) × (M → ℝ)), R.Finite ∧
                    R ⊆ S ∧ ∀ p ∈ S, ∃ r ∈ R, ∃ c, ∀ x, p.2 x = r.2 x + c
                · obtain ⟨R, hR_finite, hR_sub, hR_repr⟩ := hS_modFinite
                  have hEach : ∀ r ∈ R, ∃ C, ∀ z ∈ K,
                      ‖fderiv ℝ (ddbar
                        (r.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)) z‖ ≤ C := by
                    intro r hr
                    exact exists_fderiv_ddbar_bound_on_compact r.2 x₀ K hK hKt
                      (hS r (hR_sub hr)).2.1.1
                  let c : (M → ℝ) × (M → ℝ) → ℝ := fun r ↦
                    if hr : r ∈ R then Classical.choose (hEach r hr) else 0
                  have hc : ∀ r ∈ R, ∀ z ∈ K,
                      ‖fderiv ℝ (ddbar
                        (r.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)) z‖ ≤ c r := by
                    intro r hr z hz
                    dsimp [c]
                    rw [dite_eq_left hr]
                    exact (Classical.choose_spec (hEach r hr)) z hz
                  have hc_finite : (c '' R).Finite := hR_finite.image c
                  obtain ⟨C, hC⟩ := hc_finite.bddAbove
                  refine ⟨C, ?_⟩
                  intro p hp z hz
                  obtain ⟨r, hr, c₀, hp_eq⟩ := hR_repr p hp
                  have hfun : p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm =
                      fun y ↦ (r.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) y + c₀ := by
                    funext y
                    exact hp_eq ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm y)
                  have hddbar_eq :
                      ddbar (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) =
                        ddbar (r.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) := by
                    rw [hfun]
                    funext y
                    exact ddbar_add_const c₀
                  rw [hddbar_eq]
                  exact (hc r hr z hz).trans (hC (Set.mem_image_of_mem c hr))
                · obtain ⟨D, hDpos, hD⟩ :=
                    exists_uniform_relTrace_equivalence ω₀ S hS hG hΛ
                  have hMetric : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S, ∀ x,
                      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B ∧
                      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B :=
                    ⟨D, hDpos, hD⟩
                  obtain ⟨Ce, hCe, hEnergyLap⟩ :=
                    exists_uniform_calabi_energy_laplacian_lower ω₀ S hS hG hMetric
                  obtain ⟨c, Ct, hc, hCt, hTrace⟩ :=
                    exists_uniform_relTrace_laplacian_calabi_lower ω₀ S hS hG hMetric
                  let C : ℝ := max Ce Ct
                  have hC : 0 ≤ C := hCe.trans (le_max_left _ _)
                  have hEnergySmooth : ∀ p ∈ S,
                      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
                        (calabiEnergy ω₀ p.2) := by
                    intro p hp
                    exact (calabiEnergy_chartFormula_is_intrinsic ω₀ p.2 p.1
                      (hS p hp).2.1.1 (hS p hp).2).1
                  have hEnergyNonneg : ∀ p ∈ S, ∀ x, 0 ≤ calabiEnergy ω₀ p.2 x := by
                    intro p hp x
                    exact (calabiEnergy_chartFormula_is_intrinsic ω₀ p.2 p.1
                      (hS p hp).2.1.1 (hS p hp).2).2.2 x
                  let B : ℝ := C + ((C + 1) / c) * C + ((C + 1) / c) * D
                  have hBound : ∀ p ∈ S, ∀ x, calabiEnergy ω₀ p.2 x ≤ B := by
                    let : Nonempty M := ⟨x₀⟩
                    intro p hp x
                    let α := ω₀.perturb p.2 (hS p hp).2.1
                    let u := calabiEnergy ω₀ p.2
                    let v : M → ℝ := fun y ↦
                      relTrace (ω₀ y) (ω₀ y + mddbar n p.2 y)
                    have hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ v :=
                      (hTrace p hp).1
                    have hLap_u : ∀ y, -(C * u y + C) ≤ α.laplacian u y := by
                      intro y
                      have hmul : Ce * (u y + 1) ≤ C * (u y + 1) :=
                        mul_le_mul_of_nonneg_right (le_max_left Ce Ct)
                          (by dsimp [u]; linarith [hEnergyNonneg p hp y])
                      have h := hEnergyLap p hp y
                      dsimp [α, u] at *
                      nlinarith
                    have hLap_v : ∀ y, c * u y - C ≤ α.laplacian v y := by
                      intro y
                      have h := (hTrace p hp).2.2 y
                      have hCtC : Ct ≤ C := le_max_right Ce Ct
                      dsimp [α, u, v] at *
                      linarith
                    exact exists_bound_of_laplacian_pair α (hEnergySmooth p hp) hv
                      (hTrace p hp).2.1 (fun y ↦ (hD p hp y).1) hC hc
                      hLap_u hLap_v x
                  exact exists_uniform_fderiv_ddbar_bound_of_calabiEnergy ω₀ S hS
                    hMetric B hBound x₀ K hK hKt
        · let : NeZero n := ⟨hn⟩
          exfalso
          obtain ⟨p, hp⟩ := hS_nonempty
          have hsol := (hS p hp).2
          have hα : (ω₀ x₀ + mddbar n p.2 x₀).IsPositive := by
            simpa [KahlerForm.perturb_apply] using hsol.1.2 x₀
          have htrace : 0 < relTrace (ω₀ x₀) (ω₀ x₀ + mddbar n p.2 x₀) :=
            relTrace_pos (ω₀.isPositive x₀) hα
          have hbound := hΛ p hp x₀
          exact hΛpos (lt_of_lt_of_le htrace hbound)
    · refine ⟨0, ?_⟩
      intro p hp z hz
      exact (hS_nonempty ⟨p, hp⟩).elim
  · refine ⟨0, ?_⟩
    intro p hp z hz
    exact (hK_nonempty ⟨z, hz⟩).elim

end KahlerForm
