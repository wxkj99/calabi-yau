module

public import CalabiYau.Geometry.Kahler.Laplacian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

open scoped Manifold ContDiff Topology
open Complex Filter ContinuousAlternatingMap
namespace KahlerForm

public theorem laplacian_log_of_contDiffAt_inChart {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] (ω₀ : KahlerForm n M) {f : M → ℝ}
    (x : M)
    (hf : ContDiffAt ℝ 2 (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)) (hx : f x ≠ 0) :
    ω₀.laplacian (fun y ↦ Real.log (f y)) x =
      ω₀.laplacian f x / f x - ω₀.gradNormSq f x / (f x) ^ 2 := by
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let ψ := extChartAt I x
  let z := ψ x
  let F := f ∘ ψ.symm
  have hzsource : x ∈ ψ.source := by simp [ψ, I]
  have hpoint : ψ.symm z = x := ψ.left_inv hzsource
  have hF : F z = f x := by simp [F, z, hpoint]
  have hFne : F z ≠ 0 := by simpa [hF] using hx
  have hfz : ContDiffAt ℝ 2 F z := by simpa [F, ψ, I, z] using hf
  have hh : ContDiffAt ℝ 2 Real.log (F z) := Real.contDiffAt_log.2 hFne
  have hderiv : deriv Real.log = fun t : ℝ ↦ t⁻¹ := by
    funext t
    exact Real.deriv_log t
  have hsecond : deriv (deriv Real.log) (F z) = -((F z) ^ 2)⁻¹ := by
    rw [hderiv]
    exact deriv_inv
  have hlogddbar : ddbar (Real.log ∘ F) z =
      (F z)⁻¹ • ddbar F z + (-((F z) ^ 2)⁻¹) • dWedgeDBar (fderiv ℝ F z) := by
    have hF' : DifferentiableAt ℝ (fderiv ℝ F) z :=
      (hfz.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hh' : DifferentiableAt ℝ (fderiv ℝ Real.log) (F z) :=
      (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hF0 : DifferentiableAt ℝ F z := hfz.differentiableAt (by norm_num)
    let c : EuclideanSpace ℂ (Fin n) → ℝ →L[ℝ] ℝ := fun w ↦ fderiv ℝ Real.log (F w)
    let d : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ := fun w ↦
      fderiv ℝ F w
    have hc : DifferentiableAt ℝ c z := hh'.comp z hF0
    have hd : DifferentiableAt ℝ d z := hF'
    have hcderiv : fderiv ℝ c z =
        (fderiv ℝ (fderiv ℝ Real.log) (F z)).comp (fderiv ℝ F z) := by
      dsimp [c]
      exact fderiv_comp (f := F) (g := fderiv ℝ Real.log) (x := z) hh' hF0
    have hhpre : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 Real.log (F w) := by
      filter_upwards [hfz.continuousAt.preimage_mem_nhds (hh.eventually (by norm_num))]
        with w hw
      change ContDiffAt ℝ 2 Real.log (F w) at hw
      exact hw
    have hfirst : fderiv ℝ (Real.log ∘ F) =ᶠ[𝓝 z] fun w ↦ (c w).comp (d w) := by
      filter_upwards [hfz.eventually (by norm_num), hhpre] with w hwf hhw
      simpa [c, d] using
        (fderiv_comp (f := F) (g := Real.log) (x := w)
          (hhw.differentiableAt (by norm_num)) (hwf.differentiableAt (by norm_num)))
    have hderiv_diff : DifferentiableAt ℝ (deriv Real.log) (F z) := by
      change DifferentiableAt ℝ (fun y ↦ fderiv ℝ Real.log y 1) (F z)
      exact hh'.clm_apply (differentiableAt_const _)
    have hHesslog (r s : ℝ) :
        fderiv ℝ (fderiv ℝ Real.log) (F z) r s =
          deriv (deriv Real.log) (F z) * r * s := by
      have hEval :
          fderiv ℝ (fun y ↦ fderiv ℝ Real.log y s) (F z) r =
            fderiv ℝ (fderiv ℝ Real.log) (F z) r s := by
        rw [fderiv_clm_apply hh' (differentiableAt_const s)]
        simp
      have hEvalFun : (fun y : ℝ ↦ fderiv ℝ Real.log y s) =
          (fun y ↦ deriv Real.log y * s) := by
        funext y
        exact fderiv_eq_deriv_mul
      calc
        fderiv ℝ (fderiv ℝ Real.log) (F z) r s =
            fderiv ℝ (fun y : ℝ ↦ fderiv ℝ Real.log y s) (F z) r := hEval.symm
        _ = fderiv ℝ (fun y : ℝ ↦ deriv Real.log y * s) (F z) r := by rw [hEvalFun]
        _ = deriv (deriv Real.log) (F z) * r * s := by
          rw [fderiv_mul_const hderiv_diff s]
          rw [_root_.smul_apply, fderiv_eq_deriv_mul]
          ring
    have hderiv2_apply (s : ℝ) :
        deriv (fderiv ℝ Real.log) (F z) s = deriv (deriv Real.log) (F z) * s := by
      rw [← fderiv_apply_one_eq_deriv, hHesslog]
      simp
    have hHcomp (a b : EuclideanSpace ℂ (Fin n)) :
        fderiv ℝ (fderiv ℝ (Real.log ∘ F)) z a b =
          deriv Real.log (F z) * fderiv ℝ (fderiv ℝ F) z a b +
            deriv (deriv Real.log) (F z) * (fderiv ℝ F z a) * (fderiv ℝ F z b) := by
      rw [hfirst.fderiv_eq, fderiv_clm_comp hc hd, hcderiv]
      simp [ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
      simp [c, d, hderiv2_apply, mul_comm, mul_left_comm]
    have hlogC2 : ContDiffAt ℝ 2 (Real.log ∘ F) z := hh.comp z hfz
    ext u
    have hu : u = ![u 0, u 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hu]
    change ddbar (Real.log ∘ F) z ![u 0, u 1] =
      ((F z)⁻¹ • ddbar F z + (-((F z) ^ 2)⁻¹) • dWedgeDBar (fderiv ℝ F z)) ![u 0, u 1]
    rw [ddbar_apply hlogC2 (u 0) (u 1), ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      ddbar_apply hfz (u 0) (u 1), hHcomp (Complex.I • u 0) (u 1),
      hHcomp (u 0) (Complex.I • u 1)]
    have hwedge : (dWedgeDBar (fderiv ℝ F z)) ![u 0, u 1] =
        (fderiv ℝ F z (Complex.I • u 0) * fderiv ℝ F z (u 1) -
          fderiv ℝ F z (Complex.I • u 1) * fderiv ℝ F z (u 0)) / 2 := by
      let ℓ := fderiv ℝ F z
      change ((1 / 2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
        ((ℓ.comp (Complex.I • ContinuousLinearMap.id ℝ
          (EuclideanSpace ℂ (Fin n)))).smulRight
          (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) ℓ))) ![u 0, u 1] = _
      simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.removeNth]
      ring
    rw [hwedge, hderiv, deriv_inv]
    ring_nf
  change ContinuousAlternatingMap.relTrace (ω₀ x) (ddbar (Real.log ∘ F) z) = _
  rw [hlogddbar, ContinuousAlternatingMap.relTrace_add,
    ContinuousAlternatingMap.relTrace_smul]
  rw [KahlerForm.laplacian, KahlerForm.gradNormSq, mddbar, mdWedgeDBar]
  rw [ContinuousAlternatingMap.relTrace_smul]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [← hF]
  ring

end KahlerForm
