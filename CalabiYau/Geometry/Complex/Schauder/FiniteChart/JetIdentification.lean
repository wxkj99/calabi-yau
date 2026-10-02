module

public import CalabiYau.Geometry.Complex.Schauder.SecondJetLimit

/-!
# Identifying uniformly convergent jets on nested balls

This is the derivative-identification step of GT, Lemma 6.36, p. 136, as implemented
locally in `SecondJetLimit`. The latter's public theorem preserves a Hölder bound but does
not export the raw-jet identification needed here. Uniform limits of derivatives are identified
using `hasFDerivAt_of_tendstoLocallyUniformlyOn`, first for values and then for the first jet.
-/

set_option autoImplicit false

@[expose] public section

open Filter
open scoped ContDiff Topology

namespace KahlerForm

private theorem finiteDimensional_iteratedCML
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) :
    FiniteDimensional ℝ (E [×k]→L[ℝ] ℝ) := by
  induction k with
  | zero =>
      exact Module.Finite.equiv
        (continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.symm
  | succ k ih =>
      have : FiniteDimensional ℝ (E →L[ℝ] (E [×k]→L[ℝ] ℝ)) := by infer_instance
      exact Module.Finite.equiv
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ).toLinearEquiv.symm

private theorem secondJetLimit_approximant_jet_continuous
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)} {R S : ℝ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {j : ℕ}
    (hR : R < S) (hsmooth : ContDiffOn ℝ 2 u (Metric.ball center S)) (hj : j ≤ 2) :
    ContinuousOn (iteratedFDeriv ℝ j u) (Metric.closedBall center R) := by
  have hopen : IsOpen (Metric.ball center S) := Metric.isOpen_ball
  have hwithin : ContinuousOn (iteratedFDerivWithin ℝ j u (Metric.ball center S))
      (Metric.ball center S) :=
    hsmooth.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hopen.uniqueDiffOn
  have heq : Set.EqOn (iteratedFDerivWithin ℝ j u (Metric.ball center S))
      (iteratedFDeriv ℝ j u) (Metric.ball center S) := by
    intro x hx
    apply iteratedFDerivWithin_eq_iteratedFDeriv hopen.uniqueDiffOn
    · exact (hsmooth.contDiffAt (hopen.mem_nhds hx)).of_le (by exact_mod_cast hj)
    · exact hx
  exact (hwithin.congr heq.symm).mono (Metric.closedBall_subset_ball hR)

private theorem secondJetLimit_uniform_limit_jet_continuous
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)} {R S : ℝ}
    {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ} {φ : ℕ → ℕ} {j : ℕ}
    (hR : R < S) (hj : j ≤ 2)
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    {g : Metric.closedBall center R → EuclideanSpace ℂ (Fin n) [×j]→L[ℝ] ℝ}
    (hconv : TendstoUniformly
      (fun m (x : Metric.closedBall center R) =>
        iteratedFDeriv ℝ j (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g atTop) :
    Continuous g := by
  have hseq : ∀ m, Continuous (fun x : Metric.closedBall center R =>
      iteratedFDeriv ℝ j (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) := by
    intro m
    apply continuousOn_iff_continuous_domRestrict.mp
    exact secondJetLimit_approximant_jet_continuous hR (hsmooth (φ m)) hj
  exact hconv.continuous (Filter.Frequently.of_forall hseq)

private theorem secondJetLimit_first_derivative_compatibility
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)}
    {R S : ℝ} {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {φ : ℕ → ℕ}
    (hS : R < S)
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    {g₀ : Metric.closedBall center R → ℝ}
    {g₁ : Metric.closedBall center R →
      EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ}
    (hvalues : ∀ x : Metric.closedBall center R, g₀ x = f (x : EuclideanSpace ℂ (Fin n)))
    (h₀ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      u (φ m) (x : EuclideanSpace ℂ (Fin n))) g₀ atTop)
    (h₁ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 1 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₁ atTop) :
    ∀ (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball center R),
      HasFDerivAt f
        (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (g₁ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩)) x := by
  classical
  intro x hx
  let hxR : x ∈ Metric.closedBall center R :=
    Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))
  let G₁ : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ := fun y =>
    if hy : y ∈ Metric.closedBall center R then
      continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ (g₁ ⟨y, hy⟩)
    else 0
  have hcurrylip : LipschitzWith 1
      (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [(continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ).dist_map]
    simp
  have h₁curry : TendstoUniformly
      (fun m (y : Metric.closedBall center R) =>
        continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (iteratedFDeriv ℝ 1 (u (φ m)) (y : EuclideanSpace ℂ (Fin n))))
      (fun y => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ (g₁ y)) atTop :=
    hcurrylip.uniformContinuous.comp_tendstoUniformly h₁
  have h₁on : TendstoUniformlyOn
      (fun m y => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        (iteratedFDeriv ℝ 1 (u (φ m)) y)) G₁ atTop (Metric.closedBall center R) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have htarget : (fun y : Metric.closedBall center R => G₁ (y : EuclideanSpace ℂ (Fin n))) =
        (fun y => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ (g₁ y)) := by
      funext y
      simp only [G₁, dif_pos y.property]
    change TendstoUniformly _ (fun y : Metric.closedBall center R => G₁ (y : EuclideanSpace ℂ (Fin n))) atTop
    rw [htarget]
    exact h₁curry
  have h₁loc : TendstoLocallyUniformlyOn
      (fun m y => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        (iteratedFDeriv ℝ 1 (u (φ m)) y)) G₁ atTop (Metric.ball center R) :=
    h₁on.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall
  have hfg : ∀ y ∈ Metric.ball center R,
      Tendsto (fun m => u (φ m) y) atTop (𝓝 (f y)) := by
    intro y hy
    let hyR : y ∈ Metric.closedBall center R :=
      Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hy))
    simpa [hvalues ⟨y, hyR⟩] using h₀.tendsto_at ⟨y, hyR⟩
  have hder : ∀ m y, y ∈ Metric.ball center R →
      HasFDerivAt (u (φ m))
        (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (iteratedFDeriv ℝ 1 (u (φ m)) y)) y := by
    intro m y hy
    have hyS : y ∈ Metric.ball center S :=
      Metric.ball_subset_ball hS.le hy
    have hAt : ContDiffAt ℝ 2 (u (φ m)) y :=
      (hsmooth (φ m)).contDiffAt (Metric.isOpen_ball.mem_nhds hyS)
    have hdiff := hAt.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
    have hhas := hdiff.hasFDerivAt
    have hEq : fderiv ℝ (u (φ m)) y =
        continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (iteratedFDeriv ℝ 1 (u (φ m)) y) := by
      ext v
      simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    rw [hEq] at hhas
    exact hhas
  simpa only [G₁, dif_pos hxR] using
    hasFDerivAt_of_tendstoLocallyUniformlyOn Metric.isOpen_ball h₁loc hder hfg hx

private theorem secondJetLimit_second_derivative_compatibility
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)}
    {R S : ℝ} {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {φ : ℕ → ℕ}
    (hS : R < S)
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    {g₁ : Metric.closedBall center R →
      EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ}
    {g₂ : Metric.closedBall center R →
      EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ}
    (hfirst : ∀ x : EuclideanSpace ℂ (Fin n), ∀ hx : x ∈ Metric.ball center R,
      g₁ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩ =
        iteratedFDeriv ℝ 1 f x)
    (h₁ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 1 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₁ atTop)
    (h₂ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 2 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₂ atTop) :
    ∀ (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball center R),
      HasFDerivAt (iteratedFDeriv ℝ 1 f)
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) ℝ
          (g₂ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩)) x := by
  classical
  intro x hx
  let curry := continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) ℝ
  let G₂ : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) →L[ℝ] (EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ) := fun y =>
    if hy : y ∈ Metric.closedBall center R then
      curry (g₂ ⟨y, hy⟩)
    else 0
  have hcurryLip : LipschitzWith 1 curry := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [curry.dist_map]
    simp
  have h₂curry : TendstoUniformly
      (fun m (y : Metric.closedBall center R) =>
        curry (iteratedFDeriv ℝ 2 (u (φ m)) (y : EuclideanSpace ℂ (Fin n))))
      (fun y => curry (g₂ y)) atTop :=
    hcurryLip.uniformContinuous.comp_tendstoUniformly h₂
  have h₂on : TendstoUniformlyOn
      (fun m y => curry (iteratedFDeriv ℝ 2 (u (φ m)) y)) G₂ atTop
      (Metric.closedBall center R) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have htarget : (fun y : Metric.closedBall center R => G₂ (y : EuclideanSpace ℂ (Fin n))) =
        (fun y => curry (g₂ y)) := by
      funext y
      simp only [G₂, dif_pos y.property]
    change TendstoUniformly _ (fun y : Metric.closedBall center R => G₂ (y : EuclideanSpace ℂ (Fin n))) atTop
    rw [htarget]
    exact h₂curry
  have h₂loc : TendstoLocallyUniformlyOn
      (fun m y => curry (iteratedFDeriv ℝ 2 (u (φ m)) y)) G₂ atTop
      (Metric.ball center R) :=
    h₂on.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall
  have hfg : ∀ y ∈ Metric.ball center R,
      Tendsto (fun m => iteratedFDeriv ℝ 1 (u (φ m)) y) atTop
        (𝓝 (iteratedFDeriv ℝ 1 f y)) := by
    intro y hy
    let hyR : y ∈ Metric.closedBall center R :=
      Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hy))
    simpa [hfirst y hy] using h₁.tendsto_at ⟨y, hyR⟩
  have hder : ∀ m y, y ∈ Metric.ball center R →
      HasFDerivAt (iteratedFDeriv ℝ 1 (u (φ m)))
        (curry (iteratedFDeriv ℝ 2 (u (φ m)) y)) y := by
    intro m y hy
    have hyS : y ∈ Metric.ball center S :=
      Metric.ball_subset_ball hS.le hy
    have hAt : ContDiffAt ℝ 2 (u (φ m)) y :=
      (hsmooth (φ m)).contDiffAt (Metric.isOpen_ball.mem_nhds hyS)
    have hklt : (↑(1 : ℕ) : ℕ∞ω) < 2 := by norm_num
    have hdiff := hAt.differentiableAt_iteratedFDeriv hklt
    have hhas := hdiff.hasFDerivAt
    have hfd := congrFun
      (fderiv_iteratedFDeriv (𝕜 := ℝ) (f := u (φ m)) (n := 1)) y
    rw [hfd] at hhas
    exact hhas
  have hresult := hasFDerivAt_of_tendstoLocallyUniformlyOn
    Metric.isOpen_ball h₂loc hder hfg hx
  simpa only [G₂, dif_pos (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx)))]
    using hresult

private theorem secondJetLimit_derivative_compatibility
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)}
    {r R S : ℝ} {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {φ : ℕ → ℕ}
    (hR : r < R) (hS : R < S)
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    {g₀ : Metric.closedBall center R → ℝ}
    {g₁ : Metric.closedBall center R →
      EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ}
    {g₂ : Metric.closedBall center R →
      EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ}
    (hvalues : ∀ x : Metric.closedBall center R, g₀ x = f (x : EuclideanSpace ℂ (Fin n)))
    (h₀ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      u (φ m) (x : EuclideanSpace ℂ (Fin n))) g₀ atTop)
    (h₁ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 1 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₁ atTop)
    (h₂ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 2 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₂ atTop) :
    ContDiffOn ℝ 2 f (Metric.ball center R) ∧
      ∀ j ≤ 2, TendstoLocallyUniformlyOn
        (fun m => iteratedFDeriv ℝ j (u (φ m)))
        (iteratedFDeriv ℝ j f) atTop (Metric.closedBall center r) := by
  let : FiniteDimensional ℝ
      ((EuclideanSpace ℂ (Fin n)) [×1]→L[ℝ] ℝ) :=
    finiteDimensional_iteratedCML (E := EuclideanSpace ℂ (Fin n)) 1
  classical
  have hfirst := secondJetLimit_first_derivative_compatibility hS hsmooth hvalues h₀ h₁
  have hident₁ : ∀ x : EuclideanSpace ℂ (Fin n), ∀ hx : x ∈ Metric.ball center R,
      g₁ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩ =
        iteratedFDeriv ℝ 1 f x := by
    intro x hx
    have hfd := (hfirst x hx).fderiv
    have hformula : fderiv ℝ f x =
        continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (iteratedFDeriv ℝ 1 f x) := by
      ext v
      simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    apply (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ).injective
    calc
      continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (g₁ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩) =
          fderiv ℝ f x := hfd.symm
      _ = continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (iteratedFDeriv ℝ 1 f x) := hformula
  have hsecond := secondJetLimit_second_derivative_compatibility
    hS hsmooth hident₁ h₁ h₂
  have hident₂ : ∀ x : EuclideanSpace ℂ (Fin n), ∀ hx : x ∈ Metric.ball center R,
      g₂ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩ =
        iteratedFDeriv ℝ 2 f x := by
    intro x hx
    let curry := continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) ℝ
    have hfd := (hsecond x hx).fderiv
    have hformula : fderiv ℝ (iteratedFDeriv ℝ 1 f) x =
        curry (iteratedFDeriv ℝ 2 f x) := by
      have h := congrFun (fderiv_iteratedFDeriv (𝕜 := ℝ) (f := f) (n := 1)) x
      simpa [curry, Function.comp_apply] using h
    apply curry.injective
    calc
      curry (g₂ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩) =
          fderiv ℝ (iteratedFDeriv ℝ 1 f) x := hfd.symm
      _ = curry (iteratedFDeriv ℝ 2 f x) := hformula
  have hg₂ : Continuous g₂ :=
    secondJetLimit_uniform_limit_jet_continuous hS (j := 2) (by norm_num)
      hsmooth h₂
  let inc : Metric.ball center R → Metric.closedBall center R := fun x =>
    ⟨(x : EuclideanSpace ℂ (Fin n)), Metric.ball_subset_closedBall x.property⟩
  have hinc : Continuous inc :=
    Continuous.subtype_mk continuous_subtype_val (fun x => Metric.ball_subset_closedBall x.property)
  let curry := continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) ℝ
  have hderivW₁ : ContinuousOn (fderiv ℝ (iteratedFDeriv ℝ 1 f))
      (Metric.ball center R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Metric.ball center R).domRestrict (fderiv ℝ (iteratedFDeriv ℝ 1 f)) =
        (fun x : Metric.ball center R => curry (g₂ (inc x))) := by
      funext x
      have h := (hsecond (x : EuclideanSpace ℂ (Fin n)) x.property).fderiv
      simpa [inc, curry] using h
    rw [heq]
    exact curry.continuous.comp (hg₂.comp hinc)
  have hW₁C1 : ContDiffOn ℝ 1 (iteratedFDeriv ℝ 1 f) (Metric.ball center R) := by
    change ContDiffOn ℝ ((0 : ℕ∞) + 1) (iteratedFDeriv ℝ 1 f) (Metric.ball center R)
    rw [contDiffOn_succ_iff_fderiv_of_isOpen (n := (0 : ℕ∞)) Metric.isOpen_ball]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact (hsecond x hx).differentiableAt.differentiableWithinAt
    · simp
    · exact contDiffOn_zero.mpr hderivW₁
  have hderivf_eq : Set.EqOn (fderiv ℝ f)
      (fun x => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        (iteratedFDeriv ℝ 1 f x)) (Metric.ball center R) := by
    intro x hx
    have hfd := (hfirst x hx).fderiv
    rw [hident₁ x hx] at hfd
    exact hfd
  have hderivfC1 : ContDiffOn ℝ 1 (fderiv ℝ f) (Metric.ball center R) := by
    let curry₁ := continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
    have hcomp : ContDiffOn ℝ 1
        (fun x => curry₁ (iteratedFDeriv ℝ 1 f x)) (Metric.ball center R) := by
      simpa [curry₁, Function.comp_def] using
        hW₁C1.continuousLinearMap_comp curry₁.toContinuousLinearMap
    apply hcomp.congr
    intro x hx
    exact hderivf_eq (x := x) hx
  have hfC2 : ContDiffOn ℝ 2 f (Metric.ball center R) := by
    change ContDiffOn ℝ ((1 : ℕ∞) + 1) f (Metric.ball center R)
    rw [contDiffOn_succ_iff_fderiv_of_isOpen (n := (1 : ℕ∞)) Metric.isOpen_ball]
    refine ⟨?_, ?_, hderivfC1⟩
    · intro x hx
      exact (hfirst x hx).differentiableAt.differentiableWithinAt
    · simp
  refine ⟨hfC2, ?_⟩
  let inner : Set (EuclideanSpace ℂ (Fin n)) := Metric.closedBall center r
  have hinner : inner ⊆ Metric.closedBall center R :=
    Metric.closedBall_subset_closedBall hR.le
  have h₀on : TendstoUniformlyOn (fun m y => u (φ m) y) f atTop
      (Metric.closedBall center R) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have htarget : (fun x : Metric.closedBall center R => f (x : EuclideanSpace ℂ (Fin n))) = g₀ := by
      funext x
      exact (hvalues x).symm
    change TendstoUniformly _ (fun x : Metric.closedBall center R => f (x : EuclideanSpace ℂ (Fin n))) atTop
    rw [htarget]
    exact h₀
  have h₀inner := h₀on.mono hinner
  let curry₀ := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
  have hvalU : TendstoUniformly
      (fun m (x : Metric.closedBall center r) => u (φ m) (x : EuclideanSpace ℂ (Fin n)))
      (fun x => f (x : EuclideanSpace ℂ (Fin n))) atTop :=
    (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp h₀inner)
  have hjet0 (v : EuclideanSpace ℂ (Fin n) → ℝ) (x : EuclideanSpace ℂ (Fin n)) :
      iteratedFDeriv ℝ 0 v x = curry₀.symm (v x) := by
    rw [iteratedFDeriv_zero_eq_comp]
    rfl
  have h₀innerU : TendstoUniformly
      (fun m (x : Metric.closedBall center r) =>
        iteratedFDeriv ℝ 0 (u (φ m)) (x : EuclideanSpace ℂ (Fin n)))
      (fun x => iteratedFDeriv ℝ 0 f (x : EuclideanSpace ℂ (Fin n))) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hvalU) ε hε] with m hm x
    have hdist : dist
        (iteratedFDeriv ℝ 0 f (x : EuclideanSpace ℂ (Fin n)))
        (iteratedFDeriv ℝ 0 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) =
        dist (f (x : EuclideanSpace ℂ (Fin n))) (u (φ m) (x : EuclideanSpace ℂ (Fin n))) := by
      rw [hjet0, hjet0, curry₀.symm.dist_map]
    rw [hdist]
    exact hm x
  have h₀innerLoc : TendstoLocallyUniformlyOn
      (fun m y => iteratedFDeriv ℝ 0 (u (φ m)) y)
      (iteratedFDeriv ℝ 0 f) atTop inner := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    exact h₀innerU.tendstoLocallyUniformly
  let H₁ : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ := fun y =>
    if hy : y ∈ Metric.closedBall center R then g₁ ⟨y, hy⟩ else 0
  have h₁on : TendstoUniformlyOn
      (fun m y => iteratedFDeriv ℝ 1 (u (φ m)) y) H₁ atTop
      (Metric.closedBall center R) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have htarget : (fun x : Metric.closedBall center R => H₁ (x : EuclideanSpace ℂ (Fin n))) = g₁ := by
      funext x
      simp only [H₁, dif_pos x.property]
    change TendstoUniformly _ (fun x : Metric.closedBall center R => H₁ (x : EuclideanSpace ℂ (Fin n))) atTop
    rw [htarget]
    exact h₁
  have h₁target : (fun x : Metric.closedBall center r => H₁ (x : EuclideanSpace ℂ (Fin n))) =
      (fun x : Metric.closedBall center r => iteratedFDeriv ℝ 1 f (x : EuclideanSpace ℂ (Fin n))) := by
    funext x
    have hxR : (x : EuclideanSpace ℂ (Fin n)) ∈ Metric.ball center R :=
      Metric.closedBall_subset_ball hR x.property
    have hxclosed : (x : EuclideanSpace ℂ (Fin n)) ∈ Metric.closedBall center R :=
      Metric.ball_subset_closedBall hxR
    simp only [H₁, dif_pos hxclosed]
    exact hident₁ (x : EuclideanSpace ℂ (Fin n)) hxR
  have h₁innerOn := h₁on.mono hinner
  have h₁innerU : TendstoUniformly
      (fun m (x : Metric.closedBall center r) =>
        iteratedFDeriv ℝ 1 (u (φ m)) (x : EuclideanSpace ℂ (Fin n)))
      (fun x => iteratedFDeriv ℝ 1 f (x : EuclideanSpace ℂ (Fin n))) atTop := by
    have hU := tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp h₁innerOn
    have hU' : TendstoUniformly
        (fun (m : ℕ) (x : Metric.closedBall center r) =>
          iteratedFDeriv ℝ 1 (u (φ m)) (x : EuclideanSpace ℂ (Fin n)))
        (fun x : Metric.closedBall center r => H₁ (x : EuclideanSpace ℂ (Fin n))) atTop := by
      change TendstoUniformly _
        (fun x : Metric.closedBall center r => H₁ (x : EuclideanSpace ℂ (Fin n))) atTop at hU
      exact hU
    rw [h₁target] at hU'
    exact hU'
  have h₁innerLoc : TendstoLocallyUniformlyOn
      (fun m y => iteratedFDeriv ℝ 1 (u (φ m)) y)
      (iteratedFDeriv ℝ 1 f) atTop inner := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    exact h₁innerU.tendstoLocallyUniformly
  let H₂ : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ := fun y =>
    if hy : y ∈ Metric.closedBall center R then g₂ ⟨y, hy⟩ else 0
  have h₂on : TendstoUniformlyOn
      (fun m y => iteratedFDeriv ℝ 2 (u (φ m)) y) H₂ atTop
      (Metric.closedBall center R) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have htarget : (fun x : Metric.closedBall center R => H₂ (x : EuclideanSpace ℂ (Fin n))) = g₂ := by
      funext x
      simp only [H₂, dif_pos x.property]
    change TendstoUniformly _ (fun x : Metric.closedBall center R => H₂ (x : EuclideanSpace ℂ (Fin n))) atTop
    rw [htarget]
    exact h₂
  have h₂target : (fun x : Metric.closedBall center r => H₂ (x : EuclideanSpace ℂ (Fin n))) =
      (fun x : Metric.closedBall center r => iteratedFDeriv ℝ 2 f (x : EuclideanSpace ℂ (Fin n))) := by
    funext x
    have hxR : (x : EuclideanSpace ℂ (Fin n)) ∈ Metric.ball center R :=
      Metric.closedBall_subset_ball hR x.property
    have hxclosed : (x : EuclideanSpace ℂ (Fin n)) ∈ Metric.closedBall center R :=
      Metric.ball_subset_closedBall hxR
    simp only [H₂, dif_pos hxclosed]
    exact hident₂ (x : EuclideanSpace ℂ (Fin n)) hxR
  have h₂innerOn := h₂on.mono hinner
  have h₂innerU : TendstoUniformly
      (fun m (x : Metric.closedBall center r) =>
        iteratedFDeriv ℝ 2 (u (φ m)) (x : EuclideanSpace ℂ (Fin n)))
      (fun x => iteratedFDeriv ℝ 2 f (x : EuclideanSpace ℂ (Fin n))) atTop := by
    have hU := tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp h₂innerOn
    have hU' : TendstoUniformly
        (fun (m : ℕ) (x : Metric.closedBall center r) =>
          iteratedFDeriv ℝ 2 (u (φ m)) (x : EuclideanSpace ℂ (Fin n)))
        (fun x : Metric.closedBall center r => H₂ (x : EuclideanSpace ℂ (Fin n))) atTop := by
      change TendstoUniformly _
        (fun x : Metric.closedBall center r => H₂ (x : EuclideanSpace ℂ (Fin n))) atTop at hU
      exact hU
    rw [h₂target] at hU'
    exact hU'
  have h₂innerLoc : TendstoLocallyUniformlyOn
      (fun m y => iteratedFDeriv ℝ 2 (u (φ m)) y)
      (iteratedFDeriv ℝ 2 f) atTop inner := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    exact h₂innerU.tendstoLocallyUniformly
  intro j hj
  interval_cases j
  · exact h₀innerLoc
  · exact h₁innerLoc
  · exact h₂innerLoc

private theorem secondJetLimit_values_identify
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)}
    {R : ℝ} {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hlimit : TendstoUniformlyOn u f atTop (Metric.closedBall center R))
    {g₀ : Metric.closedBall center R → ℝ}
    (h₀ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      u (φ m) (x : EuclideanSpace ℂ (Fin n))) g₀ atTop) :
    ∀ x : Metric.closedBall center R, g₀ x = f (x : EuclideanSpace ℂ (Fin n)) := by
  have hlimitSubseq := hlimit.seq_tendstoUniformlyOn φ hφ.tendsto_atTop
  intro x
  exact tendsto_nhds_unique (h₀.tendsto_at x) (hlimitSubseq.tendsto_at x.property)

private theorem secondJetLimit_identify_uniform_jet_limits
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)}
    {r R S : ℝ} {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hR : r < R) (hS : R < S)
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    (hlimit : TendstoUniformlyOn u f atTop (Metric.closedBall center R))
    {g₀ : Metric.closedBall center R → ℝ}
    {g₁ : Metric.closedBall center R →
      EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ}
    {g₂ : Metric.closedBall center R →
      EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ}
    (h₀ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      u (φ m) (x : EuclideanSpace ℂ (Fin n))) g₀ atTop)
    (h₁ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 1 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₁ atTop)
    (h₂ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 2 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₂ atTop) :
    ContDiffOn ℝ 2 f (Metric.ball center R) ∧
      ∀ j ≤ 2, TendstoLocallyUniformlyOn
        (fun m => iteratedFDeriv ℝ j (u (φ m)))
        (iteratedFDeriv ℝ j f) atTop (Metric.closedBall center r) := by
  have hvalues := secondJetLimit_values_identify hφ hlimit h₀
  exact secondJetLimit_derivative_compatibility hR hS hsmooth hvalues h₀ h₁ h₂

/-- Given a value limit and actual uniform limits of the first two jets, those limits are
its derivatives on the interior. Shrinking once gives uniform convergence to the actual jets
also on the closed inner ball. There is no assertion at the boundary of the extraction ball. -/
private theorem jetIdentification_first_derivative_compatibility
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)} {R S : ℝ}
    {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {φ : ℕ → ℕ}
    (hS : R < S)
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    {g₀ : Metric.closedBall center R → ℝ}
    {g₁ : Metric.closedBall center R → EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ}
    (hvalues : ∀ x : Metric.closedBall center R, g₀ x = f (x : EuclideanSpace ℂ (Fin n)))
    (h₀ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      u (φ m) (x : EuclideanSpace ℂ (Fin n))) g₀ atTop)
    (h₁ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 1 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₁ atTop) :
    ∀ x : EuclideanSpace ℂ (Fin n), ∀ hx : x ∈ Metric.ball center R,
      HasFDerivAt f
        (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (g₁ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩)) x := by
  classical
  intro x hx
  let hxR : x ∈ Metric.closedBall center R :=
    Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))
  let G₁ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ := fun y =>
    if hy : y ∈ Metric.closedBall center R then
      continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ (g₁ ⟨y, hy⟩)
    else 0
  have hcurrylip : LipschitzWith 1
      (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [(continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ).dist_map]
    simp
  have h₁curry : TendstoUniformly
      (fun m (y : Metric.closedBall center R) =>
        continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (iteratedFDeriv ℝ 1 (u (φ m)) (y : EuclideanSpace ℂ (Fin n))))
      (fun y => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ (g₁ y)) atTop :=
    hcurrylip.uniformContinuous.comp_tendstoUniformly h₁
  have h₁on : TendstoUniformlyOn
      (fun m y => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        (iteratedFDeriv ℝ 1 (u (φ m)) y)) G₁ atTop (Metric.closedBall center R) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have htarget : (fun y : Metric.closedBall center R => G₁ y) =
        (fun y => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ (g₁ y)) := by
      funext y
      simp only [G₁, dif_pos y.property]
    change TendstoUniformly _ (fun y : Metric.closedBall center R => G₁ y) atTop
    rw [htarget]
    exact h₁curry
  have h₁loc : TendstoLocallyUniformlyOn
      (fun m y => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        (iteratedFDeriv ℝ 1 (u (φ m)) y)) G₁ atTop (Metric.ball center R) :=
    h₁on.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall
  have hfg : ∀ y ∈ Metric.ball center R, Tendsto (fun m => u (φ m) y) atTop (𝓝 (f y)) := by
    intro y hy
    let hyR : y ∈ Metric.closedBall center R :=
      Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hy))
    simpa [hvalues ⟨y, hyR⟩] using h₀.tendsto_at ⟨y, hyR⟩
  have hder : ∀ m y, y ∈ Metric.ball center R →
      HasFDerivAt (u (φ m))
        (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (iteratedFDeriv ℝ 1 (u (φ m)) y)) y := by
    intro m y hy
    have hyS : y ∈ Metric.ball center S := Metric.ball_subset_ball hS.le hy
    have hAt : ContDiffAt ℝ 2 (u (φ m)) y :=
      (hsmooth (φ m)).contDiffAt (Metric.isOpen_ball.mem_nhds hyS)
    have hdiff := hAt.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
    have hhas := hdiff.hasFDerivAt
    have hEq : fderiv ℝ (u (φ m)) y =
        continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (iteratedFDeriv ℝ 1 (u (φ m)) y) := by
      ext v
      simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    rw [hEq] at hhas
    exact hhas
  simpa only [G₁, dif_pos hxR] using
    hasFDerivAt_of_tendstoLocallyUniformlyOn Metric.isOpen_ball h₁loc hder hfg hx

private theorem jetIdentification_first_jet_identification
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)} {R S : ℝ}
    {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {φ : ℕ → ℕ}
    (hS : R < S)
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    {g₀ : Metric.closedBall center R → ℝ}
    {g₁ : Metric.closedBall center R → EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ}
    (hvalues : ∀ x : Metric.closedBall center R, g₀ x = f (x : EuclideanSpace ℂ (Fin n)))
    (h₀ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      u (φ m) (x : EuclideanSpace ℂ (Fin n))) g₀ atTop)
    (h₁ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 1 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₁ atTop) :
    ∀ x : EuclideanSpace ℂ (Fin n), ∀ hx : x ∈ Metric.ball center R,
      g₁ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩ =
        iteratedFDeriv ℝ 1 f x := by
  have hfirst := jetIdentification_first_derivative_compatibility hS hsmooth hvalues h₀ h₁
  intro x hx
  have hfd := (hfirst x hx).fderiv
  have hformula : fderiv ℝ f x =
      continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        (iteratedFDeriv ℝ 1 f x) := by
    ext v
    simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  apply (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ).injective
  calc
    continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        (g₁ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩) =
        fderiv ℝ f x := hfd.symm
    _ = continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        (iteratedFDeriv ℝ 1 f x) := hformula

private theorem jetIdentification_second_derivative_compatibility
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)} {R S : ℝ}
    {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {φ : ℕ → ℕ}
    (hS : R < S)
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    {g₁ : Metric.closedBall center R → EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ}
    {g₂ : Metric.closedBall center R → EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ}
    (hfirst : ∀ x : EuclideanSpace ℂ (Fin n), ∀ hx : x ∈ Metric.ball center R,
      g₁ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩ =
        iteratedFDeriv ℝ 1 f x)
    (h₁ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 1 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₁ atTop)
    (h₂ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 2 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₂ atTop) :
    ∀ x : EuclideanSpace ℂ (Fin n), ∀ hx : x ∈ Metric.ball center R,
      HasFDerivAt (iteratedFDeriv ℝ 1 f)
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) ℝ
          (g₂ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩)) x := by
  classical
  intro x hx
  let curry := continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) ℝ
  let G₂ : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) →L[ℝ] (EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ) := fun y =>
    if hy : y ∈ Metric.closedBall center R then curry (g₂ ⟨y, hy⟩) else 0
  have hcurryLip : LipschitzWith 1 curry := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [curry.dist_map]
    simp
  have h₂curry : TendstoUniformly
      (fun m (y : Metric.closedBall center R) =>
        curry (iteratedFDeriv ℝ 2 (u (φ m)) (y : EuclideanSpace ℂ (Fin n))))
      (fun y => curry (g₂ y)) atTop :=
    hcurryLip.uniformContinuous.comp_tendstoUniformly h₂
  have h₂on : TendstoUniformlyOn
      (fun m y => curry (iteratedFDeriv ℝ 2 (u (φ m)) y)) G₂ atTop
      (Metric.closedBall center R) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have htarget : (fun y : Metric.closedBall center R => G₂ y) =
        (fun y => curry (g₂ y)) := by
      funext y
      simp only [G₂, dif_pos y.property]
    change TendstoUniformly _ (fun y : Metric.closedBall center R => G₂ y) atTop
    rw [htarget]
    exact h₂curry
  have h₂loc : TendstoLocallyUniformlyOn
      (fun m y => curry (iteratedFDeriv ℝ 2 (u (φ m)) y)) G₂ atTop
      (Metric.ball center R) :=
    h₂on.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall
  have hfg : ∀ y ∈ Metric.ball center R,
      Tendsto (fun m => iteratedFDeriv ℝ 1 (u (φ m)) y) atTop
        (𝓝 (iteratedFDeriv ℝ 1 f y)) := by
    intro y hy
    simpa [hfirst y hy] using h₁.tendsto_at
      ⟨y, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hy))⟩
  have hder : ∀ m y, y ∈ Metric.ball center R →
      HasFDerivAt (iteratedFDeriv ℝ 1 (u (φ m)))
        (curry (iteratedFDeriv ℝ 2 (u (φ m)) y)) y := by
    intro m y hy
    have hyS : y ∈ Metric.ball center S := Metric.ball_subset_ball hS.le hy
    have hAt : ContDiffAt ℝ 2 (u (φ m)) y :=
      (hsmooth (φ m)).contDiffAt (Metric.isOpen_ball.mem_nhds hyS)
    have hklt : (↑(1 : ℕ) : ℕ∞ω) < 2 := by norm_num
    have hdiff := hAt.differentiableAt_iteratedFDeriv hklt
    have hhas := hdiff.hasFDerivAt
    have hfd := congrFun
      (fderiv_iteratedFDeriv (𝕜 := ℝ) (f := u (φ m)) (n := 1)) y
    rw [hfd] at hhas
    exact hhas
  have hresult := hasFDerivAt_of_tendstoLocallyUniformlyOn
    Metric.isOpen_ball h₂loc hder hfg hx
  simpa only [G₂, dif_pos (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx)))]
    using hresult

private theorem jetIdentification_second_jet_identification
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)} {R S : ℝ}
    {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {φ : ℕ → ℕ}
    (hS : R < S)
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    {g₁ : Metric.closedBall center R → EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ}
    {g₂ : Metric.closedBall center R → EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ}
    (hfirst : ∀ x : EuclideanSpace ℂ (Fin n), ∀ hx : x ∈ Metric.ball center R,
      g₁ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩ =
        iteratedFDeriv ℝ 1 f x)
    (h₁ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 1 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₁ atTop)
    (h₂ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 2 (u (φ m)) (x : EuclideanSpace ℂ (Fin n))) g₂ atTop) :
    ∀ x : EuclideanSpace ℂ (Fin n), ∀ hx : x ∈ Metric.ball center R,
      g₂ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩ =
        iteratedFDeriv ℝ 2 f x := by
  have hsecond := jetIdentification_second_derivative_compatibility
    hS hsmooth hfirst h₁ h₂
  intro x hx
  let curry := continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) ℝ
  have hfd := (hsecond x hx).fderiv
  have hformula : fderiv ℝ (iteratedFDeriv ℝ 1 f) x = curry (iteratedFDeriv ℝ 2 f x) := by
    have h := congrFun (fderiv_iteratedFDeriv (𝕜 := ℝ) (f := f) (n := 1)) x
    simpa [curry, Function.comp_apply] using h
  apply curry.injective
  calc
    curry (g₂ ⟨x, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩) =
        fderiv ℝ (iteratedFDeriv ℝ 1 f) x := hfd.symm
    _ = curry (iteratedFDeriv ℝ 2 f x) := hformula

private theorem jetIdentification_contDiffOn
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)} {R S : ℝ}
    {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {g₀ : Metric.closedBall center R → ℝ}
    {g₁ : Metric.closedBall center R → EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ}
    {g₂ : Metric.closedBall center R → EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ}
    (hS : R < S)
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    (hvalues : ∀ x : Metric.closedBall center R, g₀ x = f (x : EuclideanSpace ℂ (Fin n)))
    (h₀ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      u m (x : EuclideanSpace ℂ (Fin n))) g₀ atTop)
    (h₁ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 1 (u m) (x : EuclideanSpace ℂ (Fin n))) g₁ atTop)
    (h₂ : TendstoUniformly (fun m (x : Metric.closedBall center R) =>
      iteratedFDeriv ℝ 2 (u m) (x : EuclideanSpace ℂ (Fin n))) g₂ atTop) :
    ContDiffOn ℝ 2 f (Metric.ball center R) := by
  let : FiniteDimensional ℝ
      ((EuclideanSpace ℂ (Fin n)) [×1]→L[ℝ] ℝ) :=
    finiteDimensional_iteratedCML (E := EuclideanSpace ℂ (Fin n)) 1
  have hfirst := jetIdentification_first_derivative_compatibility
    (φ := fun m => m) hS hsmooth hvalues h₀ h₁
  have hident₁ := jetIdentification_first_jet_identification
    (φ := fun m => m) hS hsmooth hvalues h₀ h₁
  have hsecond := jetIdentification_second_derivative_compatibility
    (φ := fun m => m) hS hsmooth hident₁ h₁ h₂
  have hg₂ : Continuous g₂ := by
    have hseq : ∀ m, Continuous (fun x : Metric.closedBall center R =>
        iteratedFDeriv ℝ 2 (u m) (x : EuclideanSpace ℂ (Fin n))) := by
      intro m
      apply continuousOn_iff_continuous_domRestrict.mp
      have hopen : IsOpen (Metric.ball center S) := Metric.isOpen_ball
      have hwithin : ContinuousOn
          (iteratedFDerivWithin ℝ 2 (u m) (Metric.ball center S))
          (Metric.ball center S) :=
        (hsmooth m).continuousOn_iteratedFDerivWithin (by norm_num) hopen.uniqueDiffOn
      have heq : Set.EqOn (iteratedFDerivWithin ℝ 2 (u m) (Metric.ball center S))
          (iteratedFDeriv ℝ 2 (u m)) (Metric.ball center S) := by
        intro x hx
        apply iteratedFDerivWithin_eq_iteratedFDeriv hopen.uniqueDiffOn
        · exact ((hsmooth m).contDiffAt (hopen.mem_nhds hx)).of_le (by norm_num)
        · exact hx
      exact (hwithin.congr heq.symm).mono (Metric.closedBall_subset_ball hS)
    exact h₂.continuous (Filter.Frequently.of_forall hseq)
  let inc : Metric.ball center R → Metric.closedBall center R := fun x =>
    ⟨(x : EuclideanSpace ℂ (Fin n)), Metric.ball_subset_closedBall x.property⟩
  have hinc : Continuous inc :=
    Continuous.subtype_mk continuous_subtype_val (fun x => Metric.ball_subset_closedBall x.property)
  let curry := continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) ℝ
  have hderivW₁ : ContinuousOn (fderiv ℝ (iteratedFDeriv ℝ 1 f))
      (Metric.ball center R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Metric.ball center R).domRestrict (fderiv ℝ (iteratedFDeriv ℝ 1 f)) =
        (fun x : Metric.ball center R => curry (g₂ (inc x))) := by
      funext x
      have h := (hsecond (x : EuclideanSpace ℂ (Fin n)) x.property).fderiv
      simpa [inc, curry] using h
    rw [heq]
    exact curry.continuous.comp (hg₂.comp hinc)
  have hW₁C1 : ContDiffOn ℝ 1 (iteratedFDeriv ℝ 1 f) (Metric.ball center R) := by
    change ContDiffOn ℝ ((0 : ℕ∞) + 1) (iteratedFDeriv ℝ 1 f) (Metric.ball center R)
    rw [contDiffOn_succ_iff_fderiv_of_isOpen (n := (0 : ℕ∞)) Metric.isOpen_ball]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact (hsecond x hx).differentiableAt.differentiableWithinAt
    · simp
    · exact contDiffOn_zero.mpr hderivW₁
  have hderivf_eq : Set.EqOn (fderiv ℝ f)
      (fun x => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        (iteratedFDeriv ℝ 1 f x)) (Metric.ball center R) := by
    intro x hx
    have hfd := (hfirst x hx).fderiv
    rw [hident₁ x hx] at hfd
    exact hfd
  have hderivfC1 : ContDiffOn ℝ 1 (fderiv ℝ f) (Metric.ball center R) := by
    let curry₁ := continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
    have hcomp : ContDiffOn ℝ 1
        (fun x => curry₁ (iteratedFDeriv ℝ 1 f x)) (Metric.ball center R) := by
      simpa [curry₁, Function.comp_def] using
        hW₁C1.continuousLinearMap_comp curry₁.toContinuousLinearMap
    apply hcomp.congr
    intro x hx
    exact hderivf_eq (x := x) hx
  change ContDiffOn ℝ ((1 : ℕ∞) + 1) f (Metric.ball center R)
  rw [contDiffOn_succ_iff_fderiv_of_isOpen (n := (1 : ℕ∞)) Metric.isOpen_ball]
  refine ⟨?_, ?_, hderivfC1⟩
  · intro x hx
    exact (hfirst x hx).differentiableAt.differentiableWithinAt
  · simp

@[deprecated "unused hypothesis `hr`; will be removed" (since := "2026-10-02")]
theorem identify_uniform_jet_limits_on_nested_balls
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)} {r R S : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRS : R < S)
    (v : ℕ → EuclideanSpace ℂ (Fin n) → ℝ)
    (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (hv : ∀ j, ContDiffOn ℝ 2 (v j) (Metric.ball center S))
    (g₀ : Metric.closedBall center R → ℝ)
    (g₁ : Metric.closedBall center R → EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ)
    (g₂ : Metric.closedBall center R → EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ)
    (hvalues : ∀ z : Metric.closedBall center R, g₀ z = f z)
    (h₀ : TendstoUniformly
      (fun j (z : Metric.closedBall center R) => v j z) g₀ atTop)
    (h₁ : TendstoUniformly
      (fun j (z : Metric.closedBall center R) => iteratedFDeriv ℝ 1 (v j) z) g₁ atTop)
    (h₂ : TendstoUniformly
      (fun j (z : Metric.closedBall center R) => iteratedFDeriv ℝ 2 (v j) z) g₂ atTop) :
    ContDiffOn ℝ 2 f (Metric.ball center R) ∧
      ∀ k : ℕ, k ≤ 2 → TendstoUniformlyOn
        (fun j => iteratedFDeriv ℝ k (v j)) (iteratedFDeriv ℝ k f) atTop
        (Metric.closedBall center r) := by
  have _hr := hr
  classical
  have hregular := jetIdentification_contDiffOn hRS hv hvalues h₀ h₁ h₂
  have hident₁ := jetIdentification_first_jet_identification
    (R := R) (S := S) (u := v) (φ := fun j => j) hRS hv hvalues h₀ h₁
  have hident₂ := jetIdentification_second_jet_identification
    (R := R) (S := S) (u := v) (φ := fun j => j) hRS hv hident₁ h₁ h₂
  refine ⟨hregular, ?_⟩
  intro k hk
  interval_cases k
  · have h₀on : TendstoUniformlyOn (fun j y => v j y) f atTop
        (Metric.closedBall center R) := by
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
      have htarget : (fun z : Metric.closedBall center R => f z) = g₀ := by
        funext z
        exact (hvalues z).symm
      change TendstoUniformly _ (fun z : Metric.closedBall center R => f z) atTop
      rw [htarget]
      exact h₀
    have hinner : Metric.closedBall center r ⊆ Metric.closedBall center R :=
      Metric.closedBall_subset_closedBall hrR.le
    have h₀inner := h₀on.mono hinner
    have hvalU : TendstoUniformly
        (fun j (z : Metric.closedBall center r) => v j z) (fun z => f z) atTop :=
      tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp h₀inner
    have hjet0 (w : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n)) :
        iteratedFDeriv ℝ 0 w z = (continuousMultilinearCurryFin0 ℝ
          (EuclideanSpace ℂ (Fin n)) ℝ).symm (w z) := by
      rw [iteratedFDeriv_zero_eq_comp]
      rfl
    have hresult : TendstoUniformly
        (fun j (z : Metric.closedBall center r) => iteratedFDeriv ℝ 0 (v j) z)
        (fun z => iteratedFDeriv ℝ 0 f z) atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      filter_upwards [(Metric.tendstoUniformly_iff.mp hvalU) ε hε] with j hj z
      have hdist : dist (iteratedFDeriv ℝ 0 f z) (iteratedFDeriv ℝ 0 (v j) z) =
          dist (f z) (v j z) := by
        rw [hjet0, hjet0,
          (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ).symm.dist_map]
      rw [hdist]
      exact hj z
    exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hresult
  · have hinner : Metric.closedBall center r ⊆ Metric.closedBall center R :=
      Metric.closedBall_subset_closedBall hrR.le
    have hident (z : Metric.closedBall center r) :
        g₁ ⟨z, hinner z.property⟩ = iteratedFDeriv ℝ 1 f z := by
      exact hident₁ z (Metric.closedBall_subset_ball hrR z.property)
    let H₁ : EuclideanSpace ℂ (Fin n) →
        EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ := fun y =>
      if hy : y ∈ Metric.closedBall center R then g₁ ⟨y, hy⟩ else 0
    have h₁on : TendstoUniformlyOn
        (fun j y => iteratedFDeriv ℝ 1 (v j) y) H₁
        atTop (Metric.closedBall center R) := by
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
      have heq : (fun z : Metric.closedBall center R => H₁ z) = g₁ := by
        funext z
        simp only [H₁, dif_pos z.property]
      change TendstoUniformly _
        (fun z : Metric.closedBall center R => H₁ (z : EuclideanSpace ℂ (Fin n))) atTop
      rw [heq]
      exact h₁
    have h₁innerOn := h₁on.mono hinner
    have h₁target : Set.EqOn H₁ (iteratedFDeriv ℝ 1 f) (Metric.closedBall center r) := by
      intro z hz
      change (if hy : z ∈ Metric.closedBall center R then g₁ ⟨z, hy⟩ else 0) = _
      rw [dif_pos (hinner hz)]
      exact hident ⟨z, hz⟩
    exact h₁innerOn.congr_right h₁target
  · have hinner : Metric.closedBall center r ⊆ Metric.closedBall center R :=
      Metric.closedBall_subset_closedBall hrR.le
    have hident (z : Metric.closedBall center r) :
        g₂ ⟨z, hinner z.property⟩ = iteratedFDeriv ℝ 2 f z := by
      exact hident₂ z (Metric.closedBall_subset_ball hrR z.property)
    let H₂ : EuclideanSpace ℂ (Fin n) →
        EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ := fun y =>
      if hy : y ∈ Metric.closedBall center R then g₂ ⟨y, hy⟩ else 0
    have h₂on : TendstoUniformlyOn
        (fun j y => iteratedFDeriv ℝ 2 (v j) y) H₂
        atTop (Metric.closedBall center R) := by
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
      have heq : (fun z : Metric.closedBall center R => H₂ z) = g₂ := by
        funext z
        simp only [H₂, dif_pos z.property]
      change TendstoUniformly _
        (fun z : Metric.closedBall center R => H₂ (z : EuclideanSpace ℂ (Fin n))) atTop
      rw [heq]
      exact h₂
    have h₂innerOn := h₂on.mono hinner
    have h₂target : Set.EqOn H₂ (iteratedFDeriv ℝ 2 f) (Metric.closedBall center r) := by
      intro z hz
      change (if hy : z ∈ Metric.closedBall center R then g₂ ⟨z, hy⟩ else 0) = _
      rw [dif_pos (hinner hz)]
      exact hident ⟨z, hz⟩
    exact h₂innerOn.congr_right h₂target

end KahlerForm
