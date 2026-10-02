module

public import CalabiYau.Geometry.Complex.Schauder.SchauderCompactness
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Second-jet limits on nested balls

A common `C^{2,α}` bound gives subsequential compactness of the jets only below exponent `α`.
The second-jet Hölder bound itself is stable at the original exponent once the limit jet has been
identified. This module isolates that stability from the derivative-compatibility argument.
-/

@[expose] public section

open Filter
open scoped ContDiff NNReal Topology

namespace CalabiYau.Schauder

/-- Once all jets of a subsequence converge locally uniformly to the corresponding jets of `f`,
the original second-derivative Hölder bound passes to `f` without lowering its exponent. -/
private theorem holderBoundOn_of_locallyUniformlyConvergent_jets
    {n : ℕ} {K : Set (EuclideanSpace ℂ (Fin n))}
    {α C : ℝ≥0} {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {φ : ℕ → ℕ} {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hbound : ∀ m, HolderBoundOn 2 α C K (u m))
    (hjets : ∀ j ≤ 2, TendstoLocallyUniformlyOn
      (fun m => iteratedFDeriv ℝ j (u (φ m)))
      (iteratedFDeriv ℝ j f) atTop K) :
    HolderBoundOn 2 α C K f := by
  have hsecond := secondDerivative_holderBoundOn_of_tendstoLocallyUniformlyOn
    (fun m => hbound (φ m)) (hjets 2 le_rfl)
  refine ⟨?_, hsecond.1⟩
  intro j hj x hx
  apply le_of_tendsto ((hjets j hj).tendsto_at hx).norm
  exact Eventually.of_forall fun m => (hbound (φ m)).1 j hj x hx

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

private theorem secondJetLimit_subsequence_with_compatible_jets
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)}
    {r R S : ℝ} {α C : ℝ≥0}
    (hR : r < R) (hS : R < S)
    (hα : 0 < α) (hαone : α ≤ 1)
    {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    (hbound : ∀ m, HolderBoundOn 2 α C (Metric.closedBall center R) (u m))
    (hlimit : TendstoUniformlyOn u f atTop (Metric.closedBall center R)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ContDiffOn ℝ 2 f (Metric.ball center R) ∧
      ∀ j ≤ 2, TendstoLocallyUniformlyOn
        (fun m => iteratedFDeriv ℝ j (u (φ m)))
        (iteratedFDeriv ℝ j f) atTop (Metric.closedBall center r) := by
  have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin n)) := inferInstance
  have : ProperSpace (EuclideanSpace ℂ (Fin n)) :=
    FiniteDimensional.proper ℝ (EuclideanSpace ℂ (Fin n))
  have : FiniteDimensional ℝ
      ((EuclideanSpace ℂ (Fin n)) [×1]→L[ℝ] ℝ) :=
    finiteDimensional_iteratedCML (E := EuclideanSpace ℂ (Fin n)) 1
  have : FiniteDimensional ℝ
      ((EuclideanSpace ℂ (Fin n)) [×2]→L[ℝ] ℝ) :=
    finiteDimensional_iteratedCML (E := EuclideanSpace ℂ (Fin n)) 2
  let β : ℝ≥0 := α / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβα : β < α := by
    dsimp [β]
    exact half_lt_self hα
  obtain ⟨φ, g₀, g₁, g₂, hφ, _, _, _, h₀, h₁, h₂, _⟩ :=
    exists_subseq_tendsto_in_C2Holder_of_holderBoundOn
      (isCompact_closedBall center R) (convex_closedBall center R)
      Metric.isOpen_ball (Metric.closedBall_subset_ball hS)
      hα hαone hβ hβα hsmooth hbound
  have hcompat := secondJetLimit_identify_uniform_jet_limits
    hφ hR hS hsmooth hlimit h₀ h₁ h₂
  exact ⟨φ, hφ, hcompat.1, hcompat.2⟩

/-- A common `C^{2,α}` bound on a larger closed ball and uniform convergence of the values imply
`C^{2,α}` regularity, with the same Hölder constant and exponent, on a smaller ball. The open ball
on which the approximants are `C²` contains the larger closed ball, so both compactness and
identification of the limiting jets have a boundary margin. The compactness step is only at every
strictly lower Hölder exponent; no same-exponent `C^{2,α}` compactness is asserted. -/
theorem secondJetLimit_on_nested_balls
    {n : ℕ} {center : EuclideanSpace ℂ (Fin n)}
    {r R S : ℝ} {α C : ℝ≥0}
    (hR : r < R) (hS : R < S)
    (hα : 0 < α) (hαone : α ≤ 1)
    {u : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (u m) (Metric.ball center S))
    (hbound : ∀ m, HolderBoundOn 2 α C (Metric.closedBall center R) (u m))
    (hlimit : TendstoUniformlyOn u f atTop (Metric.closedBall center R)) :
    ContDiffOn ℝ 2 f (Metric.ball center r) ∧
      HolderBoundOn 2 α C (Metric.closedBall center r) f := by
  obtain ⟨φ, hφ, hregular, hjets⟩ := secondJetLimit_subsequence_with_compatible_jets
    hR hS hα hαone hsmooth hbound hlimit
  refine ⟨hregular.mono (Metric.ball_subset_ball hR.le), ?_⟩
  have hsubset : Metric.closedBall center r ⊆ Metric.closedBall center R :=
    Metric.closedBall_subset_closedBall hR.le
  exact holderBoundOn_of_locallyUniformlyConvergent_jets
    (K := Metric.closedBall center r)
    (fun m => (hbound m).mono_set hsubset) hjets

end CalabiYau.Schauder
