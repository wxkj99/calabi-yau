module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Analysis.Elliptic.Schauder

/-!
# Apply interior Schauder estimates to the coordinate derivatives

Once the inverse coefficients and differentiated forcing are bounded in `C^{r-2,α}`, the
interior estimate controls both real and imaginary coordinate derivatives in `C^{r,α}`.
Finite-dimensional jet reassembly then yields the potential's `C^{r+1,α}` bound on the target
compact set.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ComplexOrder MatrixOrder Topology
open Filter Set

namespace KahlerForm

private theorem contDiffOn_complexHessian_entries_of_contDiffOn_local
    {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (hf : ContDiffOn ℝ ∞ f U) :
    ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ complexHessian f z i j) U := by
  have hddbar : ContDiffOn ℝ ∞ (ddbar f) U := ContDiffOn.ddbar hU hf
  intro i j
  let f₁ : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
    ddbar f z ![EuclideanSpace.single i 1, Complex.I • EuclideanSpace.single j 1]
  let f₂ : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
    ddbar f z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
  have hf₁ : ContDiffOn ℝ ∞ f₁ U := by
    dsimp [f₁]
    exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
      ![EuclideanSpace.single i 1, Complex.I • EuclideanSpace.single j 1]).contDiff).comp_contDiffOn
        hddbar
  have hf₂ : ContDiffOn ℝ ∞ f₂ U := by
    dsimp [f₂]
    exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]).contDiff).comp_contDiffOn hddbar
  have hf₁c : ContDiffOn ℝ ∞ (fun z ↦ (f₁ z : ℂ)) U := by
    convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₁ using 1
    ext z
    simp [Complex.ofRealCLM_apply]
  have hf₂c : ContDiffOn ℝ ∞ (fun z ↦ (f₂ z : ℂ)) U := by
    convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₂ using 1
    ext z
    simp [Complex.ofRealCLM_apply]
  have hIprod : ContDiffOn ℝ ∞ (fun z ↦ Complex.I * (f₂ z : ℂ)) U :=
    contDiffOn_const.mul hf₂c
  have hformula : ContDiffOn ℝ ∞
      (fun z ↦ ((f₁ z : ℂ) - Complex.I * (f₂ z : ℂ)) / 2) U :=
    (hf₁c.sub hIprod).div_const (2 : ℂ)
  apply hformula.congr
  intro z hz
  change (ddbar f z).coeffMatrix i j = _
  simp [ContinuousAlternatingMap.coeffMatrix, f₁, f₂]

private theorem contDiffOn_matrixDet_of_contDiffOn_entries_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {U : Set E} {G : E → Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U) :
    ContDiffOn ℝ ∞ (fun z ↦ (G z).det) U := by
  simp only [Matrix.det_apply]
  fun_prop

private theorem contDiffOn_matrixInverse_entries_of_contDiffOn_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {U : Set E} {G : E → Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U)
    (hdet : ∀ z ∈ U, (G z).det ≠ 0) :
    ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ (G z)⁻¹ i j) U := by
  have hdetfun : ContDiffOn ℝ ∞ (fun z ↦ (G z).det) U :=
    contDiffOn_matrixDet_of_contDiffOn_entries_local hG
  have hinvdet : ContDiffOn ℝ ∞ (fun z ↦ ((G z).det)⁻¹) U :=
    hdetfun.inv hdet
  have hadj (i j : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ (G z).adjugate i j) U := by
    have hUpdate (a b : Fin n) : ContDiffOn ℝ ∞
        (fun z ↦ (G z).updateRow j (Pi.single i 1) a b) U := by
      by_cases ha : a = j
      · subst a
        by_cases hb : b = i
        · subst b
          simp [Matrix.updateRow_apply]
          exact contDiffOn_const
        · simp [Matrix.updateRow_apply, hb]
          exact contDiffOn_const
      · simp [Matrix.updateRow_apply, ha]
        exact hG a b
    have hdetUpdate := contDiffOn_matrixDet_of_contDiffOn_entries_local hUpdate
    apply hdetUpdate.congr
    intro z hz
    exact Matrix.adjugate_apply (G z) i j
  intro i j
  have hEq : (fun z ↦ (G z)⁻¹ i j) =
      fun z ↦ ((G z).det)⁻¹ * (G z).adjugate i j := by
    funext z
    rw [Matrix.inv_def]
    simp [Matrix.smul_apply, Ring.inverse_eq_inv]
  rw [hEq]
  exact hinvdet.mul (hadj i j)

private theorem contDiffOn_chart_perturbed_metric_inv_entries_of_solves
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2) (x : M)
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (hUtarget : U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∀ p ∈ S, ∀ i j, ContDiffOn ℝ ∞ (fun z ↦
      (ω₀.metricInChart x z + complexHessian
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ i j) U := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  intro p hp i j
  have hpot : ω₀.IsPotential p.2 := (hS p hp).2.1
  have hpotOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.2 Set.univ :=
    contMDiffOn_univ.mpr hpot.contMDiff
  have hcoord : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
      ∞ (p.2 ∘ e.symm) e.target := by
    exact hpotOn.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)
  have hcoord' : ContDiffOn ℝ ∞ (p.2 ∘ e.symm) e.target := hcoord.contDiffOn
  have hhess := contDiffOn_complexHessian_entries_of_contDiffOn_local
    (isOpen_extChartAt_target x) (p.2 ∘ e.symm) hcoord'
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun z ↦
    ω₀.metricInChart x z + complexHessian (p.2 ∘ e.symm) z
  have hG : ∀ a b, ContDiffOn ℝ ∞ (fun z ↦ G z a b) U := by
    intro a b
    exact ((ω₀.contDiffOn_metricInChart x a b).add (hhess a b)).mono hUtarget
  have hdet : ∀ z ∈ U, (G z).det ≠ 0 := by
    intro z hz
    have hpos : (G z).PosDef := by
      simpa [G, e, ω₀.metricInChart_perturb hpot x (hUtarget hz)] using
        (ω₀.perturb p.2 hpot).posDef_metricInChart x (hUtarget hz)
    have hunit : IsUnit (G z) := Matrix.PosDef.isUnit hpos
    have hunitdet : IsUnit (G z).det := (G z).isUnit_iff_isUnit_det.mp hunit
    exact hunitdet.ne_zero
  have hInv := contDiffOn_matrixInverse_entries_of_contDiffOn_local hG hdet
  simpa [G, e] using hInv i j

private theorem holderBoundOn_of_interior_schauder
    {n r : ℕ} {α lam CA CR Cφ : ℝ≥0}
    (hSch : InteriorSchauderEstimate n) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hr : 2 ≤ r) (hlam : 0 < lam) {U V : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hV : IsCompact (closure V)) (hVU : closure V ⊆ U)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (hA : ∀ j l, ContDiffOn ℝ ∞ (fun z ↦ A z j l) U)
    (hu : ContDiffOn ℝ ∞ u U)
    (hEll : IsUniformlyEllipticOn A lam U)
    (hAHolder : ∀ j l, HolderBoundOn (r - 2) α CA U (fun z ↦ A z j l))
    (hLuHolder : HolderBoundOn (r - 2) α CR U (complexEllipticOp A u))
    (huBound : ∀ z ∈ U, |u z| ≤ Cφ) :
    HolderBoundOn r α
      ((Classical.choose (hSch.holderBoundOn_of_contDiffOn (r - 2) α hα₀ hα₁
        lam CA hlam U V hU hV hVU)) * (CR + Cφ)) V u := by
  have hC := Classical.choose_spec (hSch.holderBoundOn_of_contDiffOn (r - 2) α
    hα₀ hα₁ lam CA hlam U V hU hV hVU)
  have hrEq : (r - 2) + 2 = r := by omega
  simpa only [hrEq] using
    hC A u hA hu hEll hAHolder Cφ CR hLuHolder huBound

private theorem holderBoundOn_congr_of_eqOn_open
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} {k : ℕ} {α C : ℝ≥0}
    (hU : IsOpen U) (hKU : K ⊆ U) (f g : E → F)
    (hfg : EqOn f g U) (hbound : HolderBoundOn k α C K f) :
    HolderBoundOn k α C K g := by
  have hiter (j : ℕ) (z : E) (hz : z ∈ K) :
      iteratedFDeriv ℝ j f z = iteratedFDeriv ℝ j g z := by
    have hloc : f =ᶠ[𝓝 z] g := by
      filter_upwards [hU.mem_nhds (hKU hz)] with y hy
      exact hfg hy
    exact (hloc.iteratedFDeriv ℝ j).eq_of_nhds
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    rw [← hiter j z hz]
    exact hbound.1 j hj z hz
  · intro x hx y hy
    rw [← hiter k x hx, ← hiter k y hy]
    exact hbound.2 x hx y hy

private theorem holderBoundOn_directional_of_schauder
    {n r : ℕ} {α lam CA CR Cφ : ℝ≥0}
    (hSch : InteriorSchauderEstimate n) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hr : 2 ≤ r) (hlam : 0 < lam) {U V : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hV : IsCompact (closure V)) (hVU : closure V ⊆ U)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (v : EuclideanSpace ℂ (Fin n))
    (hA : ∀ j l, ContDiffOn ℝ ∞ (fun z ↦ A z j l) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hCurrent : HolderBoundOn r α Cφ (closure U) f)
    (hEll : IsUniformlyEllipticOn A lam U)
    (hAHolder : ∀ j l, HolderBoundOn (r - 2) α CA U (fun z ↦ A z j l))
    (rhs : EuclideanSpace ℂ (Fin n) → ℝ)
    (hRhs : HolderBoundOn (r - 2) α CR U rhs)
    (hEq : ∀ z ∈ U, complexEllipticOp A (fun y ↦ fderiv ℝ f y v) z = rhs z)
    (hv : ‖v‖ ≤ 1) :
    HolderBoundOn r α
      ((Classical.choose (hSch.holderBoundOn_of_contDiffOn (r - 2) α hα₀ hα₁
        lam CA hlam U V hU hV hVU)) * (CR + Cφ)) V (fun z ↦ fderiv ℝ f z v) := by
  let u : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ fderiv ℝ f z v
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hu : ContDiffOn ℝ ∞ u U := by
    dsimp [u]
    exact hfd.clm_apply contDiffOn_const
  have hLu : HolderBoundOn (r - 2) α CR U (complexEllipticOp A u) :=
    holderBoundOn_congr_of_eqOn_open hU (Set.Subset.refl U) rhs (complexEllipticOp A u)
      (fun z hz ↦ (hEq z hz).symm) hRhs
  have huBound : ∀ z ∈ U, |u z| ≤ Cφ := by
    intro z hz
    have hfirst := hCurrent.1 1 (by omega) z (subset_closure hz)
    have hnorm : ‖fderiv ℝ f z‖ ≤ Cφ := by
      simpa [norm_iteratedFDeriv_fderiv] using hfirst
    calc
      |u z| = ‖fderiv ℝ f z v‖ := by simp [u, Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ f z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Cφ * 1 := mul_le_mul hnorm hv (norm_nonneg _) (by positivity)
      _ = Cφ := by simp
  simpa [u] using holderBoundOn_of_interior_schauder hSch hα₀ hα₁
    hr hlam hU hV hVU A u hA hu hEll hAHolder hLu huBound

private theorem finiteDimensional_iteratedCML_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ) : FiniteDimensional ℝ (E [×k]→L[ℝ] ℝ) := by
  induction k with
  | zero =>
      exact Module.Finite.equiv (continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.symm
  | succ k ih =>
      have : FiniteDimensional ℝ (E →L[ℝ] (E [×k]→L[ℝ] ℝ)) := by infer_instance
      exact Module.Finite.equiv
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ).toLinearEquiv.symm

/-- On a finite-dimensional domain, finitely many basis evaluations control the operator norm of a
continuous multilinear form. The constant depends only on the basis and the order. -/
private theorem exists_basisComponent_opNorm_bound_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (k : ℕ) :
    ∃ C : ℝ≥0, ∀ T : E [×k]→L[ℝ] ℝ,
      ‖T‖ ≤ C * ∑ v : (Fin k → ι), ‖T (fun i ↦ b (v i))‖ := by
  classical
  let L : (E [×k]→L[ℝ] ℝ) →ₗ[ℝ] ((Fin k → ι) → ℝ) := {
    toFun := fun T v ↦ T (fun i ↦ b (v i))
    map_add' := by intro T S; ext v; simp
    map_smul' := by intro c T; ext v; simp }
  have hLin : Function.Injective L := by
    intro T S h
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    apply Module.Basis.ext_multilinear (fun _ : Fin k ↦ b)
    intro v
    exact congrFun h v
  have hKer : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot.mpr hLin
  let _ : FiniteDimensional ℝ (E [×k]→L[ℝ] ℝ) := finiteDimensional_iteratedCML_local k
  obtain ⟨C, hCpos, hAnti⟩ := LinearMap.exists_antilipschitzWith L hKer
  refine ⟨C, ?_⟩
  intro T
  have hAnti0 := hAnti.le_mul_dist T 0
  rw [dist_eq_norm, map_zero, dist_eq_norm, sub_zero] at hAnti0
  have hsup : Finset.univ.sup (fun v : Fin k → ι ↦ ‖L T v‖₊) ≤
      ∑ v : Fin k → ι, ‖L T v‖₊ := by
    apply Finset.sup_le
    intro v hv
    apply Finset.single_le_sum (f := fun w : Fin k → ι ↦ ‖L T w‖₊)
    · intro w hw
      exact zero_le
    · exact Finset.mem_univ v
  have hnorm : ‖L T‖ ≤ ∑ v : (Fin k → ι), ‖L T v‖ := by
    change (↑(Finset.univ.sup fun v : Fin k → ι ↦ ‖L T v‖₊) : ℝ) ≤ _
    calc
      _ ≤ (↑(∑ v : Fin k → ι, ‖L T v‖₊) : ℝ) := by exact_mod_cast hsup
      _ = ∑ v : Fin k → ι, ‖L T v‖ := by simp
  calc
    ‖T‖ ≤ C * ‖L T‖ := by simpa [map_zero] using hAnti0
    _ ≤ C * (∑ v : (Fin k → ι), ‖L T v‖) := by gcongr
    _ = C * ∑ v : (Fin k → ι), ‖T (fun i ↦ b (v i))‖ := by rfl

private theorem holderOnWith_cml_of_basis_components_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {k : ℕ} {α C COp : ℝ≥0} {K : Set E}
    (hOp : ∀ T : E [×k]→L[ℝ] ℝ,
      ‖T‖ ≤ COp * ∑ v : (Fin k → ι), ‖T (fun i ↦ b (v i))‖)
    (F : E → (E [×k]→L[ℝ] ℝ))
    (hComp : ∀ v : Fin k → ι,
      HolderOnWith C α (fun z ↦ F z (fun i ↦ b (v i))) K) :
    HolderOnWith (COp * (Fintype.card (Fin k → ι) : ℝ≥0) * C) α F K := by
  classical
  let N : ℝ≥0 := Fintype.card (Fin k → ι)
  let C' : ℝ≥0 := COp * N * C
  change HolderOnWith C' α F K
  intro z hz w hw
  let D : ℝ := dist z w ^ (α : ℝ)
  have hD : 0 ≤ D := Real.rpow_nonneg (dist_nonneg) _
  have hsum : ∑ v : Fin k → ι, ‖(F z - F w) (fun i ↦ b (v i))‖ ≤
      (N : ℝ) * ((C : ℝ) * D) := by
    calc
      _ ≤ Fintype.card (Fin k → ι) • ((C : ℝ) * D) := by
        apply Finset.sum_le_card_nsmul
        intro v hv
        have h := (hComp v).dist_le hz hw
        simpa [D, dist_eq_norm, sub_apply] using h
      _ = (N : ℝ) * ((C : ℝ) * D) := by simp [N, nsmul_eq_mul]
  have hreal : ‖F z - F w‖ ≤ (C' : ℝ) * D := by
    calc
      ‖F z - F w‖ ≤ COp * ∑ v : Fin k → ι,
          ‖(F z - F w) (fun i ↦ b (v i))‖ := hOp (F z - F w)
      _ ≤ COp * ((N : ℝ) * ((C : ℝ) * D)) := by gcongr
      _ = (C' : ℝ) * D := by simp [C', mul_assoc]
  calc
    edist (F z) (F w) = ENNReal.ofReal (‖F z - F w‖) := by
      rw [edist_dist, dist_eq_norm]
    _ ≤ ENNReal.ofReal ((C' : ℝ) * D) := ENNReal.ofReal_le_ofReal hreal
    _ = (C' : ENNReal) * edist z w ^ (α : ℝ) := by
      change ENNReal.ofReal ((C' : ℝ) * dist z w ^ (α : ℝ)) = _
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) (NNReal.coe_nonneg α), edist_dist]

private theorem iteratedFDeriv_directional_snoc_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (r : ℕ) (v : E) (m : Fin r → E) :
    iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ f y v) z m =
      iteratedFDeriv ℝ (r + 1) f z (Fin.snoc m v) := by
  let T : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  have hfd : ContDiffAt ℝ r (fderiv ℝ f) z := by
    have hrtop : (↑(r + 1) : ℕ∞ω) ≤ ∞ := by
      exact_mod_cast (show (r + 1 : ℕ∞) ≤ ⊤ from le_top)
    exact hf.fderiv_right hrtop
  have hiter : iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ f y v) z =
      T.compContinuousMultilinearMap (iteratedFDeriv ℝ r (fderiv ℝ f) z) := by
    change iteratedFDeriv ℝ r (T ∘ fderiv ℝ f) z = _
    simpa [T, Function.comp_apply, ContinuousLinearMap.apply_apply] using
      T.iteratedFDeriv_comp_left hfd (i := r) (by exact_mod_cast le_rfl)
  have hq : (continuousMultilinearCurryRightEquiv' ℝ r E ℝ)
      (iteratedFDeriv ℝ (r + 1) f z) = iteratedFDeriv ℝ r (fderiv ℝ f) z := by
    have hsucc := iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := f) (n := r) (x := z)
    have hq0 := congrArg (continuousMultilinearCurryRightEquiv' ℝ r E ℝ) hsucc
    simpa [Function.comp_apply] using hq0
  calc
    iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ f y v) z m =
        (T.compContinuousMultilinearMap (iteratedFDeriv ℝ r (fderiv ℝ f) z)) m := by rw [hiter]
    _ = T ((iteratedFDeriv ℝ r (fderiv ℝ f) z) m) := by rfl
    _ = T (((continuousMultilinearCurryRightEquiv' ℝ r E ℝ)
        (iteratedFDeriv ℝ (r + 1) f z)) m) := by rw [hq]
    _ = iteratedFDeriv ℝ (r + 1) f z (Fin.snoc m v) := by
      simp [T, ContinuousLinearMap.apply_apply]

private theorem iteratedFDeriv_top_basisTuple_eq_directional_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (b : ι → E) {f : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ ∞ f z) (r : ℕ) (ξ : Fin (r + 1) → ι) :
    iteratedFDeriv ℝ (r + 1) f z (fun q ↦ b (ξ q)) =
      iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ f y (b (ξ (Fin.last r)))) z
        (fun q ↦ b (ξ q.castSucc)) := by
  let v := b (ξ (Fin.last r))
  let m : Fin r → E := fun q ↦ b (ξ q.castSucc)
  have htuple : Fin.snoc m v = fun q ↦ b (ξ q) := by
    funext q
    refine Fin.lastCases ?_ ?_ q
    · simp [v, m]
    · intro j
      simp [m]
  calc
    iteratedFDeriv ℝ (r + 1) f z (fun q ↦ b (ξ q)) =
        iteratedFDeriv ℝ (r + 1) f z (Fin.snoc m v) := by rw [← htuple]
    _ = iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ f y v) z m :=
      (iteratedFDeriv_directional_snoc_local hf r v m).symm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
/-- The order `r-2` interior estimate for the linearized equation, applied in every coordinate
direction of the real basis of `ℂⁿ` (both `e_i` and `I • e_i`), gives a uniform order `r+1`
bound for the potential on `K'`. -/
theorem exists_uniform_chart_holder_bound_succ_of_schauder_data
    (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    {x : M} {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    {r : ℕ} (hr : 2 ≤ r) {Cφ CA CR : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    (hUopen : IsOpen U)
    (hUtarget : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hCurrent : ∀ p ∈ S,
      HolderBoundOn r α Cφ (closure U)
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm))
    (K' : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K') (hKU : K' ⊆ U)
    (lam : ℝ≥0) (hlam : 0 < lam)
    (hUniformElliptic : ∀ p ∈ S, IsUniformlyEllipticOn
      (fun z ↦ (ω₀.metricInChart x z +
        complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹)
      lam U)
    (hCoeff : ∀ p ∈ S, ∀ j k,
      HolderBoundOn (r - 2) α CA U (fun z ↦
        (ω₀.metricInChart x z +
          complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ j k))
    (hRhs : ∀ p ∈ S, ∀ i : Fin n, ∀ β : ℂ,
      (β = 1 ∨ β = Complex.I) → HolderBoundOn (r - 2) α CR U (fun z ↦
        fderiv ℝ (p.1 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z
            (β • EuclideanSpace.single i 1) -
          RCLike.re (((ω₀.metricInChart x z +
            complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ *
              (Matrix.of fun j k ↦ fderiv ℝ
                (fun u ↦ ω₀.metricInChart x u j k) z (β • EuclideanSpace.single i 1))).trace) +
          RCLike.re ((ω₀.metricInChart x z)⁻¹ *
            (Matrix.of fun j k ↦ fderiv ℝ
              (fun u ↦ ω₀.metricInChart x u j k) z (β • EuclideanSpace.single i 1))).trace))
    (hLinearized : ∀ p ∈ S, ∀ z ∈ U, ∀ v : EuclideanSpace ℂ (Fin n),
      complexEllipticOp (fun _ ↦
        (ω₀.metricInChart x z +
          complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹)
        (fun u ↦ fderiv ℝ
          (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) u v) z =
      fderiv ℝ (p.1 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z v -
        RCLike.re (((ω₀.metricInChart x z +
          complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ *
            (Matrix.of fun j k ↦
              fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v)).trace) +
        RCLike.re ((ω₀.metricInChart x z)⁻¹ *
          (Matrix.of fun j k ↦
            fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v)).trace) :
    ∃ C : ℝ≥0, ∀ p ∈ S,
      HolderBoundOn (r + 1) α C K'
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hKclosure : closure K' = K' := closure_eq_iff_isClosed.mpr hK.isClosed
  have hKclosurecompact : IsCompact (closure K') := by simpa [hKclosure] using hK
  have hKclosureU : closure K' ⊆ U := by simpa [hKclosure] using hKU
  let Cdir : ℝ≥0 :=
    (Classical.choose (hSch.holderBoundOn_of_contDiffOn (r - 2) α hα₀ hα₁
      lam CA hlam U K' hUopen hKclosurecompact hKclosureU)) * (CR + Cφ)
  have hDirectional : ∀ p ∈ S, ∀ i : Fin n, ∀ β : ℂ,
      (β = 1 ∨ β = Complex.I) → HolderBoundOn r α Cdir K'
        (fun z ↦ fderiv ℝ (p.2 ∘ e.symm) z (β • EuclideanSpace.single i 1)) := by
    intro p hp i β hβ
    let f : EuclideanSpace ℂ (Fin n) → ℝ := p.2 ∘ e.symm
    let A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun z ↦
      (ω₀.metricInChart x z + complexHessian f z)⁻¹
    let v : EuclideanSpace ℂ (Fin n) := β • EuclideanSpace.single i 1
    have htarget : U ⊆ e.target := fun z hz ↦ hUtarget (subset_closure hz)
    have hA : ∀ j k, ContDiffOn ℝ ∞ (fun z ↦ A z j k) U := by
      intro j k
      simpa [A, f, e] using
        contDiffOn_chart_perturbed_metric_inv_entries_of_solves ω₀ S hS x htarget p hp j k
    have hpot : ω₀.IsPotential p.2 := (hS p hp).2.1
    have hpotOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.2 Set.univ :=
      contMDiffOn_univ.mpr hpot.contMDiff
    have hcoord : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
        ∞ f e.target := by
      simpa [f, e] using
        hpotOn.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)
    have hf : ContDiffOn ℝ ∞ f U := hcoord.contDiffOn.mono htarget
    have hCurrentP : HolderBoundOn r α Cφ (closure U) f := by
      simpa [f, e] using hCurrent p hp
    have hEll : IsUniformlyEllipticOn A lam U := by
      simpa [A, f, e] using hUniformElliptic p hp
    have hAHolder : ∀ j k, HolderBoundOn (r - 2) α CA U (fun z ↦ A z j k) := by
      intro j k
      simpa [A, f, e] using hCoeff p hp j k
    let rhs : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
      fderiv ℝ (p.1 ∘ e.symm) z v -
        RCLike.re (((ω₀.metricInChart x z + complexHessian f z)⁻¹ *
          (Matrix.of fun j k ↦ fderiv ℝ
            (fun u ↦ ω₀.metricInChart x u j k) z v)).trace) +
        RCLike.re ((ω₀.metricInChart x z)⁻¹ *
          (Matrix.of fun j k ↦ fderiv ℝ
            (fun u ↦ ω₀.metricInChart x u j k) z v)).trace
    have hRhsP : HolderBoundOn (r - 2) α CR U rhs := by
      simpa [rhs, v, f, e] using hRhs p hp i β hβ
    have hEq : ∀ z ∈ U,
        complexEllipticOp A (fun y ↦ fderiv ℝ f y v) z = rhs z := by
      intro z hz
      change complexEllipticOp (fun _ ↦
        (ω₀.metricInChart x z + complexHessian (p.2 ∘ e.symm) z)⁻¹)
        (fun u ↦ fderiv ℝ (p.2 ∘ e.symm) u v) z = rhs z
      simpa [rhs, v, f, e] using hLinearized p hp z hz v
    have hv : ‖v‖ ≤ 1 := by
      have hsingle : ‖EuclideanSpace.single i (1 : ℂ)‖ = 1 := by simp
      rw [norm_smul, hsingle]
      rcases hβ with hβ | hβ
      · rw [hβ, norm_one]
        norm_num
      · rw [hβ, Complex.norm_I]
        norm_num
    simpa [Cdir, f, v, e] using
      holderBoundOn_directional_of_schauder hSch hα₀ hα₁ hr hlam
        hUopen hKclosurecompact hKclosureU A f v hA hf hCurrentP hEll hAHolder
        rhs hRhsP hEq hv
  let b : Module.Basis (Σ _i : Fin n, Fin 2) ℝ (EuclideanSpace ℂ (Fin n)) :=
    (Pi.basis fun _ : Fin n => Complex.basisOneI).map
      ((EuclideanSpace.equiv (Fin n) ℂ).toLinearEquiv.restrictScalars ℝ).symm
  have hbZero (i : Fin n) : b ⟨i, 0⟩ = EuclideanSpace.single i 1 := by
    simp [b, Pi.basis_apply, Complex.coe_basisOneI, PiLp.toLp_single]
  have hbOne (i : Fin n) : b ⟨i, 1⟩ = Complex.I • EuclideanSpace.single i 1 := by
    simp [b, Pi.basis_apply, Complex.coe_basisOneI, PiLp.toLp_single]
    ext j
    simp [PiLp.single_apply]
  have hbNorm (η : (i : Fin n) × Fin 2) : ‖b η‖ = 1 := by
    rcases η with ⟨i, j⟩
    fin_cases j
    · simp [hbZero]
    · change ‖b ⟨i, 1⟩‖ = 1
      rw [hbOne, norm_smul, Complex.norm_I]
      simp
  have hSmooth : ∀ p ∈ S, ContDiffOn ℝ ∞ (p.2 ∘ e.symm) U := by
    intro p hp
    have hpot : ω₀.IsPotential p.2 := (hS p hp).2.1
    have hpotOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.2 Set.univ :=
      contMDiffOn_univ.mpr hpot.contMDiff
    have hcoord : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
        ∞ (p.2 ∘ e.symm) e.target := by
      simpa [e] using
        hpotOn.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)
    exact hcoord.contDiffOn.mono (fun z hz ↦ hUtarget (subset_closure hz))
  have hDirectionBasis : ∀ p ∈ S, ∀ η : (i : Fin n) × Fin 2,
      HolderBoundOn r α Cdir K'
        (fun z ↦ fderiv ℝ (p.2 ∘ e.symm) z (b η)) := by
    intro p hp η
    rcases η with ⟨i, j⟩
    fin_cases j
    · simpa [hbZero] using hDirectional p hp i 1 (Or.inl rfl)
    · simpa [hbOne] using hDirectional p hp i Complex.I (Or.inr rfl)
  let COp : ℝ≥0 := Classical.choose
    (exists_basisComponent_opNorm_bound_local b (r + 1))
  have hCOp : ∀ T : (EuclideanSpace ℂ (Fin n) [×(r + 1)]→L[ℝ] ℝ),
      ‖T‖ ≤ COp * ∑ ξ : (Fin (r + 1) → ((i : Fin n) × Fin 2)),
        ‖T (fun q ↦ b (ξ q))‖ := by
    exact Classical.choose_spec (exists_basisComponent_opNorm_bound_local b (r + 1))
  let Ctop : ℝ≥0 := COp *
    (Fintype.card (Fin (r + 1) → ((i : Fin n) × Fin 2)) : ℝ≥0) * Cdir
  have hComponentEq : ∀ p ∈ S, ∀ ξ : Fin (r + 1) → ((i : Fin n) × Fin 2),
      ∀ z ∈ K',
      iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) z (fun q ↦ b (ξ q)) =
        iteratedFDeriv ℝ r
          (fun y ↦ fderiv ℝ (p.2 ∘ e.symm) y (b (ξ (Fin.last r)))) z
          (fun q ↦ b (ξ q.castSucc)) := by
    intro p hp ξ z hz
    have hfz : ContDiffAt ℝ ∞ (p.2 ∘ e.symm) z :=
      (hSmooth p hp).contDiffAt (hUopen.mem_nhds (hKU hz))
    exact iteratedFDeriv_top_basisTuple_eq_directional_local b hfz r ξ
  have hTopComponentPoint : ∀ p ∈ S, ∀ ξ : Fin (r + 1) → ((i : Fin n) × Fin 2),
      ∀ z ∈ K',
      ‖iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) z (fun q ↦ b (ξ q))‖ ≤ Cdir := by
    intro p hp ξ z hz
    let η := ξ (Fin.last r)
    let m : Fin r → EuclideanSpace ℂ (Fin n) := fun q ↦ b (ξ q.castSucc)
    let g : EuclideanSpace ℂ (Fin n) → ℝ := fun y ↦
      fderiv ℝ (p.2 ∘ e.symm) y (b η)
    have hDir : HolderBoundOn r α Cdir K' g := by
      simpa [g, η] using hDirectionBasis p hp η
    rw [hComponentEq p hp ξ z hz]
    calc
      ‖iteratedFDeriv ℝ r g z m‖ ≤
          ‖iteratedFDeriv ℝ r g z‖ * ∏ q, ‖m q‖ :=
        (iteratedFDeriv ℝ r g z).le_opNorm m
      _ = ‖iteratedFDeriv ℝ r g z‖ := by simp [m, hbNorm]
      _ ≤ Cdir := hDir.1 r le_rfl z hz
  have hTopComponentHolder : ∀ p ∈ S, ∀ ξ : Fin (r + 1) → ((i : Fin n) × Fin 2),
      HolderOnWith Cdir α
        (fun z ↦ iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) z (fun q ↦ b (ξ q))) K' := by
    intro p hp ξ z hz w hw
    let η := ξ (Fin.last r)
    let m : Fin r → EuclideanSpace ℂ (Fin n) := fun q ↦ b (ξ q.castSucc)
    let g : EuclideanSpace ℂ (Fin n) → ℝ := fun y ↦
      fderiv ℝ (p.2 ∘ e.symm) y (b η)
    have hDir : HolderBoundOn r α Cdir K' g := by
      simpa [g, η] using hDirectionBasis p hp η
    change edist (iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) z (fun q ↦ b (ξ q)))
      (iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) w (fun q ↦ b (ξ q))) ≤ _
    rw [hComponentEq p hp ξ z hz, hComponentEq p hp ξ w hw]
    have hDirDist : dist (iteratedFDeriv ℝ r g z) (iteratedFDeriv ℝ r g w) ≤
        Cdir * dist z w ^ (α : ℝ) := hDir.2.dist_le hz hw
    have hEval : ‖iteratedFDeriv ℝ r g z m - iteratedFDeriv ℝ r g w m‖ ≤
        Cdir * dist z w ^ (α : ℝ) := by
      have hEvalOp : ‖(iteratedFDeriv ℝ r g z - iteratedFDeriv ℝ r g w) m‖ ≤
          ‖iteratedFDeriv ℝ r g z - iteratedFDeriv ℝ r g w‖ * ∏ q, ‖m q‖ :=
        (iteratedFDeriv ℝ r g z - iteratedFDeriv ℝ r g w).le_opNorm m
      calc
        ‖iteratedFDeriv ℝ r g z m - iteratedFDeriv ℝ r g w m‖ =
            ‖(iteratedFDeriv ℝ r g z - iteratedFDeriv ℝ r g w) m‖ := by rw [sub_apply]
        _ ≤ ‖iteratedFDeriv ℝ r g z - iteratedFDeriv ℝ r g w‖ := by
          simpa [m, hbNorm] using hEvalOp
        _ = dist (iteratedFDeriv ℝ r g z) (iteratedFDeriv ℝ r g w) := by rw [← dist_eq_norm]
        _ ≤ Cdir * dist z w ^ (α : ℝ) := hDirDist
    calc
      edist (iteratedFDeriv ℝ r g z m) (iteratedFDeriv ℝ r g w m) =
          ENNReal.ofReal (‖iteratedFDeriv ℝ r g z m - iteratedFDeriv ℝ r g w m‖) := by
        rw [edist_dist, dist_eq_norm]
      _ ≤ ENNReal.ofReal ((Cdir : ℝ) * dist z w ^ (α : ℝ)) :=
        ENNReal.ofReal_le_ofReal hEval
      _ = (Cdir : ENNReal) * edist z w ^ (α : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) (NNReal.coe_nonneg α), edist_dist]
  have hTopHolder : ∀ p ∈ S,
      HolderOnWith Ctop α
        (fun z ↦ iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) z) K' := by
    intro p hp
    exact holderOnWith_cml_of_basis_components_local b hCOp
      (fun z ↦ iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) z)
      (hTopComponentHolder p hp)
  have hTopPoint : ∀ p ∈ S, ∀ z ∈ K',
      ‖iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) z‖ ≤ Ctop := by
    intro p hp z hz
    have hsum : ∑ ξ : Fin (r + 1) → ((i : Fin n) × Fin 2),
        ‖iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) z (fun q ↦ b (ξ q))‖ ≤
        (Fintype.card (Fin (r + 1) → ((i : Fin n) × Fin 2)) : ℝ) * Cdir := by
      calc
        _ ≤ ∑ _ξ : Fin (r + 1) → ((i : Fin n) × Fin 2), (Cdir : ℝ) :=
          Finset.sum_le_sum fun ξ hξ ↦ hTopComponentPoint p hp ξ z hz
        _ = _ := by simp
    calc
      ‖iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) z‖ ≤
          COp * ∑ ξ : Fin (r + 1) → ((i : Fin n) × Fin 2),
            ‖iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) z (fun q ↦ b (ξ q))‖ :=
        hCOp (iteratedFDeriv ℝ (r + 1) (p.2 ∘ e.symm) z)
      _ ≤ COp * ((Fintype.card (Fin (r + 1) → ((i : Fin n) × Fin 2)) : ℝ) * Cdir) := by
        gcongr
      _ = Ctop := by simp [Ctop, mul_assoc]
  refine ⟨max Cφ Ctop, ?_⟩
  intro p hp
  let f : EuclideanSpace ℂ (Fin n) → ℝ := p.2 ∘ e.symm
  have hCurrentP : HolderBoundOn r α Cφ (closure U) f := by
    simpa [f, e] using hCurrent p hp
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    by_cases hjr : j ≤ r
    · have hzcl : z ∈ closure U := subset_closure (hKU hz)
      exact (hCurrentP.1 j hjr z hzcl).trans (le_max_left Cφ Ctop)
    · have hj' : j = r + 1 := by omega
      subst j
      exact (hTopPoint p hp z hz).trans (le_max_right Cφ Ctop)
  · exact (hTopHolder p hp).mono_const (le_max_right Cφ Ctop)

end KahlerForm

end
