module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.ChartInvariance

/-!
# Smoothness of the Calabi third-order energy

For a smooth Kähler potential, the perturbed metric is positive and smooth, so its inverse and
connection coefficients vary smoothly; their contracted squared norm is smooth as well.
This is the smoothness component of Székelyhidi, *An Introduction to Extremal Kähler Metrics*,
§3.3, equation (3.13), p. 45.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

open scoped ComplexOrder in
omit [T2Space M] [CompactSpace M] in
/-- The Calabi connection-difference energy is smooth for every Kähler potential. -/
theorem calabiEnergy_contMDiff (ω₀ : KahlerForm n M) {φ : M → ℝ}
    (hφ : ω₀.IsPotential φ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (calabiEnergy ω₀ φ) := by
  have contDiffOn_complexHessian_entries_of_contDiffOn
      {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
      {f : EuclideanSpace ℂ (Fin n) → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
      ∀ j k, ContDiffOn ℝ ∞ (fun z ↦ complexHessian f z j k) U := by
    have hddbar : ContDiffOn ℝ ∞ (ddbar f) U := ContDiffOn.ddbar hU hf
    intro j k
    let f₁ : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
      ddbar f z ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]
    let f₂ : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
      ddbar f z ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]
    have hf₁ : ContDiffOn ℝ ∞ f₁ U := by
      dsimp [f₁]
      exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]).contDiff).comp_contDiffOn
          hddbar
    have hf₂ : ContDiffOn ℝ ∞ f₂ U := by
      dsimp [f₂]
      exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]).contDiff).comp_contDiffOn hddbar
    have hf₁c : ContDiffOn ℝ ∞ (fun z ↦ (f₁ z : ℂ)) U := by
      convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₁ using 1
      ext z
      simp [f₁, Complex.ofRealCLM_apply]
    have hf₂c : ContDiffOn ℝ ∞ (fun z ↦ (f₂ z : ℂ)) U := by
      convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₂ using 1
      ext z
      simp [f₂, Complex.ofRealCLM_apply]
    have hformula : ContDiffOn ℝ ∞
        (fun z ↦ ((f₁ z : ℂ) - Complex.I * (f₂ z : ℂ)) / 2) U :=
      (hf₁c.sub (contDiffOn_const.mul hf₂c)).div_const (2 : ℂ)
    apply hformula.congr
    intro z hz
    change (ddbar f z).coeffMatrix j k = _
    simp [ContinuousAlternatingMap.coeffMatrix, f₁, f₂]

  have contDiffOn_matrixDet_of_contDiffOn_entries
      {U : Set (EuclideanSpace ℂ (Fin n))}
      {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
      (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U) :
      ContDiffOn ℝ ∞ (fun z ↦ (G z).det) U := by
    simp only [Matrix.det_apply]
    fun_prop

  have contDiffOn_matrixInverse_entries_of_contDiffOn
      {U : Set (EuclideanSpace ℂ (Fin n))}
      {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
      (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U)
      (hdet : ∀ z ∈ U, (G z).det ≠ 0) :
      ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ (G z)⁻¹ i j) U := by
    have hdetfun : ContDiffOn ℝ ∞ (fun z ↦ (G z).det) U :=
      contDiffOn_matrixDet_of_contDiffOn_entries hG
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
      have hdetUpdate := contDiffOn_matrixDet_of_contDiffOn_entries hUpdate
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

  have contDiffOn_c3PartialZ
      {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
      {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
      (hG : ∀ k l, ContDiffOn ℝ ∞ (fun z ↦ G z k l) U)
      (j k l : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ wirtingerDerivInChart (fun w ↦ G w k l) z j) U := by
    let f : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ G w k l
    have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) U :=
      (hG k l).fderiv_of_isOpen hU (by rw [ENat.coe_top_add_one])
    have hD₁ : ContDiffOn ℝ ∞
        (fun z ↦ fderiv ℝ f z (EuclideanSpace.single j 1)) U :=
      hD.clm_apply contDiffOn_const
    have hD₂ : ContDiffOn ℝ ∞
        (fun z ↦ fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) U :=
      hD.clm_apply contDiffOn_const
    change ContDiffOn ℝ ∞
      (fun z ↦ (fderiv ℝ f z (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2) U
    exact (hD₁.sub (contDiffOn_const.mul hD₂)).div_const (2 : ℂ)

  have contDiffOn_c3Christoffel
      {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
      {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
      (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U)
      (hGinv : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ (G z)⁻¹ i j) U)
      (i j k : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ christoffelInChart G z i j k) U := by
    have hterm (l : Fin n) : ContDiffOn ℝ ∞
        (fun z ↦ (G z)⁻¹ l i * wirtingerDerivInChart (fun w ↦ G w k l) z j) U := by
      exact (hGinv l i).mul (contDiffOn_c3PartialZ hU hG j k l)
    have hsum : ContDiffOn ℝ ∞
        (fun z ↦ ∑ l ∈ Finset.univ, (G z)⁻¹ l i * wirtingerDerivInChart (fun w ↦ G w k l) z j) U := by
      apply ContDiffOn.sum
      intro l hl
      exact hterm l
    change ContDiffOn ℝ ∞
      (fun z ↦ ∑ l ∈ Finset.univ, (G z)⁻¹ l i * wirtingerDerivInChart (fun w ↦ G w k l) z j) U
    exact hsum

  have contDiffOn_univ_sum
      {U : Set (EuclideanSpace ℂ (Fin n))}
      {f : Fin n → EuclideanSpace ℂ (Fin n) → ℂ}
      (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U) :
      ContDiffOn ℝ ∞ (fun x ↦ ∑ i, f i x) U := by
    have hsum : ContDiffOn ℝ ∞ (fun x ↦ ∑ i ∈ Finset.univ, f i x) U := by
      apply ContDiffOn.sum
      intro i hi
      exact hf i
    simpa using hsum

  have calabiEnergyInChart_contDiffOn
      (ω₀ : KahlerForm n M) (φ : M → ℝ) (x₀ : M)
      (hφ : ω₀.IsPotential φ) :
      ContDiffOn ℝ ∞ (fun z ↦ calabiEnergyInChart ω₀ φ x₀ z)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target := by
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
    let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun z ↦ ω₀.metricInChart x₀ z
    let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun z ↦ g₀ z + complexHessian (φ ∘ e.symm) z
    have hφon : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ Set.univ :=
      contMDiffOn_univ.mpr hφ.1
    have hφchart : ContDiffOn ℝ ∞ (φ ∘ e.symm) e.target := by
      have h := hφon.comp (contMDiffOn_extChartAt_symm x₀) (by intro z hz; simp)
      exact h.contDiffOn
    have hHess := contDiffOn_complexHessian_entries_of_contDiffOn
      (isOpen_extChartAt_target x₀) hφchart
    have hG₀ : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ g₀ z i j) e.target := by
      intro i j
      exact ω₀.contDiffOn_metricInChart x₀ i j
    have hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ g z i j) e.target := by
      intro i j
      exact (hG₀ i j).add (hHess i j)
    have hG₀det : ∀ z ∈ e.target, (g₀ z).det ≠ 0 := by
      intro z hz
      have hp := (ω₀.posDef_metricInChart x₀ hz).det_pos
      have hreal : 0 < RCLike.re (g₀ z).det := (RCLike.pos_iff.mp hp).1
      intro hzero
      rw [hzero] at hreal
      norm_num at hreal
    have hGdet : ∀ z ∈ e.target, (g z).det ≠ 0 := by
      intro z hz
      have hp := (ω₀.perturb φ hφ).posDef_metricInChart x₀ hz
      rw [KahlerForm.metricInChart_perturb hφ x₀ hz] at hp
      have hreal : 0 < RCLike.re (g z).det := (RCLike.pos_iff.mp hp.det_pos).1
      intro hzero
      rw [hzero] at hreal
      norm_num at hreal
    have hG₀inv := contDiffOn_matrixInverse_entries_of_contDiffOn hG₀ hG₀det
    have hGinv := contDiffOn_matrixInverse_entries_of_contDiffOn hG hGdet
    have hΓ₀ : ∀ i j k, ContDiffOn ℝ ∞
        (fun z ↦ christoffelInChart g₀ z i j k) e.target := by
      intro i j k
      exact contDiffOn_c3Christoffel (isOpen_extChartAt_target x₀) hG₀ hG₀inv i j k
    have hΓ : ∀ i j k, ContDiffOn ℝ ∞
        (fun z ↦ christoffelInChart g z i j k) e.target := by
      intro i j k
      exact contDiffOn_c3Christoffel (isOpen_extChartAt_target x₀) hG hGinv i j k
    have hT : ∀ i j k, ContDiffOn ℝ ∞
        (fun z ↦ connectionDifferenceInChart ω₀ φ x₀ z i j k) e.target := by
      intro i j k
      change ContDiffOn ℝ ∞
        (fun z ↦ christoffelInChart g z i j k - christoffelInChart g₀ z i j k) e.target
      exact (hΓ i j k).sub (hΓ₀ i j k)
    let F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n →
        EuclideanSpace ℂ (Fin n) → ℂ := fun i j k a b c z ↦
      g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
        connectionDifferenceInChart ω₀ φ x₀ z i j k *
        star (connectionDifferenceInChart ω₀ φ x₀ z a b c)
    have hF (i j k a b c : Fin n) : ContDiffOn ℝ ∞ (F i j k a b c) e.target := by
      have hstar : ContDiffOn ℝ ∞
          (fun z ↦ star (connectionDifferenceInChart ω₀ φ x₀ z a b c)) e.target := by
        convert Complex.conjCLE.contDiff.comp_contDiffOn (hT a b c) using 1
        ext z
        simp
      exact (((((hG i a).mul (hGinv b j)).mul (hGinv c k)).mul (hT i j k)).mul hstar)
    have hsumC (i j k a b : Fin n) : ContDiffOn ℝ ∞
        (fun z ↦ ∑ c, F i j k a b c z) e.target :=
      contDiffOn_univ_sum (fun c ↦ hF i j k a b c)
    have hsumB (i j k a : Fin n) : ContDiffOn ℝ ∞
        (fun z ↦ ∑ b, ∑ c, F i j k a b c z) e.target :=
      contDiffOn_univ_sum (fun b ↦ hsumC i j k a b)
    have hsumA (i j k : Fin n) : ContDiffOn ℝ ∞
        (fun z ↦ ∑ a, ∑ b, ∑ c, F i j k a b c z) e.target :=
      contDiffOn_univ_sum (fun a ↦ hsumB i j k a)
    have hsumK (i j : Fin n) : ContDiffOn ℝ ∞
        (fun z ↦ ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c z) e.target :=
      contDiffOn_univ_sum (fun k ↦ hsumA i j k)
    have hsumJ (i : Fin n) : ContDiffOn ℝ ∞
        (fun z ↦ ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c z) e.target :=
      contDiffOn_univ_sum (fun j ↦ hsumK i j)
    have hsumI : ContDiffOn ℝ ∞
        (fun z ↦ ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c z) e.target :=
      contDiffOn_univ_sum hsumJ
    have hsum : ContDiffOn ℝ ∞ (fun z ↦ ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
          connectionDifferenceInChart ω₀ φ x₀ z i j k *
          star (connectionDifferenceInChart ω₀ φ x₀ z a b c)) e.target := by
      simpa [F] using hsumI
    change ContDiffOn ℝ ∞ (fun z ↦ Complex.re (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
        connectionDifferenceInChart ω₀ φ x₀ z i j k *
        star (connectionDifferenceInChart ω₀ φ x₀ z a b c))) e.target
    convert Complex.reCLM.contDiff.comp_contDiffOn hsum using 1
    ext z
    exact (Complex.reCLM_apply _).symm

  have chartwiseCalabiEnergy_smooth_and_global (ω₀ : KahlerForm n M) {φ : M → ℝ}
      (hφ : ω₀.IsPotential φ) :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (calabiEnergy ω₀ φ) := by
    intro y
    rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
    simp only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ]
    let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
    let e := extChartAt I y
    let z := e y
    have hz : z ∈ e.target := mem_extChartAt_target y
    have hzN : e.target ∈ nhds z := (isOpen_extChartAt_target y).mem_nhds hz
    have hlocal : ContDiffAt ℝ ∞
        (fun u ↦ calabiEnergyInChart ω₀ φ y u) z :=
      (calabiEnergyInChart_contDiffOn ω₀ φ y hφ).contDiffAt hzN
    have hEq : (fun u ↦ calabiEnergy ω₀ φ (e.symm u)) =ᶠ[nhds z]
        (fun u ↦ calabiEnergyInChart ω₀ φ y u) := by
      filter_upwards [hzN] with u hu
      exact calabiEnergy_chartFormula ω₀ hφ y u hu
    exact hlocal.congr_of_eventuallyEq hEq
  exact chartwiseCalabiEnergy_smooth_and_global ω₀ hφ

end KahlerForm
