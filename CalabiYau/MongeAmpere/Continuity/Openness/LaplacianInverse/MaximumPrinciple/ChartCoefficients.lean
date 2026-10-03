module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Analysis.Elliptic.Schauder

/-!
# Local inverse-metric coefficient bounds

The compactness bridge to the explicit hypotheses of Gilbarg–Trudinger, Theorem 3.5.
A small closed coordinate ball has a positive uniform lower bound for the inverse metric
and a finite common bound on its entries. This module does not depend on the harmonic-kernel
parent, so every analytic child can remain below that parent without an import cycle.
-/

@[expose] public section

open scoped Manifold Topology ContDiff NNReal ComplexOrder Matrix
open Set Matrix

namespace KahlerForm

private theorem inverse_metric_entry_continuous
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M) (j k : Fin n) :
    ContDiffOn ℝ ∞ (fun z ↦ (ω₁.metricInChart x z)⁻¹ j k)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  let U := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z ↦ ω₁.metricInChart x z
  have hG (a b : Fin n) : ContDiffOn ℝ ∞ (fun z ↦ G z a b) U :=
    ω₁.contDiffOn_metricInChart x a b
  have hdet : ContDiffOn ℝ ∞ (fun z ↦ (G z).det) U := by
    simp_rw [Matrix.det_apply]
    fun_prop
  have hdet_ne {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U) : (G z).det ≠ 0 := by
    have hpos := (RCLike.pos_iff.mp (ω₁.posDef_metricInChart x hz).det_pos).1
    exact fun h ↦ hpos.ne' (congrArg RCLike.re h)
  have hdetInv : ContDiffOn ℝ ∞ (fun z ↦ ((G z).det)⁻¹) U :=
    hdet.inv (fun z hz ↦ hdet_ne hz)
  have hUpdate (r c s t : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ (G z).updateRow r (Pi.single c (1 : ℂ)) s t) U := by
    simp_rw [Matrix.updateRow_apply]
    by_cases hrs : s = r
    · subst s
      simp only [Pi.single_apply]
      exact contDiffOn_const
    · simp only [ite_eq_right hrs]
      exact hG s t
  have hAdj (a b : Fin n) : ContDiffOn ℝ ∞ (fun z ↦ (G z).adjugate a b) U := by
    simp_rw [Matrix.adjugate_apply, Matrix.det_apply']
    apply ContDiffOn.sum
    intro σ hσ
    have hp : ContDiffOn ℝ ∞ (fun z ↦
        ∏ t, (G z).updateRow b (Pi.single a (1 : ℂ)) (σ t) t) U :=
      contDiffOn_prod (t := Finset.univ) (fun t ht ↦ hUpdate b a (σ t) t)
    change ContDiffOn ℝ ∞ (fun z ↦
      ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ t, (G z).updateRow b (Pi.single a (1 : ℂ)) (σ t) t) U
    exact contDiffOn_const.mul hp
  have hInv (a b : Fin n) : ContDiffOn ℝ ∞ (fun z ↦ (G z)⁻¹ a b) U := by
    have hmul : ContDiffOn ℝ ∞ (fun z ↦ ((G z).det)⁻¹ * (G z).adjugate a b) U :=
      hdetInv.mul (hAdj a b)
    refine hmul.congr ?_
    intro z hz
    rw [Matrix.inv_def]
    simp [Matrix.smul_apply, smul_eq_mul]
  simpa [U, G] using hInv j k

private theorem uniformly_elliptic_on_compact
    {n : ℕ} (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hAcont : ∀ j k, ContinuousOn (fun z ↦ A z j k) K)
    (hAherm : ∀ z ∈ K, (A z).IsHermitian)
    (hApos : ∀ z ∈ K, ∀ v, v ≠ 0 →
      0 < RCLike.re (star v ⬝ᵥ (A z *ᵥ v))) :
    ∃ lam : ℝ≥0, 0 < lam ∧ IsUniformlyEllipticOn A lam K := by
  classical
  by_cases hKne : K.Nonempty
  · by_cases hn : n = 0
    · subst n
      refine ⟨1, by norm_num, ?_⟩
      intro z hz
      constructor
      · exact hAherm z hz
      · intro v
        have hv : v = 0 := Subsingleton.elim _ _
        subst v
        simp
    · let S : Set (Fin n → ℂ) := Metric.sphere 0 1
      have hScompact : IsCompact S := by simpa [S] using (isCompact_sphere (0 : Fin n → ℂ) 1)
      let T : Set (EuclideanSpace ℂ (Fin n) × (Fin n → ℂ)) := K ×ˢ S
      have hTcompact : IsCompact T := hK.prod hScompact
      let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      let v₀ : Fin n → ℂ := Pi.single i₀ 1
      have hv₀norm : ‖v₀‖ = 1 := by simp [v₀, Pi.norm_single]
      have hTne : T.Nonempty := by
        obtain ⟨z, hz⟩ := hKne
        refine ⟨(z, v₀), ?_⟩
        constructor
        · exact hz
        · simpa [S, Metric.mem_sphere, dist_eq_norm] using hv₀norm
      let Q : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) → ℝ := fun p ↦
        RCLike.re (star p.2 ⬝ᵥ (A p.1 *ᵥ p.2))
      have hAcontProd (j k : Fin n) : ContinuousOn (fun p ↦ A p.1 j k) T :=
        (hAcont j k).comp continuousOn_fst (fun p hp ↦ hp.1)
      have hcoord (k : Fin n) : ContinuousOn
          (fun p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) ↦ p.2 k) T := by fun_prop
      let inner (j : Fin n) (p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ)) :=
        ∑ k, A p.1 j k * p.2 k
      have hinner (j : Fin n) : ContinuousOn (inner j) T := by
        dsimp [inner]
        apply continuousOn_finsetSum
        intro k hk
        exact (hAcontProd j k).mul (hcoord k)
      have hterm (j : Fin n) : ContinuousOn
          (fun p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) ↦
            Complex.re (star (p.2 j) * inner j p)) T := by
        have hm : ContinuousOn (fun p ↦ star (p.2 j) * inner j p) T :=
          (hcoord j).star.mul (hinner j)
        exact Complex.continuous_re.continuousOn.comp hm (fun p hp ↦ Set.mem_univ _)
      have hQsum : ContinuousOn (fun p ↦ ∑ j, Complex.re
          (star (p.2 j) * ∑ k, A p.1 j k * p.2 k)) T := by
        apply continuousOn_finsetSum
        intro j hj
        exact hterm j
      have hQcont : ContinuousOn Q T := by
        refine hQsum.congr ?_
        intro p hp
        simp [Q, Matrix.mulVec, dotProduct]
      have hQpos (p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ)) (hp : p ∈ T) : 0 < Q p := by
        have hvnorm : ‖p.2‖ = 1 := by
          have hs := Metric.mem_sphere.mp hp.2
          simpa [dist_eq_norm] using hs
        have hvne : p.2 ≠ 0 := by
          intro hv
          simp [hv] at hvnorm
        exact hApos p.1 hp.1 p.2 hvne
      obtain ⟨p₀, hp₀, hmin⟩ := hTcompact.exists_isMinOn hTne hQcont
      let δ : ℝ := Q p₀
      have hδ : 0 < δ := hQpos p₀ hp₀
      have hquad (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) (v : Fin n → ℂ) :
          δ * ‖v‖ ^ 2 ≤ RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
        by_cases hv : v = 0
        · simp [hv]
        · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
          let u : Fin n → ℂ := (‖v‖⁻¹ : ℝ) • v
          have hunorm : ‖u‖ = 1 := by
            calc
              ‖u‖ = ‖(‖v‖⁻¹ : ℝ) • v‖ := rfl
              _ = ‖v‖⁻¹ * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
              _ = 1 := by field_simp [ne_of_gt hnorm]
          have huSphere : u ∈ S := by simpa [S, Metric.mem_sphere, dist_eq_norm] using hunorm
          have hmin' : δ ≤ Q (z, u) := by
            dsimp [δ]
            exact (isMinOn_iff.mp hmin) (z, u) ⟨hz, huSphere⟩
          have hscale : Q (z, u) = (‖v‖⁻¹)^2 *
              RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
            dsimp [Q, u]
            simp [star_smul, Matrix.mulVec_smul, dotProduct_smul]
            ring
          have hmin'' : δ ≤ (‖v‖⁻¹)^2 * RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
            rw [hscale] at hmin'
            exact hmin'
          have hmul := mul_le_mul_of_nonneg_left hmin'' (sq_nonneg ‖v‖)
          calc
            δ * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 * ((‖v‖⁻¹)^2 *
                RCLike.re (star v ⬝ᵥ (A z *ᵥ v))) := by nlinarith
            _ = RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by field_simp [ne_of_gt hnorm]
      let lam : ℝ≥0 := ⟨δ / n, div_nonneg hδ.le (by positivity)⟩
      have hlam : 0 < lam := by
        dsimp [lam]
        exact div_pos hδ (by exact_mod_cast Nat.pos_of_ne_zero hn)
      refine ⟨lam, hlam, ?_⟩
      intro z hz
      constructor
      · exact hAherm z hz
      · intro v
        have hsum : ∑ j, ‖v j‖ ^ 2 ≤ (n : ℝ) * ‖v‖ ^ 2 := by
          calc
            ∑ j, ‖v j‖ ^ 2 ≤ ∑ j : Fin n, ‖v‖ ^ 2 :=
              Finset.sum_le_sum fun j hj ↦ by
                have h : ‖v j‖ ≤ ‖v‖ := by
                  have hnn : ‖v j‖₊ ≤ Finset.univ.sup (fun i : Fin n ↦ ‖v i‖₊) :=
                    Finset.le_sup (f := fun i : Fin n ↦ ‖v i‖₊) (Finset.mem_univ j)
                  calc
                    ‖v j‖ = (‖v j‖₊ : ℝ) := by norm_cast
                    _ ≤ ↑(Finset.univ.sup (fun i : Fin n ↦ ‖v i‖₊) : ℝ≥0) := by exact_mod_cast hnn
                    _ = ‖v‖ := rfl
                simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) h
            _ = (n : ℝ) * ‖v‖ ^ 2 := by simp
        calc
          (lam : ℝ) * ∑ j, ‖v j‖ ^ 2 ≤ δ * ‖v‖ ^ 2 := by
            dsimp [lam]
            calc
              (δ / (n : ℝ)) * ∑ j, ‖v j‖ ^ 2 ≤ (δ / (n : ℝ)) * ((n : ℝ) * ‖v‖ ^ 2) :=
                mul_le_mul_of_nonneg_left hsum (div_nonneg hδ.le (by positivity))
              _ = δ * ‖v‖ ^ 2 := by field_simp [ne_of_gt (by exact_mod_cast Nat.pos_of_ne_zero hn)]
          _ ≤ RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := hquad z hz v
  · exact ⟨1, by norm_num, by intro z hz; exact (hKne ⟨z, hz⟩).elim⟩

private theorem inverse_metric_bounds_on_compact
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M) (K : Set (EuclideanSpace ℂ (Fin n)))
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ lam B : ℝ≥0, 0 < lam ∧
      IsUniformlyEllipticOn (fun z ↦ (ω₁.metricInChart x z)⁻¹) lam K ∧
      ∀ z ∈ K, ∀ j k, ‖(ω₁.metricInChart x z)⁻¹ j k‖ ≤ (B : ℝ) := by
  classical
  let A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z ↦ (ω₁.metricInChart x z)⁻¹
  have hAcont : ∀ j k, ContinuousOn (fun z ↦ A z j k) K := by
    intro j k
    exact (inverse_metric_entry_continuous ω₁ x j k).continuousOn.mono hKU
  have hAherm : ∀ z ∈ K, (A z).IsHermitian := by
    intro z hz
    exact (ω₁.posDef_metricInChart x (hKU hz)).inv.isHermitian
  have hApos : ∀ z ∈ K, ∀ v, v ≠ 0 →
      0 < RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
    intro z hz v hv
    exact (RCLike.pos_iff.mp ((ω₁.posDef_metricInChart x (hKU hz)).inv.dotProduct_mulVec_pos hv)).1
  obtain ⟨lam, hlam, hEll⟩ := uniformly_elliptic_on_compact K hK A hAcont hAherm hApos
  let b (p : Fin n × Fin n) : ℝ := max 0 (Classical.choose
    (hK.exists_bound_of_continuousOn (hAcont p.1 p.2)))
  have hb (p : Fin n × Fin n) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) :
      ‖A z p.1 p.2‖ ≤ b p := by
    exact (Classical.choose_spec (hK.exists_bound_of_continuousOn (hAcont p.1 p.2)) z hz).trans
      (le_max_right 0 _)
  let B : ℝ≥0 := ⟨1 + ∑ p : Fin n × Fin n, b p, by
    dsimp [b]
    positivity⟩
  refine ⟨lam, B, hlam, ?_, ?_⟩
  · simpa [A] using hEll
  · intro z hz j k
    have hnonneg (p : Fin n × Fin n) : 0 ≤ b p := by
      dsimp [b]
      exact le_max_left 0 _
    have hle : b (j, k) ≤ ∑ p : Fin n × Fin n, b p :=
      Finset.single_le_sum (fun p hp ↦ hnonneg p) (Finset.mem_univ (j, k))
    calc
      ‖(ω₁.metricInChart x z)⁻¹ j k‖ = ‖A z j k‖ := rfl
      _ ≤ b (j, k) := hb (j, k) z hz
      _ ≤ ∑ p : Fin n × Fin n, b p := hle
      _ ≤ (B : ℝ) := by
        change (∑ p : Fin n × Fin n, b p) ≤ 1 + ∑ p : Fin n × Fin n, b p
        linarith

private theorem inverse_metric_chart_ball_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M) :
    ∃ (r : ℝ) (lam B : ℝ≥0), 0 < r ∧ 0 < lam ∧
      Metric.closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) r ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target ∧
      IsUniformlyEllipticOn (fun z ↦ (ω₁.metricInChart x z)⁻¹) lam
        (Metric.ball (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) r) ∧
      ∀ z ∈ Metric.ball (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) r,
        ∀ j k, ‖(ω₁.metricInChart x z)⁻¹ j k‖ ≤ (B : ℝ) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let c := e x
  obtain ⟨R, hRpos, hRball⟩ :=
    Metric.isOpen_iff.mp (isOpen_extChartAt_target x) c (mem_extChartAt_target x)
  let r : ℝ := R / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hclosed : Metric.closedBall c r ⊆ e.target := by
    intro z hz
    have hz' : dist z c ≤ r := by exact Metric.mem_closedBall.mp hz
    have hzball : z ∈ Metric.ball c R := by
      rw [Metric.mem_ball]
      dsimp [r] at hz'
      linarith
    exact hRball hzball
  have hK : IsCompact (Metric.closedBall c r) := isCompact_closedBall _ _
  have hKU : Metric.closedBall c r ⊆ e.target := by simpa [c, e] using hclosed
  obtain ⟨lam, B, hlam, hEll, hB⟩ := inverse_metric_bounds_on_compact ω₁ x
    (Metric.closedBall c r) hK hKU
  refine ⟨r, lam, B, hr, hlam, ?_, ?_, ?_⟩
  · simpa [c, e] using hclosed
  · intro z hz
    exact hEll z (Metric.ball_subset_closedBall hz)
  · intro z hz j k
    exact hB z (Metric.ball_subset_closedBall hz) j k

/-- A positive-radius coordinate ball on which the inverse Kähler metric satisfies the
bounded-coefficient and positive-uniform-ellipticity hypotheses of the C² maximum principle. -/
theorem exists_chart_ball_inverse_metric_bounds {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M) :
    ∃ (r : ℝ) (lam K : ℝ≥0), 0 < r ∧ 0 < lam ∧
      Metric.closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) r ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target ∧
      IsUniformlyEllipticOn (fun y => (ω₁.metricInChart x y)⁻¹) lam
        (Metric.ball (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) r) ∧
      ∀ y ∈ Metric.ball (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) r,
        ∀ j k, ‖(ω₁.metricInChart x y)⁻¹ j k‖ ≤ (K : ℝ) := by
  exact inverse_metric_chart_ball_bounds ω₁ x

end KahlerForm
