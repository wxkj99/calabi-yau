module

public import CalabiYau.Geometry.Complex.Schauder.FiniteChart.Balls
public import CalabiYau.Geometry.Complex.Schauder.SchauderCompactness.ConvexJetLipschitz

/-!
# Uniform two-jet bounds after a chart change

GT, Lemma 6.36, p. 136, in fixed smooth coordinates. The chain rule is used on the
convex donor ball, not on an arbitrary compact gauge piece. The constant is common to
all functions of the sequence; smoothness alone would give only function-dependent constants.
-/

set_option autoImplicit false

@[expose] public section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

private theorem holderBoundOn_chart_of_gauge_bound {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (u : M → ℝ) (B : ℝ≥0)
    (hfinite : finiteChartHolderGauge cover 2 α u < ⊤)
    (hbound : (finiteChartHolderGauge cover 2 α u).toReal ≤ (B : ℝ)) :
    ∀ i : cover.ι, HolderBoundOn 2 α B (cover.piece i)
      (u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) := by
  have hg : ((finiteChartHolderGauge cover 2 α u).toNNReal : ℝ≥0∞) =
      finiteChartHolderGauge cover 2 α u :=
    ENNReal.coe_toNNReal (ne_of_lt hfinite)
  have hreal : ((finiteChartHolderGauge cover 2 α u).toNNReal : ℝ) ≤ (B : ℝ) := by
    rw [ENNReal.coe_toNNReal_eq_toReal]
    exact hbound
  have hnn : (finiteChartHolderGauge cover 2 α u).toNNReal ≤ B := by
    exact_mod_cast hreal
  have hgb : finiteChartHolderGauge cover 2 α u ≤ (B : ℝ≥0∞) := by
    rw [← hg]
    exact_mod_cast hnn
  intro i
  have hi : CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
      (u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) ≤
      (B : ℝ≥0∞) := (le_iSup _ i).trans hgb
  exact ⟨fun j hj z hz => CalabiYau.Schauder.spatialJet_norm_le hi hj hz,
    HolderWith.restrict_iff.mp
      (CalabiYau.Schauder.topSpatialJet_holderWith_restrict hi)⟩

private theorem finiteChartGauge_bound_on_piece {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (u : ℕ → M → ℝ) (B : ℝ≥0)
    (hfinite : ∀ j, finiteChartHolderGauge cover 2 α (u j) < ⊤)
    (hbound : ∀ j, (finiteChartHolderGauge cover 2 α (u j)).toReal ≤ (B : ℝ)) :
    ∀ j i, HolderBoundOn 2 α B (cover.piece i)
      (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) := by
  intro j i
  let G := finiteChartHolderGauge cover 2 α (u j)
  let C : ℝ≥0 := G.toNNReal
  have hC : C ≤ B := by
    have hreal : (C : ℝ) ≤ (B : ℝ) := by
      change (G.toNNReal : ℝ) ≤ (B : ℝ)
      rw [ENNReal.coe_toNNReal_eq_toReal]
      exact hbound j
    exact_mod_cast hreal
  have hfiniteG : G < ⊤ := hfinite j
  have hG : G ≤ (C : ENNReal) := by
    exact (ENNReal.coe_toNNReal hfiniteG.ne).ge
  have hpiece : HolderBoundOn 2 α C (cover.piece i)
      (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) := by
    refine ⟨?_, ?_⟩
    · intro k hk z hz
      have hi : CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
          (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) ≤
          (C : ENNReal) := by
        calc
          _ ≤ G := le_iSup _ i
          _ ≤ (C : ENNReal) := hG
      exact CalabiYau.Schauder.spatialJet_norm_le hi hk hz
    · have hi : CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
          (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) ≤
          (C : ENNReal) := calc
        _ ≤ G := le_iSup _ i
        _ ≤ (C : ENNReal) := hG
      exact HolderWith.restrict_iff.mp
        (CalabiYau.Schauder.topSpatialJet_holderWith_restrict hi)
  exact hpiece.mono_const hC

private theorem complexGroupoid_le_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAlgebra ℝ ℂ] [IsScalarTower ℝ ℂ E]
    (n : ℕ∞ω) :
    contDiffGroupoid n (𝓘(ℂ, E)) ≤ contDiffGroupoid n (𝓘(ℝ, E)) := by
  rw [StructureGroupoid.le_iff]
  intro e he
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at he ⊢
  rcases he with ⟨h₁, h₂⟩
  constructor
  · simpa using h₁.restrict_scalars ℝ
  · simpa using h₂.restrict_scalars ℝ

private theorem complex_manifold_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAlgebra ℝ ℂ] [IsScalarTower ℝ ℂ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (k : ℕ∞ω) [IsManifold 𝓘(ℂ, E) k M] : IsManifold 𝓘(ℝ, E) k M := by
  let : HasGroupoid M (contDiffGroupoid k (𝓘(ℝ, E))) := HasGroupoid.mk (by
    intro e e' he he'
    have hc : e.symm ≫ₕ e' ∈ contDiffGroupoid k (𝓘(ℂ, E)) :=
      HasGroupoid.compatible he he'
    exact (StructureGroupoid.le_iff.mp (complexGroupoid_le_real k)) _ hc)
  exact IsManifold.mk' (𝓘(ℝ, E)) k M

private theorem finiteChart_coord_smooth {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (balls : FiniteChartBallRefinement cover)
    (u : ℕ → M → ℝ)
    (hu : ∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (u j)) :
    ∀ p : balls.ι, ∀ j : ℕ,
      ContDiffOn ℝ 2
        (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base (balls.chart p))).symm)
        (Metric.ball (balls.center p) (balls.outerRadius p)) := by
  intro p j
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (balls.chart p))
  let : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M := complex_manifold_real ∞
  have hcoord : ContDiffOn ℝ ∞ (u j ∘ e.symm) e.target := by
    have h := (contMDiff_iff.mp (hu j)).2 (cover.base (balls.chart p)) 0
    simpa [e, extChartAt, chartAt_self_eq] using h
  have hball : Metric.ball (balls.center p) (balls.outerRadius p) ⊆ e.target := by
    exact (Metric.ball_subset_closedBall).trans (balls.outer_in_target p)
  have h2 : ContDiffOn ℝ 2 (u j ∘ e.symm) e.target :=
    hcoord.of_le (inferInstance : ENat.LEInfty (2 : ℕ∞ω)).out
  simpa [e] using h2.mono hball

/-- Transport a common finite-chart gauge bound to every extraction ball. The three orders
have uniform supremum bounds and order two has a uniform Hölder bound. Smoothness is required
on the larger open ball. The fixed chart transition constants may depend on the refinement
and exponent, but never on the sequence index. -/
private theorem smoothJetData
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} {f : E → F} {α : ℝ≥0} {k : ℕ}
    (hα : α ≤ 1) (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ (k + 1) f U) :
    ∃ C B : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ k f) K ∧
      ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ B := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ (k + 1) f) K := by
    intro x hx
    have hAt : ContDiffAt ℝ (k + 1) f x := hf.contDiffAt (hU.mem_nhds (hKU hx))
    exact hAt.continuousAt_iteratedFDeriv (by exact_mod_cast (Nat.le_refl (k + 1)))
      |>.continuousWithinAt
  have hnorm : ContinuousOn (fun x => ‖iteratedFDeriv ℝ (k + 1) f x‖) K := hcont.norm
  obtain ⟨B₀, hB₀, hB⟩ := hK.bddAbove_image hnorm |>.exists_ge 0
  let B : ℝ≥0 := ⟨B₀, hB₀⟩
  have hbound (x : E) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ (B : ℝ) := by
    exact_mod_cast hB (‖iteratedFDeriv ℝ (k + 1) f x‖) ⟨x, hx, rfl⟩
  have hklt : (↑k : ℕ∞ω) < (↑(k + 1) : ℕ∞ω) := by
    exact_mod_cast (show k < k + 1 by omega)
  have hdiff (x : E) (hx : x ∈ K) : DifferentiableAt ℝ
      (fun y => iteratedFDeriv ℝ k f y) x :=
    (hf.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt_iteratedFDeriv hklt
  have hLip : LipschitzOnWith B (fun x => iteratedFDeriv ℝ k f x) K := by
    apply hKconv.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact hdiff
    · intro x hx
      have hb : ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k f y) x‖ ≤ (B : ℝ) := by
        rw [norm_fderiv_iteratedFDeriv]
        exact hbound x hx
      exact_mod_cast hb
  have hHolder :=
    CalabiYau.Schauder.holderOnWith_of_lipschitzOnWith_of_compact hK hLip hα
  have hcontk : ContinuousOn (iteratedFDeriv ℝ k f) K := by
    intro x hx
    have hAt : ContDiffAt ℝ (k + 1) f x := hf.contDiffAt (hU.mem_nhds (hKU hx))
    exact hAt.continuousAt_iteratedFDeriv (by exact_mod_cast (show k ≤ k + 1 by omega))
      |>.continuousWithinAt
  have hnormk : ContinuousOn (fun x => ‖iteratedFDeriv ℝ k f x‖) K := hcontk.norm
  obtain ⟨C₀, hC₀, hC⟩ := hK.bddAbove_image hnormk |>.exists_ge 0
  let C : ℝ≥0 := ⟨C₀, hC₀⟩
  have hjetbound (x : E) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ k f x‖ ≤ (C : ℝ) := by
    exact_mod_cast hC (‖iteratedFDeriv ℝ k f x‖) ⟨x, hx, rfl⟩
  exact ⟨(B * (Metric.ediam K).toNNReal ^ ((1 : ℝ) - (α : ℝ))), C,
    hHolder, hjetbound⟩

private theorem holderOnWith_zeroJet_of_holderOnWith
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {f : E → F} {C α : ℝ≥0}
    (hf : HolderOnWith C α f K) :
    HolderOnWith C α (iteratedFDeriv ℝ 0 f) K := by
  let c := continuousMultilinearCurryFin0 ℝ E F
  rw [iteratedFDeriv_zero_eq_comp]
  intro x hx y hy
  change edist (c.symm (f x)) (c.symm (f y)) ≤
    (C : ℝ≥0∞) * edist x y ^ (α : ℝ)
  rw [c.symm.edist_map]
  exact hf x hx y hy

private theorem taylorCompHolderTwo_family
    {J E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E} {α : ℝ≥0}
    {p : J → E → FormalMultilinearSeries ℝ F G}
    {q : J → E → FormalMultilinearSeries ℝ E F}
    (hp : ∀ k ≤ 2, ∃ C : ℝ≥0, ∀ j, HolderOnWith C α (fun x => p j x k) K)
    (hq : ∀ k ≤ 2, ∃ C : ℝ≥0, ∀ j, HolderOnWith C α (fun x => q j x k) K)
    (hpb : ∀ k ≤ 2, ∃ B : ℝ≥0, ∀ j, ∀ x ∈ K, ‖p j x k‖ ≤ B)
    (hqb : ∀ k ≤ 2, ∃ B : ℝ≥0, ∀ j, ∀ x ∈ K, ‖q j x k‖ ≤ B) :
    ∃ C : ℝ≥0, ∀ j, HolderOnWith C α
      (fun x => (p j x).taylorComp (q j x) 2) K := by
  classical
  let l : Filter (J × E × E) := Filter.principal (Set.univ ×ˢ (K ×ˢ K))
  let d : J × E × E → ℝ := fun a => Real.rpow (dist a.2.1 a.2.2) (α : ℝ)
  let p₁ : J × E × E → FormalMultilinearSeries ℝ F G := fun a => p a.1 a.2.1
  let p₂ : J × E × E → FormalMultilinearSeries ℝ F G := fun a => p a.1 a.2.2
  let q₁ : J × E × E → FormalMultilinearSeries ℝ E F := fun a => q a.1 a.2.1
  let q₂ : J × E × E → FormalMultilinearSeries ℝ E F := fun a => q a.1 a.2.2
  have hp₁bdd : ∀ k ≤ 2, l.IsBoundedUnder (· ≤ ·) (fun a => ‖p₁ a k‖) := by
    intro k hk
    obtain ⟨B, hB⟩ := hpb k hk
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hB a.1 a.2.1 ha.2.1
  have hp₂bdd : ∀ k ≤ 2, l.IsBoundedUnder (· ≤ ·) (fun a => ‖p₂ a k‖) := by
    intro k hk
    obtain ⟨B, hB⟩ := hpb k hk
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hB a.1 a.2.2 ha.2.2
  have hq₁bdd : ∀ k ≤ 2, l.IsBoundedUnder (· ≤ ·) (fun a => ‖q₁ a k‖) := by
    intro k hk
    obtain ⟨B, hB⟩ := hqb k hk
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hB a.1 a.2.1 ha.2.1
  have hq₂bdd : ∀ k ≤ 2, l.IsBoundedUnder (· ≤ ·) (fun a => ‖q₂ a k‖) := by
    intro k hk
    obtain ⟨B, hB⟩ := hqb k hk
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hB a.1 a.2.2 ha.2.2
  have hpf : ∀ k ≤ 2, (fun a => p₁ a k - p₂ a k) =O[l] d := by
    intro k hk
    obtain ⟨C, hC⟩ := hp k hk
    rw [Asymptotics.isBigO_iff]
    refine ⟨(C : ℝ), ?_⟩
    rw [Filter.eventually_principal]
    intro a ha
    have hab := (hC a.1).dist_le ha.2.1 ha.2.2
    rw [dist_eq_norm] at hab
    change ‖p₁ a k - p₂ a k‖ ≤ (C : ℝ) * ‖d a‖
    simpa [p₁, p₂, d, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (dist_nonneg) _)] using hab
  have hqf : ∀ k ≤ 2, (fun a => q₁ a k - q₂ a k) =O[l] d := by
    intro k hk
    obtain ⟨C, hC⟩ := hq k hk
    rw [Asymptotics.isBigO_iff]
    refine ⟨(C : ℝ), ?_⟩
    rw [Filter.eventually_principal]
    intro a ha
    have hab := (hC a.1).dist_le ha.2.1 ha.2.2
    rw [dist_eq_norm] at hab
    change ‖q₁ a k - q₂ a k‖ ≤ (C : ℝ) * ‖d a‖
    simpa [q₁, q₂, d, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (dist_nonneg) _)] using hab
  have hcomp := FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
    hp₁bdd hpf hq₁bdd hq₂bdd hqf
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hcomp
  let C' : ℝ≥0 := ⟨max 0 C, le_max_left 0 C⟩
  refine ⟨C', ?_⟩
  intro j x hx y hy
  have h := (Filter.eventually_principal.mp hC) (j, x, y) ⟨Set.mem_univ j, hx, hy⟩
  have h' : ‖(p j x).taylorComp (q j x) 2 - (p j y).taylorComp (q j y) 2‖ ≤
      C * Real.rpow (dist x y) (α : ℝ) := by
    simpa [p₁, p₂, q₁, q₂, d, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (dist_nonneg) _)] using h
  have hC' : C ≤ (C' : ℝ) := le_max_right 0 C
  have h'' := h'.trans (mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg (dist_nonneg) _))
  have hENN : ENNReal.ofReal
      (dist ((p j x).taylorComp (q j x) 2) ((p j y).taylorComp (q j y) 2)) ≤
      ENNReal.ofReal (C' * Real.rpow (dist x y) (α : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    simpa only [dist_eq_norm] using h''
  change edist ((p j x).taylorComp (q j x) 2) ((p j y).taylorComp (q j y) 2) ≤
    (C' : ENNReal) * edist x y ^ (α : ℝ)
  simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg,
    Real.rpow_nonneg] using hENN

private theorem taylorComp_bounded_family
    {J E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E} {p : J → E → FormalMultilinearSeries ℝ F G}
    {q : J → E → FormalMultilinearSeries ℝ E F} {k : ℕ}
    (hp : ∃ B : ℝ≥0, ∀ j, ∀ r ≤ k, ∀ x ∈ K, ‖p j x r‖ ≤ B)
    (hq : ∃ B : ℝ≥0, ∀ j, ∀ r ≤ k, ∀ x ∈ K, ‖q j x r‖ ≤ B) :
    ∃ B : ℝ≥0, ∀ j, ∀ x ∈ K, ‖(p j x).taylorComp (q j x) k‖ ≤ B := by
  classical
  let l : Filter (J × E × E) := Filter.principal (Set.univ ×ˢ (K ×ˢ K))
  let P : J × E × E → FormalMultilinearSeries ℝ F G := fun a => p a.1 a.2.1
  let Q : J × E × E → FormalMultilinearSeries ℝ E F := fun a => q a.1 a.2.1
  obtain ⟨BP, hBP⟩ := hp
  obtain ⟨BQ, hBQ⟩ := hq
  have hPbdd : ∀ r ≤ k, l.IsBoundedUnder (· ≤ ·) (fun a => ‖P a r‖) := by
    intro r hr
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hBP a.1 r hr a.2.1 ha.2.1
  have hQbdd : ∀ r ≤ k, l.IsBoundedUnder (· ≤ ·) (fun a => ‖Q a r‖) := by
    intro r hr
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hBQ a.1 r hr a.2.1 ha.2.1
  let pzero : J × E × E → FormalMultilinearSeries ℝ F G := fun _ => 0
  let qzero : J × E × E → FormalMultilinearSeries ℝ E F := fun _ => 0
  have hPdiff : ∀ r ≤ k, (fun a => P a r - pzero a r) =O[l] (fun _ => (1 : ℝ)) := by
    intro r hr
    rw [Asymptotics.isBigO_iff]
    refine ⟨(BP : ℝ), ?_⟩
    rw [Filter.eventually_principal]
    intro a ha
    calc
      ‖P a r - pzero a r‖ = ‖p a.1 a.2.1 r‖ := by simp [P, pzero]
      _ ≤ BP := hBP a.1 r hr a.2.1 ha.2.1
      _ = BP * ‖(1 : ℝ)‖ := by simp
  have hQdiff : ∀ r ≤ k, (fun a => Q a r - qzero a r) =O[l] (fun _ => (1 : ℝ)) := by
    intro r hr
    rw [Asymptotics.isBigO_iff]
    refine ⟨(BQ : ℝ), ?_⟩
    rw [Filter.eventually_principal]
    intro a ha
    calc
      ‖Q a r - qzero a r‖ = ‖q a.1 a.2.1 r‖ := by simp [Q, qzero]
      _ ≤ BQ := hBQ a.1 r hr a.2.1 ha.2.1
      _ = BQ * ‖(1 : ℝ)‖ := by simp
  have hQzeroBdd : ∀ r ≤ k, l.IsBoundedUnder (· ≤ ·) (fun a => ‖qzero a r‖) := by
    intro r hr
    simpa [qzero] using
      (Filter.isBoundedUnder_const (r := (· ≤ ·)) (l := l) (a := (0 : ℝ)))
  have hcomp := FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
    (p₁ := P) (p₂ := pzero) (q₁ := Q) (q₂ := qzero)
    (f := fun _ : J × E × E => (1 : ℝ)) hPbdd hPdiff hQbdd hQzeroBdd hQdiff
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hcomp
  let C' : ℝ≥0 := ⟨max 0 C, le_max_left 0 C⟩
  refine ⟨C', ?_⟩
  intro j x hx
  have h := (Filter.eventually_principal.mp hC) (j, x, x) ⟨Set.mem_univ j, hx, hx⟩
  have hz : (pzero (j, x, x)).taylorComp (qzero (j, x, x)) k = 0 := by
    change (∑ c : OrderedFinpartition k,
      c.compAlongOrderedFinpartition 0 (fun _ => 0)) = 0
    apply Finset.sum_eq_zero
    intro c hc
    ext v
    simp [OrderedFinpartition.compAlongOrderFinpartition_apply]
  have hnorm : ‖(p j x).taylorComp (q j x) k‖ ≤ C := by
    simpa [P, Q, pzero, qzero, hz] using h
  exact hnorm.trans (by exact_mod_cast (le_max_right 0 C))

private theorem holderBoundOn_comp_smooth_map_two_family
    {J E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {α C : ℝ≥0} {K U V W : Set E} {τ : E → E}
    {g : J → E → ℝ}
    (hα : α ≤ 1) (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hτ : ContDiffOn ℝ 3 τ U)
    (hV : IsCompact V) (hVconv : Convex ℝ V) (hW : IsOpen W) (hVW : V ⊆ W)
    (hτV : Set.MapsTo τ K V) (hg : ∀ j, ContDiffOn ℝ 2 (g j) W)
    (hbound : ∀ j, HolderBoundOn 2 α C V (g j)) :
    ∃ C' : ℝ≥0, ∀ j, HolderBoundOn 2 α C' K (g j ∘ τ) := by
  classical
  have hτData (k : ℕ) (hk : k ≤ 2) :
      ∃ Ck Bk : ℝ≥0, HolderOnWith Ck α (fun y => iteratedFDeriv ℝ k τ y) K ∧
        ∀ y ∈ K, ‖iteratedFDeriv ℝ k τ y‖ ≤ Bk := by
    exact smoothJetData hα hK hKconv hU hKU
      (hτ.of_le (by exact_mod_cast (show k + 1 ≤ 3 by omega)))
  obtain ⟨_, Bτ1, _, hτ1bound⟩ := hτData 1 (by omega)
  have hτLipschitz : LipschitzOnWith Bτ1 τ K := by
    apply hKconv.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro x hx
      exact (hτ.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by norm_num)
    · intro x hx
      have hb : ‖fderiv ℝ τ x‖ ≤ (Bτ1 : ℝ) := by
        rw [← norm_iteratedFDeriv_one]
        exact hτ1bound x hx
      exact_mod_cast hb
  have hτHolder1 : HolderOnWith Bτ1 1 τ K := hτLipschitz.holderOnWith
  have hLipLower (j : J) :=
    CalabiYau.Schauder.lipschitzOnWith_function_and_firstDerivative_of_holderBoundOn
      hVconv hW hVW (hg j) (hbound j)
  let Bα := C * (Metric.ediam V).toNNReal ^ ((1 : ℝ) - (α : ℝ))
  have hG0 (j : J) : HolderOnWith Bα α (g j) V := by
    simpa [Bα] using
      CalabiYau.Schauder.holderOnWith_of_lipschitzOnWith_of_compact hV (hLipLower j).1 hα
  have hG0jet (j : J) : HolderOnWith Bα α (iteratedFDeriv ℝ 0 (g j)) V :=
    holderOnWith_zeroJet_of_holderOnWith (hG0 j)
  have hG1 (j : J) : HolderOnWith Bα α (fun y => iteratedFDeriv ℝ 1 (g j) y) V := by
    simpa [Bα] using
      CalabiYau.Schauder.holderOnWith_of_lipschitzOnWith_of_compact hV (hLipLower j).2 hα
  have hp : ∀ k ≤ 2, ∃ Ck : ℝ≥0, ∀ j,
      HolderOnWith Ck α (fun y => (ftaylorSeries ℝ (g j) (τ y)) k) K := by
    intro k hk
    by_cases hk2 : k = 2
    · subst k
      refine ⟨C * Bτ1 ^ (α : ℝ), ?_⟩
      intro j
      have h := (hbound j).2.comp hτHolder1 hτV
      simpa [ftaylorSeries, Function.comp_def, mul_one] using h
    · have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · refine ⟨Bα * Bτ1 ^ (α : ℝ), ?_⟩
        intro j
        have h := (hG0jet j).comp hτHolder1 hτV
        simpa [ftaylorSeries, Function.comp_def, mul_one] using h
      · refine ⟨Bα * Bτ1 ^ (α : ℝ), ?_⟩
        intro j
        have h := (hG1 j).comp hτHolder1 hτV
        simpa [ftaylorSeries, Function.comp_def, mul_one] using h
  have hq : ∀ k ≤ 2, ∃ Ck : ℝ≥0, ∀ j : J,
      HolderOnWith Ck α (fun y => (ftaylorSeries ℝ τ y) k) K := by
    intro k hk
    obtain ⟨Ck, _, hQ, _⟩ := hτData k hk
    exact ⟨Ck, fun _ => by simpa [ftaylorSeries] using hQ⟩
  have hpb : ∀ k ≤ 2, ∃ Bk : ℝ≥0, ∀ j, ∀ y ∈ K,
      ‖ftaylorSeries ℝ (g j) (τ y) k‖ ≤ Bk := by
    intro k hk
    refine ⟨C, ?_⟩
    intro j y hy
    simpa [ftaylorSeries] using (hbound j).1 k hk (τ y) (hτV hy)
  have hqb : ∀ k ≤ 2, ∃ Bk : ℝ≥0, ∀ j : J, ∀ y ∈ K,
      ‖ftaylorSeries ℝ τ y k‖ ≤ Bk := by
    intro k hk
    obtain ⟨_, Bk, _, hQ⟩ := hτData k hk
    exact ⟨Bk, fun _ y hy => by simpa [ftaylorSeries] using hQ y hy⟩
  obtain ⟨Bτ0', hBτ0'⟩ := hqb 0 (by omega)
  obtain ⟨Bτ1'', hBτ1''⟩ := hqb 1 (by omega)
  obtain ⟨Bτ2', hBτ2'⟩ := hqb 2 (by omega)
  let Bq := max Bτ0' (max Bτ1'' Bτ2')
  have hQall : ∀ k ≤ 2, ∀ j : J, ∀ y ∈ K, ‖ftaylorSeries ℝ τ y k‖ ≤ Bq := by
    intro k hk j y hy
    interval_cases k
    · exact (hBτ0' j y hy).trans (by exact_mod_cast (le_max_left Bτ0' (max Bτ1'' Bτ2')))
    · exact (hBτ1'' j y hy).trans (by exact_mod_cast
        (le_trans (le_max_left Bτ1'' Bτ2') (le_max_right Bτ0' (max Bτ1'' Bτ2'))))
    · exact (hBτ2' j y hy).trans (by exact_mod_cast
        (le_trans (le_max_right Bτ1'' Bτ2') (le_max_right Bτ0' (max Bτ1'' Bτ2'))))
  have hTaylorBound (k : ℕ) (hk : k ≤ 2) :
      ∃ Bk : ℝ≥0, ∀ j, ∀ y ∈ K,
        ‖(ftaylorSeries ℝ (g j) (τ y)).taylorComp (ftaylorSeries ℝ τ y) k‖ ≤ Bk := by
    apply taylorComp_bounded_family
    · exact ⟨C, fun j r hr y hy => by
        simpa [ftaylorSeries] using (hbound j).1 r (le_trans hr hk) (τ y) (hτV hy)⟩
    · exact ⟨Bq, fun j r hr y hy => hQall r (le_trans hr hk) j y hy⟩
  obtain ⟨Bjet0, hBjet0⟩ := hTaylorBound 0 (by omega)
  obtain ⟨Bjet1, hBjet1⟩ := hTaylorBound 1 (by omega)
  obtain ⟨Bjet2, hBjet2⟩ := hTaylorBound 2 (by omega)
  let Bjet := max Bjet0 (max Bjet1 Bjet2)
  have hTaylorBoundAll : ∀ k ≤ 2, ∀ j, ∀ y ∈ K,
      ‖(ftaylorSeries ℝ (g j) (τ y)).taylorComp (ftaylorSeries ℝ τ y) k‖ ≤ Bjet := by
    intro k hk j y hy
    interval_cases k
    · exact (hBjet0 j y hy).trans (by exact_mod_cast (le_max_left Bjet0 (max Bjet1 Bjet2)))
    · exact (hBjet1 j y hy).trans (by exact_mod_cast
        (le_trans (le_max_left Bjet1 Bjet2) (le_max_right Bjet0 (max Bjet1 Bjet2))))
    · exact (hBjet2 j y hy).trans (by exact_mod_cast
        (le_trans (le_max_right Bjet1 Bjet2) (le_max_right Bjet0 (max Bjet1 Bjet2))))
  obtain ⟨Ccomp, hCompTaylor⟩ := taylorCompHolderTwo_family hp hq hpb hqb
  have hCompEq (j : J) (k : ℕ) (hk : k ≤ 2) (y : E) (hy : y ∈ K) :
      iteratedFDeriv ℝ k ((g j) ∘ τ) y =
        (ftaylorSeries ℝ (g j) (τ y)).taylorComp (ftaylorSeries ℝ τ y) k := by
    have hgAt : ContDiffAt ℝ k (g j) (τ y) :=
      ((hg j).contDiffAt (hW.mem_nhds (hVW (hτV hy)))).of_le (by exact_mod_cast hk)
    have hτAt : ContDiffAt ℝ k τ y :=
      (hτ.contDiffAt (hU.mem_nhds (hKU hy))).of_le
        (by exact_mod_cast (show k ≤ 3 by omega))
    exact iteratedFDeriv_comp hgAt hτAt le_rfl
  have hJetBound (j : J) : ∀ k ≤ 2, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k ((g j) ∘ τ) y‖ ≤ Bjet := by
    intro k hk y hy
    rw [hCompEq j k hk y hy]
    exact hTaylorBoundAll k hk j y hy
  have hTaylorJet (j : J) : HolderOnWith Ccomp α
      (iteratedFDeriv ℝ 2 ((g j) ∘ τ)) K := by
    intro y hy z hz
    rw [hCompEq j 2 (by omega) y hy, hCompEq j 2 (by omega) z hz]
    exact hCompTaylor j y hy z hz
  let C' := max Ccomp Bjet
  refine ⟨C', ?_⟩
  intro j
  constructor
  · intro k hk y hy
    exact (hJetBound j k hk y hy).trans (by exact_mod_cast (le_max_right Ccomp Bjet))
  · exact (hTaylorJet j).mono_const (le_max_left _ _)

private theorem chartTransition_contDiffOn
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (∞ : ℕ∞ω) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    {i j : cover.ι} {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target)
    (hsource : ∀ z ∈ U, (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).source) :
    ContDiffOn ℝ 3
      (fun z => (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j))
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) U := by
  let E := EuclideanSpace ℂ (Fin n)
  let I := 𝓘(ℝ, E)
  let ci := chartAt E (cover.base i)
  let cj := chartAt E (cover.base j)
  have hi : ci ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M :=
    IsManifold.chart_mem_maximalAtlas (I := I) (n := (∞ : ℕ∞ω)) (x := cover.base i)
  have hj : cj ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M :=
    IsManifold.chart_mem_maximalAtlas (I := I) (n := (∞ : ℕ∞ω)) (x := cover.base j)
  have hgroup : ci.symm.trans cj ∈ contDiffGroupoid (∞ : ℕ∞ω) I :=
    IsManifold.compatible_of_mem_maximalAtlas hi hj
  have hraw : ContDiffOn ℝ ∞ (I ∘ (ci.symm.trans cj) ∘ I.symm)
      (I.symm ⁻¹' (ci.symm.trans cj).source ∩ Set.range I) := hgroup.1
  have hcoord : ContDiffOn ℝ ∞ (fun z => cj (ci.symm z))
      (ci.target ∩ ci.symm ⁻¹' cj.source) := by
    simpa [I, ci, cj, Function.comp_def, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, ModelWithCorners.range_eq_univ,
      OpenPartialHomeomorph.trans_source, extChartAt, chartAt_self_eq] using hraw
  have hUci : U ⊆ ci.target := by
    simpa [ci, extChartAt, chartAt_self_eq] using hU
  have hsourceci : ∀ z ∈ U, ci.symm z ∈ cj.source := by
    intro z hz
    simpa [ci, cj, extChartAt, chartAt_self_eq] using hsource z hz
  have hU' : U ⊆ ci.target ∩ ci.symm ⁻¹' cj.source := by
    intro z hz
    exact ⟨hUci hz, hsourceci z hz⟩
  have hle : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
    (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out
  have h3 : ContDiffOn ℝ 3 (fun z => cj (ci.symm z))
      (ci.target ∩ ci.symm ⁻¹' cj.source) := hcoord.of_le hle
  have hresult := h3.mono hU'
  simpa [ci, cj, extChartAt, chartAt_self_eq] using hresult

private theorem finiteChart_family_patchBound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (∞ : ℕ∞ω) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (balls : FiniteChartBallRefinement cover) (α B : ℝ≥0)
    (hα : α ≤ 1) (p : balls.ι) (u : ℕ → M → ℝ)
    (hu : ∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (u j))
    (hpiece : ∀ j, HolderBoundOn 2 α B (cover.piece (balls.donor p))
      (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        (cover.base (balls.donor p))).symm)) :
    ∃ C : ℝ≥0, ∀ j : ℕ,
      ContDiffOn ℝ 2
        (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base (balls.chart p))).symm)
        (Metric.ball (balls.center p) (balls.outerRadius p)) ∧
      HolderBoundOn 2 α C
        (Metric.closedBall (balls.center p) (balls.middleRadius p))
        (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base (balls.chart p))).symm) := by
  let E := EuclideanSpace ℂ (Fin n)
  let ci := extChartAt 𝓘(ℝ, E) (cover.base (balls.chart p))
  let cd := extChartAt 𝓘(ℝ, E) (cover.base (balls.donor p))
  let K := Metric.closedBall (balls.center p) (balls.middleRadius p)
  let U := Metric.ball (balls.center p) (balls.outerRadius p)
  let V := Metric.closedBall (balls.donorCenter p) (balls.donorRadius p)
  let τ : E → E := cd ∘ ci.symm
  have hUtarget : U ⊆ ci.target := by
    intro z hz
    exact balls.outer_in_target p (Metric.ball_subset_closedBall hz)
  have hsource (z : E) (hz : z ∈ U) : ci.symm z ∈ cd.source := by
    have hzouter := Metric.ball_subset_closedBall hz
    have hτV : τ z ∈ V := balls.overlap_mapsTo p hzouter
    have hτtarget : τ z ∈ cd.target := by
      exact cover.piece_in_target (balls.donor p)
        (interior_subset (balls.donor_in_interior p hτV))
    have hinv := balls.overlap_inverse p z hzouter
    rw [← hinv]
    exact cd.symm.map_source hτtarget
  have hτsmooth : ContDiffOn ℝ 3 τ U := by
    change ContDiffOn ℝ 3 (fun z => cd (ci.symm z)) U
    exact chartTransition_contDiffOn cover hUtarget hsource
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hKconv : Convex ℝ K := convex_closedBall _ _
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hKU : K ⊆ U := Metric.closedBall_subset_ball (balls.middle_lt_outer p)
  have hVcompact : IsCompact V := isCompact_closedBall _ _
  have hVconv : Convex ℝ V := convex_closedBall _ _
  have hVpiece : V ⊆ cover.piece (balls.donor p) := by
    intro z hz
    exact interior_subset (balls.donor_in_interior p hz)
  have hVtarget : V ⊆ cd.target := by
    intro z hz
    exact cover.piece_in_target (balls.donor p) (hVpiece hz)
  have hτV : Set.MapsTo τ K V := by
    intro z hz
    change τ z ∈ V
    exact balls.overlap_mapsTo p
      (Metric.closedBall_subset_closedBall (le_of_lt (balls.middle_lt_outer p)) hz)
  have hW : IsOpen cd.target := isOpen_extChartAt_target (cover.base (balls.donor p))
  have hcoord (j : ℕ) : ContDiffOn ℝ 2 (u j ∘ cd.symm) cd.target := by
    have h := (contMDiff_iff.mp (hu j)).2 (cover.base (balls.donor p)) 0
    have h' : ContDiffOn ℝ ∞ (u j ∘ cd.symm) cd.target := by
      simpa [cd, extChartAt, chartAt_self_eq] using h
    exact h'.of_le (inferInstance : ENat.LEInfty (2 : ℕ∞ω)).out
  let hboundV (j : ℕ) : HolderBoundOn 2 α B V (u j ∘ cd.symm) :=
    (hpiece j).mono_set hVpiece
  have hholder := holderBoundOn_comp_smooth_map_two_family hα hKcompact hKconv
    hUopen hKU hτsmooth hVcompact hVconv hW hVtarget hτV hcoord hboundV
  obtain ⟨C, hholder⟩ := hholder
  have hτU : Set.MapsTo τ U cd.target := by
    intro z hz
    exact hVtarget (balls.overlap_mapsTo p (Metric.ball_subset_closedBall hz))
  have hcoordComp (j : ℕ) : ContDiffOn ℝ 2 ((u j ∘ cd.symm) ∘ τ) U :=
    (hcoord j).comp ((hτsmooth.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by omega)))
      ) hτU
  have hlocEq (j : ℕ) (z : E) (hz : z ∈ K) :
      ((u j ∘ cd.symm) ∘ τ) =ᶠ[𝓝 z] (u j ∘ ci.symm) := by
    filter_upwards [hUopen.mem_nhds (hKU hz)] with w hw
    have hwinv := balls.overlap_inverse p w (Metric.ball_subset_closedBall hw)
    change u j (cd.symm (τ w)) = u j (ci.symm w)
    exact congrArg (u j) hwinv
  have hjetEq (j k : ℕ) (z : E) (hz : z ∈ K) :
      iteratedFDeriv ℝ k ((u j ∘ cd.symm) ∘ τ) z =
        iteratedFDeriv ℝ k (u j ∘ ci.symm) z :=
    ((hlocEq j z hz).iteratedFDeriv ℝ k).self_of_nhds
  refine ⟨C, ?_⟩
  intro j
  constructor
  · have hsmoothComp : ContDiffOn ℝ 2 (u j ∘ ci.symm) U :=
      (hcoordComp j).congr (fun z hz => by
        have hwinv := balls.overlap_inverse p z (Metric.ball_subset_closedBall hz)
        change u j (ci.symm z) = u j (cd.symm (τ z))
        exact congrArg (u j) hwinv.symm)
    simpa [ci, extChartAt, chartAt_self_eq] using hsmoothComp
  · have h := hholder j
    refine ⟨?_, ?_⟩
    · intro k hk z hz
      rw [← hjetEq j k z hz]
      exact h.1 k hk z hz
    · intro z hz w hw
      rw [← hjetEq j 2 z hz, ← hjetEq j 2 w hw]
      exact h.2 z hz w hw

theorem exists_uniform_holderBoundOn_refinement {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (balls : FiniteChartBallRefinement cover)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (u : ℕ → M → ℝ)
    (hu : ∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (u j))
    (B : ℝ≥0)
    (hfinite : ∀ j, finiteChartHolderGauge cover 2 α (u j) < ⊤)
    (hbound : ∀ j, (finiteChartHolderGauge cover 2 α (u j)).toReal ≤ (B : ℝ)) :
    ∃ C : ℝ≥0, ∀ p : balls.ι, ∀ j : ℕ,
      ContDiffOn ℝ 2
        (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base (balls.chart p))).symm)
        (Metric.ball (balls.center p) (balls.outerRadius p)) ∧
      HolderBoundOn 2 α C
        (Metric.closedBall (balls.center p) (balls.middleRadius p))
        (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base (balls.chart p))).symm) := by
  have hchart : ∀ j : ℕ, ∀ i : cover.ι,
      HolderBoundOn 2 α B (cover.piece i)
        (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) := by
    intro j i
    exact holderBoundOn_chart_of_gauge_bound cover α (u j) B (hfinite j) (hbound j) i
  have _ := hα₀
  have hsmooth := finiteChart_coord_smooth cover balls u hu
  obtain ⟨C, hholder⟩ : ∃ C : ℝ≥0, ∀ p : balls.ι, ∀ j : ℕ,
      HolderBoundOn 2 α C
        (Metric.closedBall (balls.center p) (balls.middleRadius p))
        (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base (balls.chart p))).symm) := by
      classical
    let : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (∞ : ℕ∞ω) M :=
      complex_manifold_real ∞
    let patchWitness (p : balls.ι) :=
      finiteChart_family_patchBound cover balls α B (le_of_lt hα₁) p u hu
        (fun j => hchart j (balls.donor p))
    let patchConst (p : balls.ι) := Classical.choose (patchWitness p)
    have hpatch (p : balls.ι) (j : ℕ) :
        HolderBoundOn 2 α (patchConst p)
          (Metric.closedBall (balls.center p) (balls.middleRadius p))
          (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (cover.base (balls.chart p))).symm) :=
      (Classical.choose_spec (patchWitness p) j).2
    let C' : ℝ≥0 := Finset.univ.sum patchConst
    have hC (p : balls.ι) : patchConst p ≤ C' := by
      dsimp [C']
      exact Finset.single_le_sum
        (fun q hq => by positivity) (Finset.mem_univ p)
    refine ⟨C', ?_⟩
    intro p j
    exact (hpatch p j).mono_const (hC p)
  exact ⟨C, fun p j => ⟨hsmooth p j, hholder p j⟩⟩

end KahlerForm
