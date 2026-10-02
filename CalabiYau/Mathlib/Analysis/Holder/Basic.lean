-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Holder/Basic.lean
-- Locally modified.
module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.MetricSpace.Snowflaking
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

@[expose] public section

-- and its private helpers occur in public declarations.

noncomputable section

open Set
open scoped ENNReal NNReal BigOperators Topology

namespace CalabiYau.Schauder

section

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
theorem contDiff_two_of_hasFDerivAt
    {V G : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (u : BoundedContinuousFunction V G)
    (du : BoundedContinuousFunction V (V →L[Real] G))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] G))
    (hu : ∀ x, HasFDerivAt (u : V → G) (du x) x)
    (hdu : ∀ x, HasFDerivAt (du : V → V →L[Real] G) (d2u x) x) :
    ContDiff Real 2 (u : V → G) := by
  have hduC1 : ContDiff Real 1 (du : V → V →L[Real] G) :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨d2u, d2u.continuous, hdu⟩
  exact (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr ⟨du, hduC1, hu⟩

theorem holderWith_zero_of_norm_le
    {Y G : Type*} [PseudoMetricSpace Y] [NormedAddCommGroup G]
    {B : NNReal} {f : Y → G} (h : ∀ x, ‖f x‖ ≤ B) :
    HolderWith (2 * B) 0 f := by
  intro x y
  rw [edist_dist, edist_dist]
  have hdist : dist (f x) (f y) ≤ 2 * (B : Real) := by
    rw [dist_eq_norm]
    exact (norm_sub_le (f x) (f y)).trans
      ((add_le_add (h x) (h y)).trans_eq (by ring))
  calc
    ENNReal.ofReal (dist (f x) (f y)) ≤ ENNReal.ofReal (2 * (B : Real)) :=
      ENNReal.ofReal_le_ofReal hdist
    _ = ((2 * B : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y) ^ (0 : Real) := by
      rw [ENNReal.rpow_zero, mul_one, ENNReal.coe_mul, ENNReal.coe_ofNat,
        ENNReal.ofReal_mul (by positivity : (0 : Real) ≤ 2),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]

theorem holderWith_restrict_of_norm_le_of_lipschitzOnWith
    {Y G : Type*} [MetricSpace Y] [NormedAddCommGroup G]
    {s : Set Y} {f : Y → G} {M L alpha epsilon : NNReal}
    (hepsilon : 0 < epsilon) (halpha : alpha ≤ 1)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ M)
    (hlip : LipschitzOnWith L f s) :
    HolderWith
      (L * epsilon ^ ((1 : NNReal) - alpha : Real) +
        2 * M / epsilon ^ (alpha : Real)) alpha
      (s.domRestrict f) := by
  rw [HolderWith.restrict_iff]
  intro x hx y hy
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ alpha.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  rw [← NNReal.coe_le_coe]
  simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_div,
    NNReal.coe_rpow, NNReal.coe_ofNat]
  by_cases hxy : x = y
  · subst y
    simp only [dist_self]
    positivity
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  by_cases hsmall : dist x y ≤ epsilon
  · have hlip' := hlip.dist_le_mul x hx y hy
    calc
      dist (f x) (f y) ≤ (L : Real) * dist x y := hlip'
      _ ≤ ((L * epsilon ^ ((1 : NNReal) - alpha : Real) : NNReal) : Real) *
          dist x y ^ (alpha : Real) := by
        rw [NNReal.coe_mul, NNReal.coe_rpow]
        have halphaReal : (alpha : Real) ≤ 1 := by exact_mod_cast halpha
        have hsum : ((1 : NNReal) - alpha : Real) + (alpha : Real) = 1 := by
          norm_num
        calc
          (L : Real) * dist x y = (L : Real) *
              (dist x y ^ ((1 : NNReal) - alpha : Real) *
                dist x y ^ (alpha : Real)) := by
            rw [← Real.rpow_add hdist, hsum, Real.rpow_one]
          _ ≤ (L : Real) *
              ((epsilon : Real) ^ ((1 : NNReal) - alpha : Real) *
                dist x y ^ (alpha : Real)) := by
            gcongr
          _ = (L : Real) * (epsilon : Real) ^
              ((1 : NNReal) - alpha : Real) *
                dist x y ^ (alpha : Real) := by ring
      _ ≤ (((L * epsilon ^ ((1 : NNReal) - alpha : Real) +
          2 * M / epsilon ^ (alpha : Real) : NNReal) : Real) *
          dist x y ^ (alpha : Real)) := by
        gcongr
        exact_mod_cast (le_add_right le_rfl :
          L * epsilon ^ ((1 : NNReal) - alpha : Real) ≤
            L * epsilon ^ ((1 : NNReal) - alpha : Real) +
              2 * M / epsilon ^ (alpha : Real))
  · have hfar : (epsilon : Real) < dist x y := lt_of_not_ge hsmall
    have hfunction : dist (f x) (f y) ≤ 2 * M := by
      rw [dist_eq_norm]
      calc
        ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hfnorm x hx) (hfnorm y hy)
        _ = 2 * M := by ring
    calc
      dist (f x) (f y) ≤ (2 * M : NNReal) := hfunction
      _ ≤ ((2 * M / epsilon ^ (alpha : Real) : NNReal) : Real) *
          dist x y ^ (alpha : Real) := by
        rw [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat,
          NNReal.coe_rpow]
        have hepspow : 0 < (epsilon : Real) ^ (alpha : Real) := by positivity
        rw [div_mul_eq_mul_div, le_div_iff₀ hepspow]
        gcongr
      _ ≤ (((L * epsilon ^ ((1 : NNReal) - alpha : Real) +
          2 * M / epsilon ^ (alpha : Real) : NNReal) : Real) *
          dist x y ^ (alpha : Real)) := by
        gcongr
        exact_mod_cast (le_add_left le_rfl :
          2 * M / epsilon ^ (alpha : Real) ≤
            L * epsilon ^ ((1 : NNReal) - alpha : Real) +
              2 * M / epsilon ^ (alpha : Real))

theorem holderWith_sub
    {Y G : Type*} [PseudoMetricSpace Y] [NormedAddCommGroup G]
    {alpha C D : NNReal} {f g : Y → G}
    (hf : HolderWith C alpha f) (hg : HolderWith D alpha g) :
    HolderWith (C + D) alpha (f - g) := by
  have hneg : HolderWith D alpha (-g) := by
    intro x y
    simpa only [Pi.neg_apply, edist_neg_neg] using hg x y
  simpa only [Pi.add_apply, Pi.sub_apply, sub_eq_add_neg] using hf.add hneg

theorem holderOnWith_of_tendsto
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {C alpha : NNReal} {f : ι → X → F} {g : X → F} {s : Set X}
    (hf : ∀ᶠ i in l, HolderOnWith C alpha (f i) s)
    (hfg : ∀ x ∈ s, Filter.Tendsto (fun i ↦ f i x) l (nhds (g x))) :
    HolderOnWith C alpha g s := by
  intro x hx y hy
  exact le_of_tendsto ((hfg x hx).edist (hfg y hy))
    (hf.mono fun i hi ↦ hi x hx y hy)

theorem TendstoLocallyUniformlyOn.holderOnWith
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {C alpha : NNReal} {f : ι → X → F} {g : X → F} {s : Set X}
    (hfg : TendstoLocallyUniformlyOn f g l s)
    (hf : ∀ᶠ i in l, HolderOnWith C alpha (f i) s) :
    HolderOnWith C alpha g s :=
  holderOnWith_of_tendsto hf fun _ hx ↦ hfg.tendsto_at hx

def eSupNormOn (s : Set X) (f : X → F) : ENNReal :=
  ⨆ x : s, ENNReal.ofReal ‖f x‖

end

section

variable {X F : Type*}  [NormedAddCommGroup F]
theorem eSupNormOn_congr {s : Set X} {f g : X → F}
    (hfg : Set.EqOn f g s) :
    eSupNormOn s f = eSupNormOn s g := by
  unfold eSupNormOn
  congr 1
  funext x
  rw [hfg x.2]

theorem eSupNormOn_add_le (s : Set X) (f g : X → F) :
    eSupNormOn s (f + g) ≤ eSupNormOn s f + eSupNormOn s g := by
  apply iSup_le
  intro x
  calc
    ENNReal.ofReal ‖f x + g x‖ ≤ ENNReal.ofReal (‖f x‖ + ‖g x‖) :=
      ENNReal.ofReal_le_ofReal (norm_add_le (f x) (g x))
    _ = ENNReal.ofReal ‖f x‖ + ENNReal.ofReal ‖g x‖ := by
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    _ ≤ eSupNormOn s f + eSupNormOn s g := by
      exact add_le_add (le_iSup (fun y : s ↦ ENNReal.ofReal ‖f y‖) x)
        (le_iSup (fun y : s ↦ ENNReal.ofReal ‖g y‖) x)

theorem eSupNormOn_sub_le (s : Set X) (f g : X → F) :
    eSupNormOn s (f - g) ≤ eSupNormOn s f + eSupNormOn s g := by
  apply iSup_le
  intro x
  calc
    ENNReal.ofReal ‖f x - g x‖ ≤ ENNReal.ofReal (‖f x‖ + ‖g x‖) :=
      ENNReal.ofReal_le_ofReal (norm_sub_le (f x) (g x))
    _ = ENNReal.ofReal ‖f x‖ + ENNReal.ofReal ‖g x‖ := by
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    _ ≤ eSupNormOn s f + eSupNormOn s g := by
      exact add_le_add (le_iSup (fun y : s ↦ ENNReal.ofReal ‖f y‖) x)
        (le_iSup (fun y : s ↦ ENNReal.ofReal ‖g y‖) x)

theorem norm_le_eSupNormOn (s : Set X) (f : X → F) (x : X) (hx : x ∈ s) :
    ENNReal.ofReal ‖f x‖ ≤ eSupNormOn s f :=
  le_iSup (fun y : s => ENNReal.ofReal ‖f y‖) ⟨x, hx⟩

theorem eSupNormOn_le {s : Set X} {f : X → F} {C : ENNReal} :
    eSupNormOn s f ≤ C ↔ ∀ x ∈ s, ENNReal.ofReal ‖f x‖ ≤ C := by
  simp only [eSupNormOn, iSup_le_iff, Subtype.forall]

end

section

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
def eHolderSeminormOn (alpha : NNReal) (s : Set X) (f : X → F) : ENNReal :=
  eHolderNorm alpha (s.domRestrict f)

theorem eHolderSeminormOn_congr {s : Set X} {f g : X → F}
    (hfg : Set.EqOn f g s) (alpha : NNReal) :
    eHolderSeminormOn alpha s f = eHolderSeminormOn alpha s g := by
  unfold eHolderSeminormOn
  congr 1
  funext x
  exact hfg x.2

theorem holderWith_restrict_of_eHolderSeminormOn_le
    {alpha C : NNReal} {s : Set X} {f : X → F}
    (h : eHolderSeminormOn alpha s f ≤ C) :
    HolderWith C alpha (s.domRestrict f) := by
  let g : s → F := s.domRestrict f
  have he : eHolderNorm alpha g ≤ (C : ENNReal) := by
    simpa only [eHolderSeminormOn, g] using h
  have hmem : MemHolder alpha g :=
    eHolderNorm_lt_top.mp (lt_of_le_of_lt he ENNReal.coe_lt_top)
  have hbase : HolderWith (nnHolderNorm alpha g) alpha g :=
    MemHolder.holderWith hmem
  have hnn : nnHolderNorm alpha g ≤ C :=
    ENNReal.coe_le_coe.mp (coe_nnHolderNorm_le_eHolderNorm.trans he)
  simpa only [g] using hbase.mono hnn

private theorem orthonormal_repr_abs_le_norm
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι Real V) (v : V) (i : ι) :
    |b.repr v i| ≤ ‖v‖ := by
  classical
  have hsq : (b.repr v i) ^ 2 ≤ ‖b.repr v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (f := fun j : ι => (b.repr v j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [show |b.repr v i| = Real.sqrt ((b.repr v i) ^ 2) from
      (Real.sqrt_sq_eq_abs _).symm,
    show ‖v‖ = Real.sqrt (‖b.repr v‖ ^ 2) from by
      rw [Real.sqrt_sq (norm_nonneg _), b.repr.norm_map]]
  exact Real.sqrt_le_sqrt hsq

theorem continuousMultilinearMap_norm_le_sum_stdOrthonormalBasis
    {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] [NormedAddCommGroup G] [NormedSpace Real G]
    {j : Nat} (A : ContinuousMultilinearMap Real (fun _ : Fin j => V) G) :
    ‖A‖ ≤ ∑ β : Fin j → Fin (Module.finrank Real V),
      ‖A (fun i => (stdOrthonormalBasis Real V) (β i))‖ := by
  classical
  let b := stdOrthonormalBasis Real V
  let C : Real := ∑ β : Fin j → Fin (Module.finrank Real V),
    ‖A (fun i => b (β i))‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ContinuousMultilinearMap.opNorm_le_bound hC ?_
  intro m
  have hexpand : ∀ i : Fin j, m i =
      ∑ a : Fin (Module.finrank Real V), b.repr (m i) a • b a := by
    intro i
    exact (b.sum_repr (m i)).symm
  have hA : A m = ∑ β : Fin j → Fin (Module.finrank Real V),
      (∏ i : Fin j, b.repr (m i) (β i)) • A (fun i => b (β i)) := by
    have hstep : A m = A (fun i : Fin j =>
        ∑ a : Fin (Module.finrank Real V), b.repr (m i) a • b a) := by
      congr
      funext i
      exact hexpand i
    rw [hstep]
    change A.toMultilinearMap _ = _
    rw [A.toMultilinearMap.map_sum
      (fun (i : Fin j) (a : Fin (Module.finrank Real V)) =>
        b.repr (m i) a • b a)]
    apply Finset.sum_congr rfl
    intro β _
    rw [A.toMultilinearMap.map_smul_univ]
    rfl
  rw [hA]
  calc
    ‖∑ β : Fin j → Fin (Module.finrank Real V),
        (∏ i : Fin j, b.repr (m i) (β i)) • A (fun i => b (β i))‖
        ≤ ∑ β : Fin j → Fin (Module.finrank Real V),
          ‖(∏ i : Fin j, b.repr (m i) (β i)) • A (fun i => b (β i))‖ :=
      norm_sum_le _ _
    _ = ∑ β : Fin j → Fin (Module.finrank Real V),
          |∏ i : Fin j, b.repr (m i) (β i)| * ‖A (fun i => b (β i))‖ := by
      apply Finset.sum_congr rfl
      intro β _
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ β : Fin j → Fin (Module.finrank Real V),
          (∏ i : Fin j, ‖m i‖) * ‖A (fun i => b (β i))‖ := by
      gcongr with β
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _)
        (fun i _ => orthonormal_repr_abs_le_norm b (m i) (β i))
    _ = C * ∏ i : Fin j, ‖m i‖ := by
      unfold C
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro β _
      ring

theorem continuousLinearMap_norm_le_sum_stdOrthonormalBasis
    {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] [NormedAddCommGroup G] [NormedSpace Real G]
    (A : V →L[Real] G) :
    ‖A‖ ≤ ∑ i : Fin (Module.finrank Real V),
      ‖A ((stdOrthonormalBasis Real V) i)‖ := by
  classical
  let b := stdOrthonormalBasis Real V
  let C : Real := ∑ i : Fin (Module.finrank Real V), ‖A (b i)‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound (𝕜 := Real) (𝕜₂ := Real) A hC ?_
  intro v
  calc
    ‖A v‖ = ‖A (∑ i, b.repr v i • b i)‖ := by
      rw [b.sum_repr]
    _ = ‖∑ i, A (b.repr v i • b i)‖ := by rw [map_sum]
    _ ≤ ∑ i, ‖A (b.repr v i • b i)‖ := norm_sum_le _ _
    _ = ∑ i, |b.repr v i| * ‖A (b i)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, ‖v‖ * ‖A (b i)‖ := by
      gcongr with i
      exact orthonormal_repr_abs_le_norm b v i
    _ = C * ‖v‖ := by
      unfold C
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem continuousLinearMap_two_norm_le_sum_stdOrthonormalBasis
    {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] [NormedAddCommGroup G] [NormedSpace Real G]
    (A : V →L[Real] V →L[Real] G) :
    ‖A‖ ≤ ∑ i, ∑ j : Fin (Module.finrank Real V),
      ‖A ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) j)‖ := by
  calc
    ‖A‖ ≤ ∑ i : Fin (Module.finrank Real V),
        ‖A ((stdOrthonormalBasis Real V) i)‖ :=
      continuousLinearMap_norm_le_sum_stdOrthonormalBasis A
    _ ≤ ∑ i : Fin (Module.finrank Real V),
        ∑ j : Fin (Module.finrank Real V),
          ‖A ((stdOrthonormalBasis Real V) i)
            ((stdOrthonormalBasis Real V) j)‖ := by
      gcongr with i
      exact continuousLinearMap_norm_le_sum_stdOrthonormalBasis
        (A ((stdOrthonormalBasis Real V) i))

theorem holderWith_continuousMultilinearMap_of_stdOrthonormalBasis
    {X V G : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup G] [NormedSpace Real G]
    {j : Nat} {alpha : NNReal}
    (A : X → ContinuousMultilinearMap Real (fun _ : Fin j => V) G)
    (C : (Fin j → Fin (Module.finrank Real V)) → NNReal)
    (h : ∀ β, HolderWith (C β) alpha
      (fun x => A x (fun i => (stdOrthonormalBasis Real V) (β i)))) :
    HolderWith (∑ β, C β) alpha A := by
  intro x y
  have hreal : dist (A x) (A y) ≤
      (∑ β, C β : NNReal) * dist x y ^ (alpha : Real) := by
    rw [dist_eq_norm]
    calc
      ‖A x - A y‖ ≤ ∑ β : Fin j → Fin (Module.finrank Real V),
          ‖(A x - A y) (fun i => (stdOrthonormalBasis Real V) (β i))‖ :=
        continuousMultilinearMap_norm_le_sum_stdOrthonormalBasis (A x - A y)
      _ ≤ ∑ β : Fin j → Fin (Module.finrank Real V),
          (C β : Real) * dist x y ^ (alpha : Real) := by
        gcongr with β
        simpa only [sub_apply, dist_eq_norm] using
          (h β).dist_le x y
      _ = (∑ β, C β : NNReal) * dist x y ^ (alpha : Real) := by
        push_cast
        rw [Finset.sum_mul]
  rw [edist_dist, edist_dist]
  calc
    ENNReal.ofReal (dist (A x) (A y)) ≤
        ENNReal.ofReal (((∑ β, C β : NNReal) : Real) *
          dist x y ^ (alpha : Real)) := ENNReal.ofReal_le_ofReal hreal
    _ = ((∑ β, C β : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul (by positivity :
        (0 : Real) ≤ (∑ β, C β : NNReal))]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = ((∑ β, C β : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) alpha.coe_nonneg]

theorem holderWith_continuousLinearMap_two_of_stdOrthonormalBasis
    {X V G : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup G] [NormedSpace Real G]
    {alpha : NNReal}
    (A : X → V →L[Real] V →L[Real] G)
    (C : Fin (Module.finrank Real V) → Fin (Module.finrank Real V) → NNReal)
    (h : ∀ i j, HolderWith (C i j) alpha
      (fun x ↦ A x ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) j))) :
    HolderWith (∑ i, ∑ j, C i j) alpha A := by
  intro x y
  have hreal : dist (A x) (A y) ≤
      ((∑ i, ∑ j, C i j : NNReal) : Real) *
        dist x y ^ (alpha : Real) := by
    rw [dist_eq_norm (A x) (A y)]
    calc
      ‖A x - A y‖ ≤
          ∑ i, ∑ j : Fin (Module.finrank Real V),
            ‖(A x - A y) ((stdOrthonormalBasis Real V) i)
              ((stdOrthonormalBasis Real V) j)‖ :=
        continuousLinearMap_two_norm_le_sum_stdOrthonormalBasis (A x - A y)
      _ ≤ ∑ i, ∑ j : Fin (Module.finrank Real V),
          (C i j : Real) * dist x y ^ (alpha : Real) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        simpa only [sub_apply, dist_eq_norm] using
          (h i j).dist_le x y
      _ = ((∑ i, ∑ j, C i j : NNReal) : Real) *
          dist x y ^ (alpha : Real) := by
        push_cast
        simp only [Finset.sum_mul]
  rw [edist_dist, edist_dist]
  calc
    ENNReal.ofReal (dist (A x) (A y)) ≤
        ENNReal.ofReal (((∑ i, ∑ j, C i j : NNReal) : Real) *
          dist x y ^ (alpha : Real)) := ENNReal.ofReal_le_ofReal hreal
    _ = ((∑ i, ∑ j, C i j : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul (by positivity :
        (0 : Real) ≤ (∑ i, ∑ j, C i j : NNReal))]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = ((∑ i, ∑ j, C i j : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) alpha.coe_nonneg]

end

section Spatial

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {V : Type*} [NormedAddCommGroup V] in
theorem eHolderSeminormOn_add_le
    (alpha : NNReal) (s : Set X) (f g : X → F) :
    eHolderSeminormOn alpha s (f + g) ≤
      eHolderSeminormOn alpha s f + eHolderSeminormOn alpha s g := by
  unfold eHolderSeminormOn
  exact eHolderNorm_add_le

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real F] in
theorem eHolderSeminormOn_sub_le
    (alpha : NNReal) (s : Set X) (f g : X → F) :
    eHolderSeminormOn alpha s (f - g) ≤
      eHolderSeminormOn alpha s f + eHolderSeminormOn alpha s g := by
  have hrestrict : s.domRestrict (f - g) = s.domRestrict f - s.domRestrict g := by
    rfl
  have hneg : eHolderNorm alpha (-s.domRestrict g) =
      eHolderNorm alpha (s.domRestrict g) := by
    have hfun : -s.domRestrict g = (-1 : Real) • s.domRestrict g := by
      ext x
      simp
    rw [hfun, eHolderNorm_smul]
    simp
  unfold eHolderSeminormOn
  rw [hrestrict, sub_eq_add_neg]
  exact eHolderNorm_add_le.trans_eq
    (congrArg (eHolderNorm alpha (s.domRestrict f) + ·) hneg)

section

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedSpace Real F]
def eContDiffHolderGaugeOn (k : Nat) (alpha : NNReal)
    (s : Set V) (f : V → F) : ENNReal :=
  (∑ j ∈ Finset.range (k + 1), eSupNormOn s (iteratedFDeriv Real j f)) +
    eHolderSeminormOn alpha s (iteratedFDeriv Real k f)

theorem eContDiffHolderGaugeOn_add_le
    (k : Nat) (alpha : NNReal) (s : Set V) (f g : V → F)
    (hf : ∀ x ∈ s, ContDiffAt Real k f x)
    (hg : ∀ x ∈ s, ContDiffAt Real k g x) :
    eContDiffHolderGaugeOn k alpha s (f + g) ≤
      eContDiffHolderGaugeOn k alpha s f +
        eContDiffHolderGaugeOn k alpha s g := by
  have hjet : ∀ j ≤ k, Set.EqOn
      (iteratedFDeriv Real j (f + g))
      (iteratedFDeriv Real j f + iteratedFDeriv Real j g) s := by
    intro j hj x hx
    exact iteratedFDeriv_add_apply
      ((hf x hx).of_le (by exact_mod_cast hj))
      ((hg x hx).of_le (by exact_mod_cast hj))
  unfold eContDiffHolderGaugeOn
  calc
    (∑ j ∈ Finset.range (k + 1),
        eSupNormOn s (iteratedFDeriv Real j (f + g))) +
        eHolderSeminormOn alpha s (iteratedFDeriv Real k (f + g)) ≤
      (∑ j ∈ Finset.range (k + 1),
        (eSupNormOn s (iteratedFDeriv Real j f) +
          eSupNormOn s (iteratedFDeriv Real j g))) +
        (eHolderSeminormOn alpha s (iteratedFDeriv Real k f) +
          eHolderSeminormOn alpha s (iteratedFDeriv Real k g)) := by
      gcongr with j hj
      · exact (eSupNormOn_congr
          (hjet j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))).le.trans
            (eSupNormOn_add_le s _ _)
      · exact (eHolderSeminormOn_congr (hjet k le_rfl) alpha).le.trans
          (eHolderSeminormOn_add_le alpha s _ _)
    _ = ((∑ j ∈ Finset.range (k + 1),
          eSupNormOn s (iteratedFDeriv Real j f)) +
          eHolderSeminormOn alpha s (iteratedFDeriv Real k f)) +
        ((∑ j ∈ Finset.range (k + 1),
          eSupNormOn s (iteratedFDeriv Real j g)) +
          eHolderSeminormOn alpha s (iteratedFDeriv Real k g)) := by
      simp only [Finset.sum_add_distrib, add_assoc, add_left_comm]

theorem eContDiffHolderGaugeOn_sub_le
    (k : Nat) (alpha : NNReal) (s : Set V) (f g : V → F)
    (hf : ∀ x ∈ s, ContDiffAt Real k f x)
    (hg : ∀ x ∈ s, ContDiffAt Real k g x) :
    eContDiffHolderGaugeOn k alpha s (f - g) ≤
      eContDiffHolderGaugeOn k alpha s f +
        eContDiffHolderGaugeOn k alpha s g := by
  have hjet : ∀ j ≤ k, Set.EqOn
      (iteratedFDeriv Real j (f - g))
      (iteratedFDeriv Real j f - iteratedFDeriv Real j g) s := by
    intro j hj x hx
    exact iteratedFDeriv_sub_apply
      ((hf x hx).of_le (by exact_mod_cast hj))
      ((hg x hx).of_le (by exact_mod_cast hj))
  unfold eContDiffHolderGaugeOn
  calc
    (∑ j ∈ Finset.range (k + 1),
        eSupNormOn s (iteratedFDeriv Real j (f - g))) +
        eHolderSeminormOn alpha s (iteratedFDeriv Real k (f - g)) ≤
      (∑ j ∈ Finset.range (k + 1),
        (eSupNormOn s (iteratedFDeriv Real j f) +
          eSupNormOn s (iteratedFDeriv Real j g))) +
        (eHolderSeminormOn alpha s (iteratedFDeriv Real k f) +
          eHolderSeminormOn alpha s (iteratedFDeriv Real k g)) := by
      gcongr with j hj
      · exact (eSupNormOn_congr
          (hjet j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))).le.trans
            (eSupNormOn_sub_le s _ _)
      · exact (eHolderSeminormOn_congr (hjet k le_rfl) alpha).le.trans
          (eHolderSeminormOn_sub_le alpha s _ _)
    _ = ((∑ j ∈ Finset.range (k + 1),
          eSupNormOn s (iteratedFDeriv Real j f)) +
          eHolderSeminormOn alpha s (iteratedFDeriv Real k f)) +
        ((∑ j ∈ Finset.range (k + 1),
          eSupNormOn s (iteratedFDeriv Real j g)) +
          eHolderSeminormOn alpha s (iteratedFDeriv Real k g)) := by
      simp only [Finset.sum_add_distrib, add_assoc, add_left_comm]

def IsContDiffHolderOn (k : Nat) (alpha : NNReal)
    (s : Set V) (f : V → F) : Prop :=
  (∀ x ∈ s, ContDiffAt Real k f x) ∧
    MemHolder alpha (s.domRestrict (iteratedFDeriv Real k f))

theorem eContDiffHolderGaugeOn_le
    {k : Nat} {alpha : NNReal} {s : Set V} {f : V → F}
    (Cspatial : Nat → NNReal) (Cholder : NNReal)
    (hspatial : ∀ j ≤ k, ∀ x ∈ s,
      ‖iteratedFDeriv Real j f x‖ ≤ Cspatial j)
    (hholder : HolderWith Cholder alpha
      (s.domRestrict (iteratedFDeriv Real k f))) :
    eContDiffHolderGaugeOn k alpha s f ≤
      (∑ j ∈ Finset.range (k + 1), (Cspatial j : ENNReal)) + Cholder := by
  have hsup : ∀ j ≤ k,
      eSupNormOn s (iteratedFDeriv Real j f) ≤ Cspatial j := by
    intro j hj
    rw [eSupNormOn_le]
    intro x hx
    rw [ENNReal.ofReal_le_coe]
    exact hspatial j hj x hx
  have hholder' : eHolderSeminormOn alpha s (iteratedFDeriv Real k f) ≤
      Cholder := hholder.eHolderNorm_le
  unfold eContDiffHolderGaugeOn
  gcongr with j hj
  exact hsup j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem spatialJet_le_eContDiffHolderGaugeOn
    (k : Nat) (alpha : NNReal) (s : Set V) (f : V → F)
    {j : Nat} (hj : j ≤ k) (x : V) (hx : x ∈ s) :
    ENNReal.ofReal ‖iteratedFDeriv Real j f x‖ ≤
      eContDiffHolderGaugeOn k alpha s f := by
  have hterm : eSupNormOn s (iteratedFDeriv Real j f) ≤
      ∑ q ∈ Finset.range (k + 1), eSupNormOn s (iteratedFDeriv Real q f) :=
    Finset.single_le_sum
      (fun q _ => (bot_le : (⊥ : ENNReal) ≤
        eSupNormOn s (iteratedFDeriv Real q f)))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  exact (norm_le_eSupNormOn s (iteratedFDeriv Real j f) x hx).trans
    (hterm.trans (by
      unfold eContDiffHolderGaugeOn
      exact le_add_right le_rfl))

theorem holderSeminorm_le_eContDiffHolderGaugeOn
    (k : Nat) (alpha : NNReal) (s : Set V) (f : V → F) :
    eHolderSeminormOn alpha s (iteratedFDeriv Real k f) ≤
      eContDiffHolderGaugeOn k alpha s f := by
  unfold eContDiffHolderGaugeOn
  exact le_add_left le_rfl

theorem spatialJet_norm_le {k : Nat} {alpha C : NNReal}
    {s : Set V} {f : V → F}
    (h : eContDiffHolderGaugeOn k alpha s f ≤ C)
    {j : Nat} (hj : j ≤ k) {x : V} (hx : x ∈ s) :
    ‖iteratedFDeriv Real j f x‖ ≤ C := by
  rw [← ENNReal.ofReal_le_coe]
  exact (spatialJet_le_eContDiffHolderGaugeOn k alpha s f hj x hx).trans h

theorem topSpatialJet_holderWith_restrict {k : Nat} {alpha C : NNReal}
    {s : Set V} {f : V → F}
    (h : eContDiffHolderGaugeOn k alpha s f ≤ C) :
    HolderWith C alpha (s.domRestrict (iteratedFDeriv Real k f)) :=
  holderWith_restrict_of_eHolderSeminormOn_le
    ((holderSeminorm_le_eContDiffHolderGaugeOn k alpha s f).trans h)

def hessianCurryEquiv
    (V F : Type*) [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F] :
    (V [×2]→L[Real] F) ≃ₗᵢ[Real] V →L[Real] V →L[Real] F :=
  (continuousMultilinearCurryRightEquiv' Real 1 V F).trans
    (continuousMultilinearCurryFin1 Real V (V →L[Real] F))

theorem hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv
    (u : V → F) (x : V) :
    hessianCurryEquiv V F (iteratedFDeriv Real 2 u x) =
      fderiv Real (fderiv Real u) x := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [hessianCurryEquiv, LinearIsometryEquiv.trans_apply,
    continuousMultilinearCurryFin1_apply,
    continuousMultilinearCurryRightEquiv_apply', iteratedFDeriv_two_apply]
  simp

theorem hessianCurryEquiv_iteratedFDeriv_two
    (u : V → F) (du : V → V →L[Real] F)
    (d2u : V → V →L[Real] V →L[Real] F)
    (hu : ∀ x, HasFDerivAt u (du x) x)
    (hdu : ∀ x, HasFDerivAt du (d2u x) x) (x : V) :
    hessianCurryEquiv V F (iteratedFDeriv Real 2 u x) = d2u x := by
  have hfd : fderiv Real u = du := by
    funext y
    exact (hu y).fderiv
  rw [hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv, hfd,
    (hdu x).fderiv]

end

end Spatial

section

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
abbrev ParabolicPoint (V : Type*) :=
  Metric.Snowflaking Real (1 / 2) (by norm_num) (by norm_num) × V

def parabolicPoint {V : Type*} (t : Real) (x : V) : ParabolicPoint V :=
  (Metric.Snowflaking.toSnowflaking t, x)

def ParabolicPoint.time {V : Type*} (p : ParabolicPoint V) : Real :=
  p.1.ofSnowflaking

def ParabolicPoint.space {V : Type*} (p : ParabolicPoint V) : V :=
  p.2

@[simp]
theorem parabolicPoint_time {V : Type*} (t : Real) (x : V) :
    (parabolicPoint t x).time = t := rfl

@[simp]
theorem parabolicPoint_space {V : Type*} (t : Real) (x : V) :
    (parabolicPoint t x).space = x := rfl

@[simp]
theorem parabolicPoint_time_space {V : Type*} (p : ParabolicPoint V) :
    parabolicPoint p.time p.space = p := by
  rcases p with ⟨⟨t⟩, x⟩
  rfl

theorem dist_parabolicPoint {V : Type*} [PseudoMetricSpace V]
    (t s : Real) (x y : V) :
    dist (parabolicPoint t x) (parabolicPoint s y) =
      max (|t - s| ^ (1 / 2 : Real)) (dist x y) := by
  simp [parabolicPoint, Prod.dist_eq, Real.dist_eq]

def parabolicCylinder {V : Type*} (J : Set Real) (Omega : Set V) :
    Set (ParabolicPoint V) :=
  {p | p.time ∈ J ∧ p.space ∈ Omega}

theorem parabolicHolder_time_dist_le
    {V F : Type*} [PseudoMetricSpace V] [MetricSpace F]
    {alpha C : NNReal} {Q : Set (ParabolicPoint V)}
    {f : ParabolicPoint V → F}
    (h : HolderWith C alpha (Q.domRestrict f))
    {t s : Real} {x : V}
    (ht : parabolicPoint t x ∈ Q) (hs : parabolicPoint s x ∈ Q) :
    dist (f (parabolicPoint t x)) (f (parabolicPoint s x)) ≤
      C * |t - s| ^ ((alpha : Real) / 2) := by
  have hraw := h.dist_le
    (⟨parabolicPoint t x, ht⟩ : Q) (⟨parabolicPoint s x, hs⟩ : Q)
  change dist (f (parabolicPoint t x)) (f (parabolicPoint s x)) ≤
    C * dist (parabolicPoint t x) (parabolicPoint s x) ^ (alpha : Real) at hraw
  rw [dist_parabolicPoint, dist_self, max_eq_left
    (Real.rpow_nonneg (abs_nonneg _) _)] at hraw
  rw [← Real.rpow_mul (abs_nonneg _) (1 / 2 : Real) (alpha : Real)] at hraw
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hraw

theorem holderWith_slice_of_parabolicCylinder
    {V F : Type*} [PseudoMetricSpace V] [PseudoMetricSpace F]
    {alpha C : NNReal} {J : Set Real} {f : Real → V → F}
    (h : HolderWith C alpha
      ((parabolicCylinder J Set.univ).domRestrict
        (fun p => f p.time p.space)))
    {t : Real} (ht : t ∈ J) :
    HolderWith C alpha (f t) := by
  intro x y
  let px : parabolicCylinder J (Set.univ : Set V) :=
    ⟨parabolicPoint t x, ht, Set.mem_univ x⟩
  let py : parabolicCylinder J (Set.univ : Set V) :=
    ⟨parabolicPoint t y, ht, Set.mem_univ y⟩
  have hxy := h.edist_le px py
  change edist (f t x) (f t y) ≤
    (C : ENNReal) * edist px py ^ (alpha : Real) at hxy
  change edist (f t x) (f t y) ≤
    (C : ENNReal) * edist x y ^ (alpha : Real)
  rw [edist_dist, edist_dist] at hxy ⊢
  simpa [px, py, Subtype.dist_eq, dist_parabolicPoint,
    Real.zero_rpow (by norm_num : (1 / 2 : Real) ≠ 0),
    max_eq_right dist_nonneg] using hxy

theorem holderWith_parabolic_const_time
    {V F : Type*} [PseudoMetricSpace V] [PseudoMetricSpace F]
    {alpha K : NNReal} (f : V → F) (hf : HolderWith K alpha f)
    (J : Set Real) :
    HolderWith K alpha
      ((parabolicCylinder J Set.univ).domRestrict (fun p => f p.space)) := by
  have hsnd : LipschitzWith 1 (fun p : ParabolicPoint V => p.space) :=
    LipschitzWith.prod_snd
  have hfull := hf.comp hsnd.holderWith
  have hfull' : HolderWith K alpha
      (fun p : ParabolicPoint V => f p.space) := by
    simpa only [NNReal.one_rpow, mul_one, Function.comp_apply, one_mul] using! hfull
  exact (hfull'.holderOnWith (parabolicCylinder J Set.univ)).holderWith

end

section Parabolic

section

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedSpace Real F]
def parabolicSpatialJet (j : Nat) (u : Real → V → F) :
    ParabolicPoint V → (V [×j]→L[Real] F) :=
  fun p => iteratedFDeriv Real j (u p.time) p.space

def parabolicTimeDerivative (u : Real → V → F) : ParabolicPoint V → F :=
  fun p => fderiv Real (fun t => u t p.space) p.time 1

def IsParabolicC2On
    (Q : Set (ParabolicPoint V)) (u : Real → V → F) : Prop :=
  (∀ p ∈ Q, ContDiffAt Real 2 (u p.time) p.space) ∧
    ∀ p ∈ Q, DifferentiableAt Real (fun t ↦ u t p.space) p.time

theorem parabolicSpatialJet_add
    (j : Nat) (u v : Real → V → F) (p : ParabolicPoint V)
    (hu : ContDiffAt Real j (u p.time) p.space)
    (hv : ContDiffAt Real j (v p.time) p.space) :
    parabolicSpatialJet j (fun t x ↦ u t x + v t x) p =
      parabolicSpatialJet j u p + parabolicSpatialJet j v p := by
  unfold parabolicSpatialJet
  change iteratedFDeriv Real j (u p.time + v p.time) p.space = _
  rw [iteratedFDeriv_add_apply hu hv]

end

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {V : Type*}
    [NormedSpace Real F] in
theorem parabolicTimeDerivative_add
    (u v : Real → V → F) (p : ParabolicPoint V)
    (hu : DifferentiableAt Real (fun t ↦ u t p.space) p.time)
    (hv : DifferentiableAt Real (fun t ↦ v t p.space) p.time) :
    parabolicTimeDerivative (fun t x ↦ u t x + v t x) p =
      parabolicTimeDerivative u p + parabolicTimeDerivative v p := by
  unfold parabolicTimeDerivative
  change (fderiv Real
      ((fun t ↦ u t p.space) + fun t ↦ v t p.space) p.time) 1 = _
  rw [fderiv_add hu hv]
  exact add_apply _ _ _

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedSpace Real F] in
def eParabolicC2HolderGaugeOn (alpha : NNReal)
    (Q : Set (ParabolicPoint V)) (u : Real → V → F) : ENNReal :=
  (∑ j ∈ Finset.range 3, eSupNormOn Q (parabolicSpatialJet j u)) +
    eSupNormOn Q (parabolicTimeDerivative u) +
    eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) +
    eHolderSeminormOn alpha Q (parabolicTimeDerivative u)

variable {X F : Type*}  [NormedAddCommGroup F]
    {V : Type*} in
theorem eSupNormOn_mono {s t : Set X} (hst : s ⊆ t) (f : X → F) :
    eSupNormOn s f ≤ eSupNormOn t f := by
  apply iSup_le
  intro x
  exact le_iSup_of_le ⟨x, hst x.2⟩ le_rfl

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {V : Type*} in
theorem eHolderSeminormOn_mono {s t : Set X} (hst : s ⊆ t)
    (alpha : NNReal) (f : X → F) :
    eHolderSeminormOn alpha s f ≤ eHolderSeminormOn alpha t f := by
  unfold eHolderSeminormOn eHolderNorm
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  exact HolderWith.eHolderNorm_le
    ((HolderWith.restrict_iff.mp hC).mono hst).holderWith

section

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedSpace Real F]
theorem eContDiffHolderGaugeOn_mono {s t : Set V} (hst : s ⊆ t)
    (k : Nat) (alpha : NNReal) (f : V → F) :
    eContDiffHolderGaugeOn k alpha s f ≤
      eContDiffHolderGaugeOn k alpha t f := by
  unfold eContDiffHolderGaugeOn
  gcongr with j
  · exact eSupNormOn_mono hst _
  · exact eHolderSeminormOn_mono hst alpha _

theorem eParabolicC2HolderGaugeOn_mono
    {Q R : Set (ParabolicPoint V)} (hQR : Q ⊆ R)
    (alpha : NNReal) (u : Real → V → F) :
    eParabolicC2HolderGaugeOn alpha Q u ≤
      eParabolicC2HolderGaugeOn alpha R u := by
  unfold eParabolicC2HolderGaugeOn
  gcongr with j
  · exact eSupNormOn_mono hQR _
  · exact eSupNormOn_mono hQR _
  · exact eHolderSeminormOn_mono hQR alpha _
  · exact eHolderSeminormOn_mono hQR alpha _

theorem eParabolicC2HolderGaugeOn_add_le
    (alpha : NNReal) (Q : Set (ParabolicPoint V))
    (u v : Real → V → F)
    (hu : IsParabolicC2On Q u) (hv : IsParabolicC2On Q v) :
    eParabolicC2HolderGaugeOn alpha Q (fun t x ↦ u t x + v t x) ≤
      eParabolicC2HolderGaugeOn alpha Q u +
        eParabolicC2HolderGaugeOn alpha Q v := by
  have hspatial : ∀ j ≤ 2, Set.EqOn
      (parabolicSpatialJet j (fun t x ↦ u t x + v t x))
      (parabolicSpatialJet j u + parabolicSpatialJet j v) Q := by
    intro j hj p hp
    unfold parabolicSpatialJet
    change iteratedFDeriv Real j (u p.time + v p.time) p.space = _
    rw [iteratedFDeriv_add_apply
      ((hu.1 p hp).of_le (by exact_mod_cast hj))
      ((hv.1 p hp).of_le (by exact_mod_cast hj))]
    rfl
  have htime : Set.EqOn
      (parabolicTimeDerivative (fun t x ↦ u t x + v t x))
      (parabolicTimeDerivative u + parabolicTimeDerivative v) Q := by
    intro p hp
    unfold parabolicTimeDerivative
    change (fderiv Real
        ((fun t ↦ u t p.space) + fun t ↦ v t p.space) p.time) 1 =
      (fderiv Real (fun t ↦ u t p.space) p.time) 1 +
        (fderiv Real (fun t ↦ v t p.space) p.time) 1
    rw [fderiv_add (hu.2 p hp) (hv.2 p hp)]
    exact add_apply _ _ _
  unfold eParabolicC2HolderGaugeOn
  calc
    (∑ j ∈ Finset.range 3,
        eSupNormOn Q
          (parabolicSpatialJet j (fun t x ↦ u t x + v t x))) +
        eSupNormOn Q
          (parabolicTimeDerivative (fun t x ↦ u t x + v t x)) +
        eHolderSeminormOn alpha Q
          (parabolicSpatialJet 2 (fun t x ↦ u t x + v t x)) +
        eHolderSeminormOn alpha Q
          (parabolicTimeDerivative (fun t x ↦ u t x + v t x)) ≤
      (∑ j ∈ Finset.range 3,
        (eSupNormOn Q (parabolicSpatialJet j u) +
          eSupNormOn Q (parabolicSpatialJet j v))) +
        (eSupNormOn Q (parabolicTimeDerivative u) +
          eSupNormOn Q (parabolicTimeDerivative v)) +
        (eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) +
          eHolderSeminormOn alpha Q (parabolicSpatialJet 2 v)) +
        (eHolderSeminormOn alpha Q (parabolicTimeDerivative u) +
          eHolderSeminormOn alpha Q (parabolicTimeDerivative v)) := by
      gcongr with j hj
      · exact (eSupNormOn_congr
          (hspatial j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))).le.trans
            (eSupNormOn_add_le Q _ _)
      · exact (eSupNormOn_congr htime).le.trans
          (eSupNormOn_add_le Q _ _)
      · exact (eHolderSeminormOn_congr (hspatial 2 le_rfl) alpha).le.trans
          (eHolderSeminormOn_add_le alpha Q _ _)
      · exact (eHolderSeminormOn_congr htime alpha).le.trans
          (eHolderSeminormOn_add_le alpha Q _ _)
    _ = ((∑ j ∈ Finset.range 3,
          eSupNormOn Q (parabolicSpatialJet j u)) +
          eSupNormOn Q (parabolicTimeDerivative u) +
          eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) +
          eHolderSeminormOn alpha Q (parabolicTimeDerivative u)) +
        ((∑ j ∈ Finset.range 3,
          eSupNormOn Q (parabolicSpatialJet j v)) +
          eSupNormOn Q (parabolicTimeDerivative v) +
          eHolderSeminormOn alpha Q (parabolicSpatialJet 2 v) +
          eHolderSeminormOn alpha Q (parabolicTimeDerivative v)) := by
      rw [Finset.sum_add_distrib]
      abel

def IsParabolicC2HolderOn (alpha : NNReal)
    (Q : Set (ParabolicPoint V)) (u : Real → V → F) : Prop :=
  IsParabolicC2On Q u ∧
    MemHolder alpha (Q.domRestrict (parabolicSpatialJet 2 u)) ∧
    MemHolder alpha (Q.domRestrict (parabolicTimeDerivative u))

theorem eParabolicC2HolderGaugeOn_le
    {alpha : NNReal} {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (Cspatial : Nat → NNReal) (Ctime CspatialHolder CtimeHolder : NNReal)
    (hspatial : ∀ j < 3, ∀ p ∈ Q,
      ‖parabolicSpatialJet j u p‖ ≤ Cspatial j)
    (htime : ∀ p ∈ Q, ‖parabolicTimeDerivative u p‖ ≤ Ctime)
    (hspatialHolder : HolderWith CspatialHolder alpha
      (Q.domRestrict (parabolicSpatialJet 2 u)))
    (htimeHolder : HolderWith CtimeHolder alpha
      (Q.domRestrict (parabolicTimeDerivative u))) :
    eParabolicC2HolderGaugeOn alpha Q u ≤
      (∑ j ∈ Finset.range 3, (Cspatial j : ENNReal)) + Ctime +
        CspatialHolder + CtimeHolder := by
  have hsupSpatial : ∀ j < 3,
      eSupNormOn Q (parabolicSpatialJet j u) ≤ Cspatial j := by
    intro j hj
    rw [eSupNormOn_le]
    intro p hp
    rw [ENNReal.ofReal_le_coe]
    exact hspatial j hj p hp
  have hsupTime : eSupNormOn Q (parabolicTimeDerivative u) ≤ Ctime := by
    rw [eSupNormOn_le]
    intro p hp
    rw [ENNReal.ofReal_le_coe]
    exact htime p hp
  have hholderSpatial :
      eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) ≤ CspatialHolder :=
    hspatialHolder.eHolderNorm_le
  have hholderTime :
      eHolderSeminormOn alpha Q (parabolicTimeDerivative u) ≤ CtimeHolder :=
    htimeHolder.eHolderNorm_le
  unfold eParabolicC2HolderGaugeOn
  gcongr with j hj
  exact hsupSpatial j (Finset.mem_range.mp hj)

theorem parabolicSpatialJet_le
    (alpha : NNReal) (Q : Set (ParabolicPoint V)) (u : Real → V → F)
    {j : Nat} (hj : j < 3) (p : ParabolicPoint V) (hp : p ∈ Q) :
    ENNReal.ofReal ‖parabolicSpatialJet j u p‖ ≤
      eParabolicC2HolderGaugeOn alpha Q u := by
  have hterm : eSupNormOn Q (parabolicSpatialJet j u) ≤
      ∑ q ∈ Finset.range 3, eSupNormOn Q (parabolicSpatialJet q u) :=
    Finset.single_le_sum
      (fun q _ => (bot_le : (⊥ : ENNReal) ≤
        eSupNormOn Q (parabolicSpatialJet q u)))
      (Finset.mem_range.mpr hj)
  exact (norm_le_eSupNormOn Q (parabolicSpatialJet j u) p hp).trans
    (hterm.trans (by
      unfold eParabolicC2HolderGaugeOn
      exact (le_add_right le_rfl).trans
        ((le_add_right le_rfl).trans (le_add_right le_rfl))))

theorem parabolicTimeDerivative_le
    (alpha : NNReal) (Q : Set (ParabolicPoint V)) (u : Real → V → F)
    (p : ParabolicPoint V) (hp : p ∈ Q) :
    ENNReal.ofReal ‖parabolicTimeDerivative u p‖ ≤
      eParabolicC2HolderGaugeOn alpha Q u := by
  exact (norm_le_eSupNormOn Q (parabolicTimeDerivative u) p hp).trans (by
    unfold eParabolicC2HolderGaugeOn
    exact (le_add_left le_rfl).trans
      ((le_add_right le_rfl).trans (le_add_right le_rfl)))

theorem parabolicSpatialHolderSeminorm_le
    (alpha : NNReal) (Q : Set (ParabolicPoint V)) (u : Real → V → F) :
    eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) ≤
      eParabolicC2HolderGaugeOn alpha Q u := by
  unfold eParabolicC2HolderGaugeOn
  exact (le_add_left le_rfl).trans (le_add_right le_rfl)

theorem parabolicTimeHolderSeminorm_le
    (alpha : NNReal) (Q : Set (ParabolicPoint V)) (u : Real → V → F) :
    eHolderSeminormOn alpha Q (parabolicTimeDerivative u) ≤
      eParabolicC2HolderGaugeOn alpha Q u := by
  unfold eParabolicC2HolderGaugeOn
  exact le_add_left le_rfl

theorem parabolicSpatialJet_norm_le {alpha C : NNReal}
    {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (h : eParabolicC2HolderGaugeOn alpha Q u ≤ C)
    {j : Nat} (hj : j ≤ 2) {p : ParabolicPoint V} (hp : p ∈ Q) :
    ‖parabolicSpatialJet j u p‖ ≤ C := by
  rw [← ENNReal.ofReal_le_coe]
  exact (parabolicSpatialJet_le alpha Q u (by omega) p hp).trans h

theorem parabolicTimeDerivative_norm_le {alpha C : NNReal}
    {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (h : eParabolicC2HolderGaugeOn alpha Q u ≤ C)
    {p : ParabolicPoint V} (hp : p ∈ Q) :
    ‖parabolicTimeDerivative u p‖ ≤ C := by
  rw [← ENNReal.ofReal_le_coe]
  exact (parabolicTimeDerivative_le alpha Q u p hp).trans h

theorem parabolicSpatialJet_holderWith_restrict {alpha C : NNReal}
    {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (h : eParabolicC2HolderGaugeOn alpha Q u ≤ C) :
    HolderWith C alpha (Q.domRestrict (parabolicSpatialJet 2 u)) :=
  holderWith_restrict_of_eHolderSeminormOn_le
    ((parabolicSpatialHolderSeminorm_le alpha Q u).trans h)

theorem eContDiffHolderGaugeOn_slice_le
    {alpha C : NNReal} {J : Set Real} {u : Real → V → F}
    {t : Real} (ht : t ∈ J)
    (h : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) u ≤ C) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u t) ≤
      (∑ _j ∈ Finset.range 3, (C : ENNReal)) + C := by
  apply eContDiffHolderGaugeOn_le (fun _ => C) C
  · intro j hj x hx
    have hp : parabolicPoint t x ∈ parabolicCylinder J (Set.univ : Set V) :=
      ⟨ht, Set.mem_univ x⟩
    exact parabolicSpatialJet_norm_le
      (alpha := alpha) (C := C)
      (Q := parabolicCylinder J (Set.univ : Set V)) (u := u)
      h (j := j) hj (p := parabolicPoint t x) hp
  · have hpar := parabolicSpatialJet_holderWith_restrict h
    have hslice := holderWith_slice_of_parabolicCylinder
      (f := fun q x => parabolicSpatialJet 2 u (parabolicPoint q x)) hpar ht
    have hslice' := (hslice.holderOnWith (Set.univ : Set V)).holderWith
    simpa only [parabolicSpatialJet, parabolicPoint_time,
      parabolicPoint_space] using! hslice'

end

end Parabolic

end CalabiYau.Schauder
