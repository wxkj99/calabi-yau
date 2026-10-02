-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Holder/Operator.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Holder.NormedSpace
public import CalabiYau.Analysis.Holder.Interpolation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section

-- and its private helpers occur in public declarations.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Set
open scoped ENNReal NNReal

namespace CalabiYau.Schauder

section Map

variable {X F G : Type*} [MetricSpace X]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]

omit [MetricSpace X] in
theorem eSupNormOn_comp_continuousLinearMap_le
    (L : F →L[Real] G) (f : X → F) :
    eSupNormOn Set.univ (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eSupNormOn Set.univ f := by
  rw [eSupNormOn_le]
  intro x _hx
  calc
    ENNReal.ofReal ‖L (f x)‖ ≤ ENNReal.ofReal (‖L‖ * ‖f x‖) :=
      ENNReal.ofReal_le_ofReal (L.le_opNorm (f x))
    _ = (‖L‖₊ : ENNReal) * ENNReal.ofReal ‖f x‖ := by
      rw [ENNReal.ofReal_mul (norm_nonneg L), ofReal_norm,
        enorm_eq_nnnorm]
    _ ≤ (‖L‖₊ : ENNReal) * eSupNormOn Set.univ f :=
      mul_le_mul_right
        (norm_le_eSupNormOn Set.univ f x (Set.mem_univ x)) _

theorem eHolderNorm_comp_continuousLinearMap_le
    {alpha : NNReal} (L : F →L[Real] G) {f : X → F}
    (hf : MemHolder alpha f) :
    eHolderNorm alpha (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eHolderNorm alpha f := by
  have hcomp := L.lipschitz.holderWith.comp hf.holderWith
  calc
    eHolderNorm alpha (fun x ↦ L (f x)) ≤
        ((‖L‖₊ * nnHolderNorm alpha f : NNReal) : ENNReal) := by
      change eHolderNorm alpha (⇑L ∘ f) ≤ _
      simpa only [Function.comp_apply, NNReal.coe_one, NNReal.rpow_one,
        mul_one, one_mul] using hcomp.eHolderNorm_le
    _ = (‖L‖₊ : ENNReal) * (nnHolderNorm alpha f : ENNReal) := by
      rw [ENNReal.coe_mul]
    _ ≤ (‖L‖₊ : ENNReal) * eHolderNorm alpha f :=
      mul_le_mul_right coe_nnHolderNorm_le_eHolderNorm _

theorem eHolderGauge_comp_continuousLinearMap_le
    {alpha : NNReal} (L : F →L[Real] G) {f : X → F}
    (hf : IsBoundedHolder alpha f) :
    eHolderGauge alpha (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eHolderGauge alpha f := by
  unfold eHolderGauge
  calc
    eSupNormOn Set.univ (fun x ↦ L (f x)) +
        eHolderNorm alpha (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eSupNormOn Set.univ f +
        (‖L‖₊ : ENNReal) * eHolderNorm alpha f :=
      add_le_add (eSupNormOn_comp_continuousLinearMap_le L f)
        (eHolderNorm_comp_continuousLinearMap_le L hf.memHolder)
    _ = (‖L‖₊ : ENNReal) *
        (eSupNormOn Set.univ f + eHolderNorm alpha f) := by
      rw [mul_add]

private def boundedHolderSpaceMapLinearMap
    (alpha : NNReal) (L : F →L[Real] G) :
    BoundedHolderSpace (X := X) (F := F) alpha →ₗ[Real]
      BoundedHolderSpace (X := X) (F := G) alpha where
  toFun f := ⟨fun x ↦ L (f x), by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top f.2)
      (eHolderGauge_comp_continuousLinearMap_le L f.2)⟩
  map_add' f g := by
    apply boundedHolderSpace_ext
    intro x
    exact L.map_add (f x) (g x)
  map_smul' c f := by
    apply boundedHolderSpace_ext
    intro x
    exact L.map_smul c (f x)

private theorem norm_boundedHolderSpaceMapLinearMap_le
    {alpha : NNReal} (L : F →L[Real] G)
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    ‖boundedHolderSpaceMapLinearMap alpha L f‖ ≤ ‖L‖ * ‖f‖ := by
  rw [norm_boundedHolderSpace_eq, norm_boundedHolderSpace_eq]
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top f.2)
    (eHolderGauge_comp_continuousLinearMap_le L f.2)
  change (eHolderGauge alpha (fun x => L (boundedHolderSpaceFun f x))).toReal ≤
    ((‖L‖₊ : ENNReal) * eHolderGauge alpha (boundedHolderSpaceFun f)).toReal at hreal
  change (eHolderGauge alpha (fun x => L (f x))).toReal ≤
    ‖L‖ * (eHolderGauge alpha (fun x => f x)).toReal
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, coe_nnnorm,
    ofReal_norm, enorm_eq_nnnorm]
    using hreal

def boundedHolderSpaceMap (alpha : NNReal) (L : F →L[Real] G) :
    BoundedHolderSpace (X := X) (F := F) alpha →L[Real]
      BoundedHolderSpace (X := X) (F := G) alpha :=
  LinearMap.mkContinuous (boundedHolderSpaceMapLinearMap alpha L) ‖L‖
    (norm_boundedHolderSpaceMapLinearMap_le L)

@[simp]
theorem boundedHolderSpaceMap_apply
    (alpha : NNReal) (L : F →L[Real] G)
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    boundedHolderSpaceMap alpha L f x = L (f x) :=
  rfl

theorem norm_boundedHolderSpaceMap_le
    (alpha : NNReal) (L : F →L[Real] G) :
    ‖boundedHolderSpaceMap (X := X) alpha L‖ ≤ ‖L‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg L)
    (norm_boundedHolderSpaceMapLinearMap_le L)

end Map

section BoundedContinuousFunction

variable {X F : Type*} [MetricSpace X]
  [NormedAddCommGroup F] [NormedSpace Real F]

private def boundedHolderSpaceToBoundedContinuousFunctionLinearMap
    (alpha : NNReal) (halpha : 0 < alpha) :
    BoundedHolderSpace (X := X) (F := F) alpha →ₗ[Real]
      BoundedContinuousFunction X F where
  toFun f :=
    ⟨⟨boundedHolderSpaceFun f,
        (boundedHolderSpace_holderWith f).continuous halpha⟩,
      ⟨2 * ‖f‖, fun x y ↦ by
        rw [dist_eq_norm]
        exact (norm_sub_le (f x) (f y)).trans
          ((add_le_add (norm_boundedHolderSpace_apply_le f x)
            (norm_boundedHolderSpace_apply_le f y)).trans_eq (by ring))⟩⟩
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_smul' c f := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl

private theorem norm_boundedHolderSpaceToBoundedContinuousFunctionLinearMap_le
    {alpha : NNReal} (halpha : 0 < alpha)
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    ‖boundedHolderSpaceToBoundedContinuousFunctionLinearMap alpha halpha f‖ ≤
      ‖f‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg f)]
  intro x
  exact norm_boundedHolderSpace_apply_le f x

def boundedHolderSpaceToBoundedContinuousFunction
    (alpha : NNReal) (halpha : 0 < alpha) :
    BoundedHolderSpace (X := X) (F := F) alpha →L[Real]
      BoundedContinuousFunction X F :=
  LinearMap.mkContinuous
    (boundedHolderSpaceToBoundedContinuousFunctionLinearMap alpha halpha) 1
    (fun f ↦ by simpa using
      norm_boundedHolderSpaceToBoundedContinuousFunctionLinearMap_le halpha f)

@[simp]
theorem boundedHolderSpaceToBoundedContinuousFunction_apply
    (alpha : NNReal) (halpha : 0 < alpha)
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    boundedHolderSpaceToBoundedContinuousFunction alpha halpha f x = f x :=
  rfl

theorem norm_boundedHolderSpaceToBoundedContinuousFunction_le
    (alpha : NNReal) (halpha : 0 < alpha) :
    ‖boundedHolderSpaceToBoundedContinuousFunction
      (X := X) (F := F) alpha halpha‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun f ↦ by simpa using
      norm_boundedHolderSpaceToBoundedContinuousFunctionLinearMap_le halpha f)

end BoundedContinuousFunction

section EllipticBoundedContinuousFunction

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

private def contDiffHolderSpaceToBoundedContinuousFunctionLinearMap
    (k : Nat) (alpha : NNReal) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →ₗ[Real]
      BoundedContinuousFunction V F where
  toFun f := BoundedContinuousFunction.ofNormedAddCommGroup
    (contDiffHolderSpaceFun f)
    (by
      have hf : ContDiff Real k (contDiffHolderSpaceFun f) := by
        rw [contDiff_iff_contDiffAt]
        intro x
        exact f.2.1.1 x (Set.mem_univ x)
      exact hf.continuous)
    ‖f‖ (norm_contDiffHolderSpace_apply_le f)
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_smul' c f := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl

private theorem norm_contDiffHolderSpaceToBoundedContinuousFunctionLinearMap_le
    {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    ‖contDiffHolderSpaceToBoundedContinuousFunctionLinearMap k alpha f‖ ≤
      ‖f‖ := by
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (norm_nonneg f) (norm_contDiffHolderSpace_apply_le f)

def contDiffHolderSpaceToBoundedContinuousFunction
    (k : Nat) (alpha : NNReal) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedContinuousFunction V F :=
  LinearMap.mkContinuous
    (contDiffHolderSpaceToBoundedContinuousFunctionLinearMap k alpha) 1
    (fun f ↦ by simpa using
      norm_contDiffHolderSpaceToBoundedContinuousFunctionLinearMap_le f)

@[simp]
theorem contDiffHolderSpaceToBoundedContinuousFunction_apply
    (k : Nat) (alpha : NNReal)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceToBoundedContinuousFunction k alpha f x = f x :=
  rfl

theorem norm_contDiffHolderSpaceToBoundedContinuousFunction_le
    (k : Nat) (alpha : NNReal) :
    ‖contDiffHolderSpaceToBoundedContinuousFunction
      (V := V) (F := F) k alpha‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun f ↦ by simpa using
      norm_contDiffHolderSpaceToBoundedContinuousFunctionLinearMap_le f)

private def contDiffHolderSpaceJetLinearMap
    (k : Nat) (alpha : NNReal) (j : Nat) (hj : j ≤ k) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →ₗ[Real]
      BoundedContinuousFunction V (V [×j]→L[Real] F) where
  toFun f := BoundedContinuousFunction.ofNormedAddCommGroup
    (iteratedFDeriv Real j (contDiffHolderSpaceFun f))
    (by
      have hf : ContDiff Real k (contDiffHolderSpaceFun f) := by
        rw [contDiff_iff_contDiffAt]
        intro x
        exact f.2.1.1 x (Set.mem_univ x)
      exact hf.continuous_iteratedFDeriv (by exact_mod_cast hj))
    ‖f‖ (contDiffHolderSpace_iteratedFDeriv_norm_le f hj)
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    exact iteratedFDeriv_add_apply
      ((f.2.1.1 x (Set.mem_univ x)).of_le (by exact_mod_cast hj))
      ((g.2.1.1 x (Set.mem_univ x)).of_le (by exact_mod_cast hj))
  map_smul' c f := by
    apply BoundedContinuousFunction.ext
    intro x
    exact iteratedFDeriv_const_smul_apply
      ((f.2.1.1 x (Set.mem_univ x)).of_le (by exact_mod_cast hj))

private theorem norm_contDiffHolderSpaceJetLinearMap_le
    {k : Nat} {alpha : NNReal} {j : Nat} (hj : j ≤ k)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    ‖contDiffHolderSpaceJetLinearMap k alpha j hj f‖ ≤ ‖f‖ := by
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (norm_nonneg f) (contDiffHolderSpace_iteratedFDeriv_norm_le f hj)

def contDiffHolderSpaceJet
    (k : Nat) (alpha : NNReal) (j : Nat) (hj : j ≤ k) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedContinuousFunction V (V [×j]→L[Real] F) :=
  LinearMap.mkContinuous
    (contDiffHolderSpaceJetLinearMap k alpha j hj) 1
    (fun f ↦ by simpa using
      norm_contDiffHolderSpaceJetLinearMap_le hj f)

@[simp]
theorem contDiffHolderSpaceJet_apply
    (k : Nat) (alpha : NNReal) (j : Nat) (hj : j ≤ k)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceJet k alpha j hj f x =
      iteratedFDeriv Real j (contDiffHolderSpaceFun f) x :=
  rfl

theorem norm_contDiffHolderSpaceJet_le
    (k : Nat) (alpha : NNReal) (j : Nat) (hj : j ≤ k) :
    ‖contDiffHolderSpaceJet (V := V) (F := F) k alpha j hj‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun f ↦ by simpa using norm_contDiffHolderSpaceJetLinearMap_le hj f)

def contDiffHolderSpaceFDeriv
    (k : Nat) (alpha : NNReal) (hk : 1 ≤ k) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedContinuousFunction V (V →L[Real] F) :=
  (((continuousMultilinearCurryFin1 Real V F).toContinuousLinearEquiv.toContinuousLinearMap
    ).compLeftContinuousBounded V).comp
    (contDiffHolderSpaceJet k alpha 1 hk)

@[simp]
theorem contDiffHolderSpaceFDeriv_apply
    (k : Nat) (alpha : NNReal) (hk : 1 ≤ k)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceFDeriv k alpha hk f x =
      fderiv Real (contDiffHolderSpaceFun f) x := by
  apply ContinuousLinearMap.ext
  intro v
  change continuousMultilinearCurryFin1 Real V F
      (iteratedFDeriv Real 1 (contDiffHolderSpaceFun f) x) v = _
  simp only [continuousMultilinearCurryFin1_apply,
    iteratedFDeriv_one_apply, Fin.snoc_zero]

def contDiffHolderSpaceHessian
    (k : Nat) (alpha : NNReal) (hk : 2 ≤ k) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedContinuousFunction V (V →L[Real] V →L[Real] F) :=
  (((hessianCurryEquiv V F).toContinuousLinearEquiv.toContinuousLinearMap
    ).compLeftContinuousBounded V).comp
    (contDiffHolderSpaceJet k alpha 2 hk)

@[simp]
theorem contDiffHolderSpaceHessian_apply
    (k : Nat) (alpha : NNReal) (hk : 2 ≤ k)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceHessian k alpha hk f x =
      fderiv Real (fderiv Real (contDiffHolderSpaceFun f)) x := by
  simp only [contDiffHolderSpaceHessian, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compLeftContinuousBounded_apply,
    contDiffHolderSpaceJet_apply]
  exact hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv _ _

theorem contDiffHolderSpace_hasFDerivAt
    (k : Nat) (alpha : NNReal) (hk : 1 ≤ k)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    HasFDerivAt (contDiffHolderSpaceFun f)
      (contDiffHolderSpaceFDeriv k alpha hk f x) x := by
  rw [contDiffHolderSpaceFDeriv_apply]
  exact ((f.2.1.1 x (Set.mem_univ x)).differentiableAt
    (by exact_mod_cast (Nat.ne_zero_of_lt hk))).hasFDerivAt

theorem contDiffHolderSpaceFDeriv_hasFDerivAt
    (k : Nat) (alpha : NNReal) (hk : 2 ≤ k)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    HasFDerivAt
      (contDiffHolderSpaceFDeriv k alpha ((by omega : 1 ≤ 2).trans hk) f :
        V → V →L[Real] F)
      (contDiffHolderSpaceHessian k alpha hk f x) x := by
  have hf : ContDiff Real 2 (contDiffHolderSpaceFun f) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact (f.2.1.1 y (Set.mem_univ y)).of_le (by exact_mod_cast hk)
  have hfd : ContDiff Real 1 (fderiv Real (contDiffHolderSpaceFun f)) := by
    have hf' : ContDiff Real ((1 : WithTop ℕ∞) + 1) (contDiffHolderSpaceFun f) := by
      convert hf using 1
      norm_num
    exact ((contDiff_succ_iff_fderiv (n := 1)).mp
      hf').2.2
  have heq :
      (contDiffHolderSpaceFDeriv k alpha ((by omega : 1 ≤ 2).trans hk) f :
        V → V →L[Real] F) = fderiv Real (contDiffHolderSpaceFun f) := by
    funext y
    exact contDiffHolderSpaceFDeriv_apply k alpha
      ((by omega : 1 ≤ 2).trans hk) f y
  rw [heq, contDiffHolderSpaceHessian_apply]
  exact (hfd.differentiable (by norm_num) x).hasFDerivAt

private theorem eHolderGauge_contDiffHolderSpaceFun_le
    {k : Nat} {alpha : NNReal} (hk : 1 ≤ k) (halpha : alpha ≤ 1)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    eHolderGauge alpha (contDiffHolderSpaceFun f) ≤
      ((3 * ‖f‖₊ : NNReal) : ENNReal) := by
  have hsup : eSupNormOn Set.univ (contDiffHolderSpaceFun f) ≤
      (‖f‖₊ : ENNReal) := by
    rw [eSupNormOn_le]
    intro x _hx
    rw [ENNReal.ofReal_le_coe]
    simpa using norm_contDiffHolderSpace_apply_le f x
  have hlip : LipschitzWith ‖f‖₊ (contDiffHolderSpaceFun f) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := Real)
    · exact fun x ↦ (contDiffHolderSpace_hasFDerivAt
        k alpha hk f x).differentiableAt
    · intro x
      have hreal : ‖fderiv Real (contDiffHolderSpaceFun f) x‖ ≤ ‖f‖ := by
        rw [← norm_iteratedFDeriv_one]
        exact contDiffHolderSpace_iteratedFDeriv_norm_le f hk x
      exact_mod_cast hreal
  have hzero : HolderWith (2 * ‖f‖₊) 0
      (contDiffHolderSpaceFun f) :=
    holderWith_zero_of_norm_le (norm_contDiffHolderSpace_apply_le f)
  have hnorm : ‖f‖₊ ≤ 2 * ‖f‖₊ := by
    rw [show 2 * ‖f‖₊ = ‖f‖₊ + ‖f‖₊ by ring]
    exact le_add_right le_rfl
  have hholder : HolderWith (2 * ‖f‖₊) alpha
      (contDiffHolderSpaceFun f) := by
    simpa only [max_eq_left hnorm] using
      hzero.of_le_of_le hlip.holderWith (by positivity) halpha
  unfold eHolderGauge
  calc
    eSupNormOn Set.univ (contDiffHolderSpaceFun f) +
        eHolderNorm alpha (contDiffHolderSpaceFun f) ≤
      (‖f‖₊ : ENNReal) + (2 * ‖f‖₊ : NNReal) :=
      add_le_add hsup hholder.eHolderNorm_le
    _ = ((3 * ‖f‖₊ : NNReal) : ENNReal) := by
      push_cast
      ring

private def contDiffHolderSpaceValueHolderLinearMap
    (k : Nat) (alpha : NNReal) (hk : 1 ≤ k) (halpha : alpha ≤ 1) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →ₗ[Real]
      BoundedHolderSpace (X := V) (F := F) alpha where
  toFun f := ⟨contDiffHolderSpaceFun f,
    ne_top_of_le_ne_top ENNReal.coe_ne_top
      (eHolderGauge_contDiffHolderSpaceFun_le hk halpha f)⟩
  map_add' f g := by
    apply boundedHolderSpace_ext
    intro x
    rfl
  map_smul' c f := by
    apply boundedHolderSpace_ext
    intro x
    rfl

private theorem norm_contDiffHolderSpaceValueHolderLinearMap_le
    {k : Nat} {alpha : NNReal} (hk : 1 ≤ k) (halpha : alpha ≤ 1)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    ‖contDiffHolderSpaceValueHolderLinearMap k alpha hk halpha f‖ ≤
      3 * ‖f‖ := by
  rw [norm_boundedHolderSpace_eq]
  have hreal := ENNReal.toReal_mono ENNReal.coe_ne_top
    (eHolderGauge_contDiffHolderSpaceFun_le hk halpha f)
  change (eHolderGauge alpha (contDiffHolderSpaceFun f)).toReal ≤
    3 * (eContDiffHolderGaugeOn k alpha Set.univ (contDiffHolderSpaceFun f)).toReal
  simp only [ENNReal.coe_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, coe_nnnorm, norm_contDiffHolderSpace_eq] at hreal
  norm_num at hreal
  exact hreal

def contDiffHolderSpaceValueHolder
    (k : Nat) (alpha : NNReal) (hk : 1 ≤ k) (halpha : alpha ≤ 1) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedHolderSpace (X := V) (F := F) alpha :=
  LinearMap.mkContinuous
    (contDiffHolderSpaceValueHolderLinearMap k alpha hk halpha) 3
    (norm_contDiffHolderSpaceValueHolderLinearMap_le hk halpha)

@[simp]
theorem contDiffHolderSpaceValueHolder_apply
    (k : Nat) (alpha : NNReal) (hk : 1 ≤ k) (halpha : alpha ≤ 1)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceValueHolder k alpha hk halpha f x = f x :=
  rfl

theorem norm_contDiffHolderSpaceValueHolder_le
    (k : Nat) (alpha : NNReal) (hk : 1 ≤ k) (halpha : alpha ≤ 1) :
    ‖contDiffHolderSpaceValueHolder
      (V := V) (F := F) k alpha hk halpha‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num)
    (norm_contDiffHolderSpaceValueHolderLinearMap_le hk halpha)

private theorem eHolderGauge_contDiffHolderSpaceFDeriv_le
    {k : Nat} {alpha : NNReal} (hk : 2 ≤ k) (halpha : alpha ≤ 1)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    eHolderGauge alpha
        (contDiffHolderSpaceFDeriv k alpha
          ((by omega : 1 ≤ 2).trans hk) f : V → V →L[Real] F) ≤
      ((3 * ‖f‖₊ : NNReal) : ENNReal) := by
  let df := contDiffHolderSpaceFDeriv k alpha
    ((by omega : 1 ≤ 2).trans hk) f
  let d2f := contDiffHolderSpaceHessian k alpha hk f
  have hdfnorm : ∀ x, ‖df x‖ ≤ ‖f‖ := by
    intro x
    simp only [df, contDiffHolderSpaceFDeriv_apply]
    rw [← norm_iteratedFDeriv_one]
    exact contDiffHolderSpace_iteratedFDeriv_norm_le f
      ((by omega : 1 ≤ 2).trans hk) x
  have hsup : eSupNormOn Set.univ (df : V → V →L[Real] F) ≤
      (‖f‖₊ : ENNReal) := by
    rw [eSupNormOn_le]
    intro x _hx
    rw [ENNReal.ofReal_le_coe]
    simpa using hdfnorm x
  have hd2fnorm : ∀ x, ‖d2f x‖ ≤ ‖f‖ := by
    intro x
    simp only [d2f, contDiffHolderSpaceHessian_apply]
    rw [← hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv,
      LinearIsometryEquiv.norm_map]
    exact contDiffHolderSpace_iteratedFDeriv_norm_le f hk x
  have hlip : LipschitzWith ‖f‖₊ (df : V → V →L[Real] F) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := Real)
    · exact fun x ↦ (contDiffHolderSpaceFDeriv_hasFDerivAt
        k alpha hk f x).differentiableAt
    · intro x
      rw [(contDiffHolderSpaceFDeriv_hasFDerivAt
        k alpha hk f x).fderiv]
      exact_mod_cast hd2fnorm x
  have hzero : HolderWith (2 * ‖f‖₊) 0
      (df : V → V →L[Real] F) :=
    holderWith_zero_of_norm_le (fun x ↦ by simpa using hdfnorm x)
  have hnorm : ‖f‖₊ ≤ 2 * ‖f‖₊ := by
    rw [show 2 * ‖f‖₊ = ‖f‖₊ + ‖f‖₊ by ring]
    exact le_add_right le_rfl
  have hholder : HolderWith (2 * ‖f‖₊) alpha
      (df : V → V →L[Real] F) := by
    simpa only [max_eq_left hnorm] using
      hzero.of_le_of_le hlip.holderWith (by positivity) halpha
  unfold eHolderGauge
  calc
    eSupNormOn Set.univ (df : V → V →L[Real] F) +
        eHolderNorm alpha (df : V → V →L[Real] F) ≤
      (‖f‖₊ : ENNReal) + (2 * ‖f‖₊ : NNReal) :=
      add_le_add hsup hholder.eHolderNorm_le
    _ = ((3 * ‖f‖₊ : NNReal) : ENNReal) := by
      push_cast
      ring

private def contDiffHolderSpaceFDerivHolderLinearMap
    (k : Nat) (alpha : NNReal) (hk : 2 ≤ k) (halpha : alpha ≤ 1) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →ₗ[Real]
      BoundedHolderSpace (X := V) (F := V →L[Real] F) alpha where
  toFun f :=
    ⟨(contDiffHolderSpaceFDeriv k alpha
      ((by omega : 1 ≤ 2).trans hk) f : V → V →L[Real] F),
      ne_top_of_le_ne_top ENNReal.coe_ne_top
        (eHolderGauge_contDiffHolderSpaceFDeriv_le hk halpha f)⟩
  map_add' f g := by
    apply boundedHolderSpace_ext
    intro x
    change contDiffHolderSpaceFDeriv k alpha
      ((by omega : 1 ≤ 2).trans hk) (f + g) x = _
    rw [map_add]
    rfl
  map_smul' c f := by
    apply boundedHolderSpace_ext
    intro x
    change contDiffHolderSpaceFDeriv k alpha
      ((by omega : 1 ≤ 2).trans hk) (c • f) x = _
    rw [map_smul]
    rfl

private theorem norm_contDiffHolderSpaceFDerivHolderLinearMap_le
    {k : Nat} {alpha : NNReal} (hk : 2 ≤ k) (halpha : alpha ≤ 1)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    ‖contDiffHolderSpaceFDerivHolderLinearMap k alpha hk halpha f‖ ≤
      3 * ‖f‖ := by
  rw [norm_boundedHolderSpace_eq]
  have hreal := ENNReal.toReal_mono ENNReal.coe_ne_top
    (eHolderGauge_contDiffHolderSpaceFDeriv_le hk halpha f)
  change (eHolderGauge alpha (contDiffHolderSpaceFDeriv k alpha
    ((by omega : 1 ≤ 2).trans hk) f)).toReal ≤
      3 * (eContDiffHolderGaugeOn k alpha Set.univ (contDiffHolderSpaceFun f)).toReal
  simp only [ENNReal.coe_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, coe_nnnorm, norm_contDiffHolderSpace_eq] at hreal
  norm_num at hreal
  exact hreal

def contDiffHolderSpaceFDerivHolder
    (k : Nat) (alpha : NNReal) (hk : 2 ≤ k) (halpha : alpha ≤ 1) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedHolderSpace (X := V) (F := V →L[Real] F) alpha :=
  LinearMap.mkContinuous
    (contDiffHolderSpaceFDerivHolderLinearMap k alpha hk halpha) 3
    (norm_contDiffHolderSpaceFDerivHolderLinearMap_le hk halpha)

@[simp]
theorem contDiffHolderSpaceFDerivHolder_apply
    (k : Nat) (alpha : NNReal) (hk : 2 ≤ k) (halpha : alpha ≤ 1)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceFDerivHolder k alpha hk halpha f x =
      fderiv Real (contDiffHolderSpaceFun f) x :=
  contDiffHolderSpaceFDeriv_apply k alpha
    ((by omega : 1 ≤ 2).trans hk) f x

theorem norm_contDiffHolderSpaceFDerivHolder_le
    (k : Nat) (alpha : NNReal) (hk : 2 ≤ k) (halpha : alpha ≤ 1) :
    ‖contDiffHolderSpaceFDerivHolder
      (V := V) (F := F) k alpha hk halpha‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num)
    (norm_contDiffHolderSpaceFDerivHolderLinearMap_le hk halpha)

end EllipticBoundedContinuousFunction

section RestrictUniv

variable {X F : Type*} [MetricSpace X]
  [NormedAddCommGroup F]

theorem eHolderNorm_le_eHolderSeminormOn_univ
    {alpha : NNReal} {f : X → F}
    (hf : MemHolder alpha (Set.univ.domRestrict f)) :
    eHolderNorm alpha f ≤ eHolderSeminormOn alpha Set.univ f := by
  have hglobal : HolderWith
      (nnHolderNorm alpha (Set.univ.domRestrict f)) alpha f := by
    intro x y
    exact hf.holderWith ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩
  exact hglobal.eHolderNorm_le.trans coe_nnHolderNorm_le_eHolderNorm

end RestrictUniv

section EllipticJet

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem eHolderGauge_iteratedFDeriv_le
    {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    eHolderGauge alpha
        (iteratedFDeriv Real k (contDiffHolderSpaceFun f)) ≤
      eContDiffHolderGaugeOn k alpha Set.univ
        (contDiffHolderSpaceFun f) := by
  have hsup : eSupNormOn Set.univ
      (iteratedFDeriv Real k (contDiffHolderSpaceFun f)) ≤
      ∑ j ∈ Finset.range (k + 1),
        eSupNormOn Set.univ
          (iteratedFDeriv Real j (contDiffHolderSpaceFun f)) :=
    Finset.single_le_sum
      (fun j _ ↦ (bot_le : (0 : ENNReal) ≤ eSupNormOn Set.univ
        (iteratedFDeriv Real j (contDiffHolderSpaceFun f))))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  have hholder : eHolderNorm alpha
      (iteratedFDeriv Real k (contDiffHolderSpaceFun f)) ≤
      eHolderSeminormOn alpha Set.univ
        (iteratedFDeriv Real k (contDiffHolderSpaceFun f)) :=
    eHolderNorm_le_eHolderSeminormOn_univ f.2.1.2
  unfold eHolderGauge eContDiffHolderGaugeOn
  exact add_le_add hsup hholder

private def contDiffHolderSpaceTopJetLinearMap
    (k : Nat) (alpha : NNReal) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →ₗ[Real]
      BoundedHolderSpace (X := V) (F := V [×k]→L[Real] F) alpha where
  toFun f := ⟨iteratedFDeriv Real k (contDiffHolderSpaceFun f),
    ne_top_of_le_ne_top f.2.2 (eHolderGauge_iteratedFDeriv_le f)⟩
  map_add' f g := by
    apply boundedHolderSpace_ext
    intro x
    exact iteratedFDeriv_add_apply
      (f.2.1.1 x (Set.mem_univ x))
      (g.2.1.1 x (Set.mem_univ x))
  map_smul' c f := by
    apply boundedHolderSpace_ext
    intro x
    exact iteratedFDeriv_const_smul_apply
      (f.2.1.1 x (Set.mem_univ x))

private theorem norm_contDiffHolderSpaceTopJetLinearMap_le
    {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    ‖contDiffHolderSpaceTopJetLinearMap k alpha f‖ ≤ ‖f‖ := by
  rw [norm_boundedHolderSpace_eq, norm_contDiffHolderSpace_eq]
  exact ENNReal.toReal_mono f.2.2 (eHolderGauge_iteratedFDeriv_le f)

def contDiffHolderSpaceTopJet (k : Nat) (alpha : NNReal) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedHolderSpace (X := V) (F := V [×k]→L[Real] F) alpha :=
  LinearMap.mkContinuous (contDiffHolderSpaceTopJetLinearMap k alpha) 1
    (fun f ↦ by simpa using norm_contDiffHolderSpaceTopJetLinearMap_le f)

@[simp]
theorem contDiffHolderSpaceTopJet_apply
    (k : Nat) (alpha : NNReal)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceTopJet k alpha f x =
      iteratedFDeriv Real k (contDiffHolderSpaceFun f) x :=
  rfl

theorem norm_contDiffHolderSpaceTopJet_le (k : Nat) (alpha : NNReal) :
    ‖contDiffHolderSpaceTopJet (V := V) (F := F) k alpha‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun f ↦ by simpa using norm_contDiffHolderSpaceTopJetLinearMap_le f)

def contDiffHolderSpaceHessianHolder (alpha : NNReal) :
    ContDiffHolderSpace (V := V) (F := F) 2 alpha →L[Real]
      BoundedHolderSpace (X := V) (F := V →L[Real] V →L[Real] F) alpha :=
  (boundedHolderSpaceMap alpha
    (hessianCurryEquiv V F).toContinuousLinearEquiv.toContinuousLinearMap).comp
    (contDiffHolderSpaceTopJet 2 alpha)

@[simp]
theorem contDiffHolderSpaceHessianHolder_apply
    (alpha : NNReal)
    (f : ContDiffHolderSpace (V := V) (F := F) 2 alpha) (x : V) :
    contDiffHolderSpaceHessianHolder alpha f x =
      fderiv Real (fderiv Real (contDiffHolderSpaceFun f)) x := by
  simp only [contDiffHolderSpaceHessianHolder,
    ContinuousLinearMap.comp_apply, boundedHolderSpaceMap_apply,
    contDiffHolderSpaceTopJet_apply]
  exact hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv _ _

end EllipticJet

section ParabolicJet

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem eHolderGauge_parabolicSpatialHessian_le
    {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    eHolderGauge alpha
        (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) ≤
      eParabolicC2HolderGaugeOn alpha Set.univ
        (parabolicC2HolderSpaceFun u) := by
  have hsup : eSupNormOn Set.univ
      (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) ≤
      ∑ j ∈ Finset.range 3,
        eSupNormOn Set.univ
          (parabolicSpatialJet j (parabolicC2HolderSpaceFun u)) :=
    Finset.single_le_sum
      (fun j _ ↦ (bot_le : (0 : ENNReal) ≤ eSupNormOn Set.univ
        (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))))
      (Finset.mem_range.mpr (show 2 < 3 by norm_num))
  have hholder : eHolderNorm alpha
      (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) ≤
      eHolderSeminormOn alpha Set.univ
        (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) :=
    eHolderNorm_le_eHolderSeminormOn_univ u.2.1.2.1
  unfold eHolderGauge
  calc
    eSupNormOn Set.univ
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) +
        eHolderNorm alpha
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) ≤
      eSupNormOn Set.univ
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) +
        eHolderSeminormOn alpha Set.univ
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) :=
      add_le_add le_rfl hholder
    _ ≤ (∑ j ∈ Finset.range 3,
          eSupNormOn Set.univ
            (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
        eHolderSeminormOn alpha Set.univ
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) :=
      add_le_add hsup le_rfl
    _ ≤ eParabolicC2HolderGaugeOn alpha Set.univ
        (parabolicC2HolderSpaceFun u) := by
      unfold eParabolicC2HolderGaugeOn
      calc
        (∑ j ∈ Finset.range 3,
              eSupNormOn Set.univ
                (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
            eHolderSeminormOn alpha Set.univ
              (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) ≤
          ((∑ j ∈ Finset.range 3,
              eSupNormOn Set.univ
                (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
            eHolderSeminormOn alpha Set.univ
              (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u))) +
            (eSupNormOn Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u))) :=
          le_add_right le_rfl
        _ = (∑ j ∈ Finset.range 3,
              eSupNormOn Set.univ
                (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
            eSupNormOn Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) := by
          abel

theorem eHolderGauge_parabolicTimeDerivative_le
    {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    eHolderGauge alpha
        (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) ≤
      eParabolicC2HolderGaugeOn alpha Set.univ
        (parabolicC2HolderSpaceFun u) := by
  have hholder : eHolderNorm alpha
      (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) ≤
      eHolderSeminormOn alpha Set.univ
        (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) :=
    eHolderNorm_le_eHolderSeminormOn_univ u.2.1.2.2
  unfold eHolderGauge
  calc
    eSupNormOn Set.univ
          (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
        eHolderNorm alpha
          (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) ≤
      eSupNormOn Set.univ
          (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
        eHolderSeminormOn alpha Set.univ
          (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) :=
      add_le_add le_rfl hholder
    _ ≤ eParabolicC2HolderGaugeOn alpha Set.univ
        (parabolicC2HolderSpaceFun u) := by
      unfold eParabolicC2HolderGaugeOn
      calc
        eSupNormOn Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) ≤
          ((∑ j ∈ Finset.range 3,
              eSupNormOn Set.univ
                (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
            eHolderSeminormOn alpha Set.univ
              (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u))) +
            (eSupNormOn Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u))) :=
          le_add_left le_rfl
        _ = (∑ j ∈ Finset.range 3,
              eSupNormOn Set.univ
                (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
            eSupNormOn Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) := by
          abel

private def parabolicC2HolderSpaceSpatialHessianLinearMap
    (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →ₗ[Real]
      ParabolicHolderSpace (V := V) (F := V [×2]→L[Real] F) alpha where
  toFun u := ⟨parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u),
    ne_top_of_le_ne_top u.2.2
      (eHolderGauge_parabolicSpatialHessian_le u)⟩
  map_add' u v := by
    apply boundedHolderSpace_ext
    intro p
    exact parabolicSpatialJet_add 2 _ _ p
      (u.2.1.1.1 p (Set.mem_univ p))
      (v.2.1.1.1 p (Set.mem_univ p))
  map_smul' c u := by
    apply boundedHolderSpace_ext
    intro p
    exact parabolicSpatialJet_const_smul 2 _ p c
      (u.2.1.1.1 p (Set.mem_univ p))

private theorem norm_parabolicC2HolderSpaceSpatialHessianLinearMap_le
    {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    ‖parabolicC2HolderSpaceSpatialHessianLinearMap alpha u‖ ≤ ‖u‖ := by
  rw [norm_boundedHolderSpace_eq, norm_parabolicC2HolderSpace_eq]
  exact ENNReal.toReal_mono u.2.2
    (eHolderGauge_parabolicSpatialHessian_le u)

def parabolicC2HolderSpaceSpatialHessian (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := V) (F := V [×2]→L[Real] F) alpha :=
  LinearMap.mkContinuous
    (parabolicC2HolderSpaceSpatialHessianLinearMap alpha) 1
    (fun u ↦ by simpa using
      norm_parabolicC2HolderSpaceSpatialHessianLinearMap_le u)

@[simp]
theorem parabolicC2HolderSpaceSpatialHessian_apply
    (alpha : NNReal)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (p : ParabolicPoint V) :
    parabolicC2HolderSpaceSpatialHessian alpha u p =
      parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u) p :=
  rfl

theorem norm_parabolicC2HolderSpaceSpatialHessian_le (alpha : NNReal) :
    ‖parabolicC2HolderSpaceSpatialHessian (V := V) (F := F) alpha‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun u ↦ by simpa using
      norm_parabolicC2HolderSpaceSpatialHessianLinearMap_le u)

private def parabolicC2HolderSpaceTimeDerivativeLinearMap
    (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →ₗ[Real]
      ParabolicHolderSpace (V := V) (F := F) alpha where
  toFun u := ⟨parabolicTimeDerivative (parabolicC2HolderSpaceFun u),
    ne_top_of_le_ne_top u.2.2
      (eHolderGauge_parabolicTimeDerivative_le u)⟩
  map_add' u v := by
    apply boundedHolderSpace_ext
    intro p
    exact parabolicTimeDerivative_add _ _ p
      (u.2.1.1.2 p (Set.mem_univ p))
      (v.2.1.1.2 p (Set.mem_univ p))
  map_smul' c u := by
    apply boundedHolderSpace_ext
    intro p
    exact parabolicTimeDerivative_const_smul _ p c
      (u.2.1.1.2 p (Set.mem_univ p))

private theorem norm_parabolicC2HolderSpaceTimeDerivativeLinearMap_le
    {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    ‖parabolicC2HolderSpaceTimeDerivativeLinearMap alpha u‖ ≤ ‖u‖ := by
  rw [norm_boundedHolderSpace_eq, norm_parabolicC2HolderSpace_eq]
  exact ENNReal.toReal_mono u.2.2
    (eHolderGauge_parabolicTimeDerivative_le u)

def parabolicC2HolderSpaceTimeDerivative (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := V) (F := F) alpha :=
  LinearMap.mkContinuous
    (parabolicC2HolderSpaceTimeDerivativeLinearMap alpha) 1
    (fun u ↦ by simpa using
      norm_parabolicC2HolderSpaceTimeDerivativeLinearMap_le u)

@[simp]
theorem parabolicC2HolderSpaceTimeDerivative_apply
    (alpha : NNReal)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (p : ParabolicPoint V) :
    parabolicC2HolderSpaceTimeDerivative alpha u p =
      parabolicTimeDerivative (parabolicC2HolderSpaceFun u) p :=
  rfl

theorem norm_parabolicC2HolderSpaceTimeDerivative_le (alpha : NNReal) :
    ‖parabolicC2HolderSpaceTimeDerivative (V := V) (F := F) alpha‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun u ↦ by simpa using
      norm_parabolicC2HolderSpaceTimeDerivativeLinearMap_le u)

theorem eHolderGauge_parabolicC2HolderSpaceValue_le
    {alpha : NNReal} (halpha : alpha ≤ 1)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    eHolderGauge alpha
        (fun p : ParabolicPoint V ↦ u p.time p.space) ≤
      ((3 * ‖u‖₊ : NNReal) : ENNReal) := by
  have hgauge : eParabolicC2HolderGaugeOn alpha Set.univ
      (parabolicC2HolderSpaceFun u) ≤ (‖u‖₊ : ENNReal) := by
    rw [eParabolicC2HolderGaugeOn_eq_ofReal_norm]
    simp only [ofReal_norm, enorm_eq_nnnorm]
    exact le_rfl
  have hsup : eSupNormOn Set.univ
      (fun p : ParabolicPoint V ↦ u p.time p.space) ≤
      (‖u‖₊ : ENNReal) := by
    rw [eSupNormOn_le]
    intro p _hp
    rw [ENNReal.ofReal_le_coe]
    have hzero := parabolicSpatialJet_norm_le hgauge
      (j := 0) (by omega) (p := p) (Set.mem_univ _)
    simpa only [parabolicSpatialJet, norm_iteratedFDeriv_zero] using hzero
  have hholder := parabolicValue_holderWith halpha u.2.1.1 hgauge
  unfold eHolderGauge
  calc
    eSupNormOn Set.univ (fun p : ParabolicPoint V ↦ u p.time p.space) +
        eHolderNorm alpha (fun p : ParabolicPoint V ↦ u p.time p.space) ≤
      (‖u‖₊ : ENNReal) + (2 * ‖u‖₊ : NNReal) :=
        add_le_add hsup hholder.eHolderNorm_le
    _ = ((3 * ‖u‖₊ : NNReal) : ENNReal) := by
      push_cast
      ring

private def parabolicC2HolderSpaceValueLinearMap
    (alpha : NNReal) (halpha : alpha ≤ 1) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →ₗ[Real]
      ParabolicHolderSpace (V := V) (F := F) alpha where
  toFun u := ⟨fun p ↦ u p.time p.space,
    ne_top_of_le_ne_top ENNReal.coe_ne_top
      (eHolderGauge_parabolicC2HolderSpaceValue_le halpha u)⟩
  map_add' u v := by
    apply boundedHolderSpace_ext
    intro p
    exact parabolicC2HolderSpace_add_apply u v p.time p.space
  map_smul' c u := by
    apply boundedHolderSpace_ext
    intro p
    rfl

private theorem norm_parabolicC2HolderSpaceValueLinearMap_le
    {alpha : NNReal} (halpha : alpha ≤ 1)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    ‖parabolicC2HolderSpaceValueLinearMap alpha halpha u‖ ≤ 3 * ‖u‖ := by
  rw [norm_boundedHolderSpace_eq, norm_parabolicC2HolderSpace_eq]
  have hreal := ENNReal.toReal_mono ENNReal.coe_ne_top
    (eHolderGauge_parabolicC2HolderSpaceValue_le halpha u)
  simp only [ENNReal.coe_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, coe_nnnorm, norm_parabolicC2HolderSpace_eq] at hreal
  norm_num at hreal
  exact hreal

def parabolicC2HolderSpaceValue
    (alpha : NNReal) (halpha : alpha ≤ 1) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := V) (F := F) alpha :=
  LinearMap.mkContinuous
    (parabolicC2HolderSpaceValueLinearMap alpha halpha) 3
    (norm_parabolicC2HolderSpaceValueLinearMap_le halpha)

@[simp]
theorem parabolicC2HolderSpaceValue_apply
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (p : ParabolicPoint V) :
    parabolicC2HolderSpaceValue alpha halpha u p = u p.time p.space :=
  rfl

theorem norm_parabolicC2HolderSpaceValue_le
    (alpha : NNReal) (halpha : alpha ≤ 1) :
    ‖parabolicC2HolderSpaceValue (V := V) (F := F) alpha halpha‖ ≤ 3 := by
  exact LinearMap.mkContinuous_norm_le _ (by norm_num)
    (norm_parabolicC2HolderSpaceValueLinearMap_le halpha)

theorem eHolderGauge_parabolicSpatialJet_one_le
    {alpha : NNReal} (halpha : alpha ≤ 1)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    eHolderGauge alpha
        (parabolicSpatialJet 1 (parabolicC2HolderSpaceFun u)) ≤
      ((6 * ‖u‖₊ : NNReal) : ENNReal) := by
  have hgauge : eParabolicC2HolderGaugeOn alpha Set.univ
      (parabolicC2HolderSpaceFun u) ≤ (‖u‖₊ : ENNReal) := by
    rw [eParabolicC2HolderGaugeOn_eq_ofReal_norm]
    simp only [ofReal_norm, enorm_eq_nnnorm]
    exact le_rfl
  have hsup : eSupNormOn Set.univ
      (parabolicSpatialJet 1 (parabolicC2HolderSpaceFun u)) ≤
      (‖u‖₊ : ENNReal) := by
    rw [eSupNormOn_le]
    intro p _hp
    rw [ENNReal.ofReal_le_coe]
    exact parabolicSpatialJet_norm_le hgauge (by omega) (Set.mem_univ _)
  have hholder := parabolicSpatialJet_one_holderWith halpha u.2.1.1 hgauge
  unfold eHolderGauge
  calc
    eSupNormOn Set.univ
          (parabolicSpatialJet 1 (parabolicC2HolderSpaceFun u)) +
        eHolderNorm alpha
          (parabolicSpatialJet 1 (parabolicC2HolderSpaceFun u)) ≤
      (‖u‖₊ : ENNReal) + (5 * ‖u‖₊ : NNReal) :=
        add_le_add hsup hholder.eHolderNorm_le
    _ = ((6 * ‖u‖₊ : NNReal) : ENNReal) := by
      push_cast
      ring

private def parabolicC2HolderSpaceSpatialJetOneLinearMap
    (alpha : NNReal) (halpha : alpha ≤ 1) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →ₗ[Real]
      ParabolicHolderSpace (V := V) (F := V [×1]→L[Real] F) alpha where
  toFun u := ⟨parabolicSpatialJet 1 (parabolicC2HolderSpaceFun u),
    ne_top_of_le_ne_top ENNReal.coe_ne_top
      (eHolderGauge_parabolicSpatialJet_one_le halpha u)⟩
  map_add' u v := by
    apply boundedHolderSpace_ext
    intro p
    exact parabolicSpatialJet_add 1 _ _ p
      (u.2.1.1.1 p (Set.mem_univ p) |>.of_le (by norm_num))
      (v.2.1.1.1 p (Set.mem_univ p) |>.of_le (by norm_num))
  map_smul' c u := by
    apply boundedHolderSpace_ext
    intro p
    exact parabolicSpatialJet_const_smul 1 _ p c
      (u.2.1.1.1 p (Set.mem_univ p) |>.of_le (by norm_num))

private theorem norm_parabolicC2HolderSpaceSpatialJetOneLinearMap_le
    {alpha : NNReal} (halpha : alpha ≤ 1)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    ‖parabolicC2HolderSpaceSpatialJetOneLinearMap alpha halpha u‖ ≤
      6 * ‖u‖ := by
  change (eHolderGauge alpha
    (parabolicSpatialJet 1 (parabolicC2HolderSpaceFun u))).toReal ≤
      6 * (eParabolicC2HolderGaugeOn alpha Set.univ
        (parabolicC2HolderSpaceFun u)).toReal
  have hreal := ENNReal.toReal_mono ENNReal.coe_ne_top
    (eHolderGauge_parabolicSpatialJet_one_le halpha u)
  simp only [ENNReal.coe_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, coe_nnnorm, norm_parabolicC2HolderSpace_eq] at hreal
  norm_num at hreal
  exact hreal

private def parabolicC2HolderSpaceSpatialJetOne
    (alpha : NNReal) (halpha : alpha ≤ 1) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := V) (F := V [×1]→L[Real] F) alpha :=
  LinearMap.mkContinuous
    (parabolicC2HolderSpaceSpatialJetOneLinearMap alpha halpha) 6
    (norm_parabolicC2HolderSpaceSpatialJetOneLinearMap_le halpha)

def parabolicC2HolderSpaceSpatialGradient
    (alpha : NNReal) (halpha : alpha ≤ 1) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := V) (F := V →L[Real] F) alpha :=
  (boundedHolderSpaceMap alpha
    (continuousMultilinearCurryFin1 Real V F).toLinearIsometry.toContinuousLinearMap).comp
    (parabolicC2HolderSpaceSpatialJetOne alpha halpha)

@[simp]
theorem parabolicC2HolderSpaceSpatialGradient_apply
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (p : ParabolicPoint V) :
    parabolicC2HolderSpaceSpatialGradient alpha halpha u p =
      fderiv Real (parabolicC2HolderSpaceFun u p.time) p.space := by
  apply ContinuousLinearMap.ext
  intro v
  change continuousMultilinearCurryFin1 Real V F
      (parabolicSpatialJet 1 (parabolicC2HolderSpaceFun u) p) v = _
  rw [← parabolicPoint_time_space p]
  simp only [parabolicSpatialJet, parabolicPoint_time,
    parabolicPoint_space, continuousMultilinearCurryFin1_apply,
    iteratedFDeriv_one_apply, Fin.snoc_zero]

theorem norm_parabolicC2HolderSpaceSpatialGradient_le
    (alpha : NNReal) (halpha : alpha ≤ 1) :
    ‖parabolicC2HolderSpaceSpatialGradient
      (V := V) (F := F) alpha halpha‖ ≤ 6 := by
  let L :=
    (continuousMultilinearCurryFin1 Real V F).toLinearIsometry.toContinuousLinearMap
  have hjet :
      ‖parabolicC2HolderSpaceSpatialJetOne (V := V) (F := F) alpha halpha‖ ≤ 6 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (fun u => norm_parabolicC2HolderSpaceSpatialJetOneLinearMap_le halpha u)
  calc
    ‖parabolicC2HolderSpaceSpatialGradient
        (V := V) (F := F) alpha halpha‖ ≤
      ‖boundedHolderSpaceMap alpha L‖ *
        ‖parabolicC2HolderSpaceSpatialJetOne
          (V := V) (F := F) alpha halpha‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 6 := mul_le_mul
      ((norm_boundedHolderSpaceMap_le alpha L).trans
        (continuousMultilinearCurryFin1 Real V F).toLinearIsometry.norm_toContinuousLinearMap_le)
      hjet
      (norm_nonneg _) zero_le_one
    _ = 6 := by norm_num

end ParabolicJet

end CalabiYau.Schauder
