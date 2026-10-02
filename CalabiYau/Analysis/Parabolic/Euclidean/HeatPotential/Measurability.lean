-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatPotential/Measurability.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatPotential.TimeRealization

@[expose] public section

-- and its private helpers occur in public declarations.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Real Set
open scoped Interval NNReal RealInnerProductSpace Topology

namespace HeatEquation

open CalabiYau.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

omit [Nontrivial V] [CompleteSpace F] in
private theorem integral_time_aestronglyMeasurable_of_continuousOn
    {t : Real} {G : Real × V → F}
    (hG : ContinuousOn G (Ioo (0 : Real) t ×ˢ (Set.univ : Set V))) :
    AEStronglyMeasurable (fun s : Real => ∫ y : V, G (s, y))
      (volume.restrict (Ioc (0 : Real) t)) := by
  let A : Set (Real × V) := Ioo (0 : Real) t ×ˢ (Set.univ : Set V)
  have hGA : AEStronglyMeasurable G
      ((volume.prod (volume : Measure V)).restrict A) :=
    hG.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
  have hind : AEStronglyMeasurable (A.indicator G)
      (volume.prod (volume : Measure V)) :=
    (aestronglyMeasurable_indicator_iff
      (measurableSet_Ioo.prod MeasurableSet.univ)).mpr hGA
  have hint := hind.integral_prod_right'
  have heq : (fun s : Real => ∫ y : V, A.indicator G (s, y)) =
      (Ioo (0 : Real) t).indicator (fun s : Real => ∫ y : V, G (s, y)) := by
    funext s
    by_cases hs : s ∈ Ioo (0 : Real) t
    · simp [A, hs]
    · simp [A, hs]
  rw [heq] at hint
  have hIoo : AEStronglyMeasurable (fun s : Real => ∫ y : V, G (s, y))
      (volume.restrict (Ioo (0 : Real) t)) :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioo).mp hint
  rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hIoo

omit [Nontrivial V] [CompleteSpace F] in
theorem heatSup_timeSource_aestronglyMeasurable_of_continuousOn
    {t : Real} (ht : 0 ≤ t)
    (f : Real → BoundedContinuousFunction V F)
    (hsource : ContinuousOn (fun q : Real × V => f q.1 q.2)
      (Ioo (0 : Real) t ×ˢ (Set.univ : Set V)))
    (z : V) :
    AEStronglyMeasurable (fun s : Real => heatSup (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)) := by
  rw [uIoc_of_le ht]
  let A : Set (Real × V) := Ioo (0 : Real) t ×ˢ (Set.univ : Set V)
  let G : Real × V → F := fun q =>
    heatKernel (t - q.1) q.2 • f q.1 (z - q.2)
  apply integral_time_aestronglyMeasurable_of_continuousOn (G := G)
  rw [show Ioo (0 : Real) t ×ˢ (Set.univ : Set V) = A from rfl,
    continuousOn_iff_continuous_domRestrict]
  let phi : A → A := fun q => ⟨(q.1.1, z - q.1.2), q.2.1, Set.mem_univ _⟩
  have hphi : Continuous phi := by
    unfold phi
    fun_prop
  have hf : Continuous (fun q : A => f q.1.1 (z - q.1.2)) := by
    exact (continuousOn_iff_continuous_domRestrict.mp hsource).comp hphi
  have hr : Continuous (fun q : A => heatScale (t - q.1.1)) := by
    unfold heatScale
    fun_prop
  have hr0 : ∀ q : A, heatScale (t - q.1.1) ≠ 0 := by
    intro q
    exact (heatScale_pos (sub_pos.mpr q.2.1.2)).ne'
  have hrinv : Continuous (fun q : A => (heatScale (t - q.1.1))⁻¹) :=
    hr.inv₀ hr0
  have hbase : Continuous
      (fun q : A => baseHeat ((heatScale (t - q.1.1))⁻¹ • q.1.2)) := by
    unfold baseHeat baseHeatMass
    fun_prop
  unfold G heatKernel
  exact (((hr.pow _).inv₀ (fun q => pow_ne_zero _ (hr0 q))).mul hbase).smul hf

omit [Nontrivial V] [CompleteSpace F] in
theorem heatSup_timeSource_aestronglyMeasurable_of_parabolic_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha)
    {S t : Real} (ht : t ∈ Ioc (0 : Real) S)
    (f : Real → BoundedContinuousFunction V F)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (z : V) :
    AEStronglyMeasurable (fun s : Real => heatSup (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)) := by
  apply heatSup_timeSource_aestronglyMeasurable_of_continuousOn ht.1.le f ?_ z
  rw [continuousOn_iff_continuous_domRestrict]
  let A : Set (Real × V) := Ioo (0 : Real) t ×ˢ (Set.univ : Set V)
  let phi : A → parabolicCylinder (Icc (0 : Real) S) Set.univ := fun q =>
    ⟨parabolicPoint q.1.1 q.1.2,
      ⟨⟨q.2.1.1.le, q.2.1.2.le.trans ht.2⟩, Set.mem_univ _⟩⟩
  have hphi : Continuous phi := by
    unfold phi parabolicPoint
    fun_prop
  exact ((hsource.continuous halpha0).comp hphi).congr fun _ => rfl

omit [Nontrivial V] [CompleteSpace F] in
theorem heatSupGradient_timeSource_aestronglyMeasurable_of_continuousOn
    {t : Real} (ht : 0 ≤ t)
    (f : Real → BoundedContinuousFunction V F)
    (hsource : ContinuousOn (fun q : Real × V => f q.1 q.2)
      (Ioo (0 : Real) t ×ˢ (Set.univ : Set V)))
    (z : V) :
    AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)) := by
  rw [uIoc_of_le ht]
  let A : Set (Real × V) := Ioo (0 : Real) t ×ˢ (Set.univ : Set V)
  let G : Real × V → V →L[Real] F := fun q =>
    (heatD1Map (t - q.1) (z - q.2)).smulRight (f q.1 q.2)
  apply integral_time_aestronglyMeasurable_of_continuousOn (G := G)
  rw [show Ioo (0 : Real) t ×ˢ (Set.univ : Set V) = A from rfl,
    continuousOn_iff_continuous_domRestrict]
  have hf : Continuous (fun q : A => f q.1.1 q.1.2) :=
    continuousOn_iff_continuous_domRestrict.mp hsource
  have hr : Continuous (fun q : A => heatScale (t - q.1.1)) := by
    unfold heatScale
    fun_prop
  have hr0 : ∀ q : A, heatScale (t - q.1.1) ≠ 0 := by
    intro q
    exact (heatScale_pos (sub_pos.mpr q.2.1.2)).ne'
  have hrinv : Continuous (fun q : A => (heatScale (t - q.1.1))⁻¹) :=
    hr.inv₀ hr0
  have hcoef : Continuous (fun q : A =>
      ((heatScale (t - q.1.1)) ^ Module.finrank Real V)⁻¹ *
        (heatScale (t - q.1.1))⁻¹) :=
    ((hr.pow _).inv₀ (fun q => pow_ne_zero _ (hr0 q))).mul hrinv
  have hbase : Continuous (fun q : A =>
      baseD1Map ((heatScale (t - q.1.1))⁻¹ • (z - q.1.2))) := by
    unfold baseD1Map baseHeat baseHeatMass
    fun_prop
  have hmap : Continuous (fun q : A =>
      (((heatScale (t - q.1.1)) ^ Module.finrank Real V)⁻¹ *
        (heatScale (t - q.1.1))⁻¹) •
          baseD1Map ((heatScale (t - q.1.1))⁻¹ • (z - q.1.2))) :=
    hcoef.smul hbase
  unfold G heatD1Map
  exact (ContinuousLinearMap.smulRightL Real V F).continuous₂.comp₂ hmap hf

omit [Nontrivial V] [CompleteSpace F] in
theorem heatSupGradient_timeSource_aestronglyMeasurable_of_parabolic_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha)
    {S t : Real} (ht : t ∈ Ioc (0 : Real) S)
    (f : Real → BoundedContinuousFunction V F)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (z : V) :
    AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)) := by
  apply heatSupGradient_timeSource_aestronglyMeasurable_of_continuousOn ht.1.le f ?_ z
  rw [continuousOn_iff_continuous_domRestrict]
  let A : Set (Real × V) := Ioo (0 : Real) t ×ˢ (Set.univ : Set V)
  let phi : A → parabolicCylinder (Icc (0 : Real) S) Set.univ := fun q =>
    ⟨parabolicPoint q.1.1 q.1.2,
      ⟨⟨q.2.1.1.le, q.2.1.2.le.trans ht.2⟩, Set.mem_univ _⟩⟩
  have hphi : Continuous phi := by
    unfold phi parabolicPoint
    fun_prop
  exact ((hsource.continuous halpha0).comp hphi).congr fun _ => rfl

omit [Nontrivial V] [CompleteSpace F] in
theorem heatSupHessian_timeSource_aestronglyMeasurable_of_parabolic_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha)
    {S t : Real} (ht : t ∈ Ioc (0 : Real) S)
    (f : Real → BoundedContinuousFunction V F)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (z : V) :
    AEStronglyMeasurable
      (fun s : Real => heatSupHessian (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)) := by
  rw [uIoc_of_le ht.1.le]
  let A : Set (Real × V) := Ioo (0 : Real) t ×ˢ (Set.univ : Set V)
  let G : Real × V → V →L[Real] (V →L[Real] F) := fun q =>
    heatD2SmulRightMap (t - q.1) (z - q.2) (f q.1 q.2)
  apply integral_time_aestronglyMeasurable_of_continuousOn (G := G)
  rw [show Ioo (0 : Real) t ×ˢ (Set.univ : Set V) = A from rfl,
    continuousOn_iff_continuous_domRestrict]
  let phi : A → parabolicCylinder (Icc (0 : Real) S) Set.univ := fun q =>
    ⟨parabolicPoint q.1.1 q.1.2,
      ⟨⟨q.2.1.1.le, q.2.1.2.le.trans ht.2⟩, Set.mem_univ _⟩⟩
  have hphi : Continuous phi := by
    unfold phi parabolicPoint
    fun_prop
  have hf : Continuous (fun q : A => f q.1.1 q.1.2) := by
    exact ((hsource.continuous halpha0).comp hphi).congr fun _ => rfl
  have hr : Continuous (fun q : A => heatScale (t - q.1.1)) := by
    unfold heatScale
    fun_prop
  have hr0 : ∀ q : A, heatScale (t - q.1.1) ≠ 0 := by
    intro q
    exact (heatScale_pos (sub_pos.mpr q.2.1.2)).ne'
  have hrinv : Continuous (fun q : A => (heatScale (t - q.1.1))⁻¹) :=
    hr.inv₀ hr0
  have hcoef : Continuous (fun q : A =>
      ((heatScale (t - q.1.1)) ^ Module.finrank Real V)⁻¹ *
        (heatScale (t - q.1.1))⁻¹ *
          (heatScale (t - q.1.1))⁻¹) :=
    (((hr.pow _).inv₀ (fun q => pow_ne_zero _ (hr0 q))).mul hrinv).mul hrinv
  have hbase : Continuous (fun q : A =>
      baseD2CurriedMap
        ((heatScale (t - q.1.1))⁻¹ • (z - q.1.2))) := by
    let x : A → V := fun q =>
      (heatScale (t - q.1.1))⁻¹ • (z - q.1.2)
    have hx : Continuous x := by
      unfold x
      fun_prop
    have hd : Continuous (fun q : A => innerSL Real (x q)) :=
      (innerSL Real (E := V)).toContinuousLinearMap.continuous.comp hx
    have hb : Continuous (fun q : A => baseHeat (x q)) := by
      unfold baseHeat baseHeatMass
      fun_prop
    have hright : Continuous (fun q : A =>
        ((4 : Real)⁻¹ * baseHeat (x q)) • innerSL Real (x q)) := by
      fun_prop
    have hfirst : Continuous (fun q : A =>
        (innerSL Real (x q)).smulRight
          (((4 : Real)⁻¹ * baseHeat (x q)) • innerSL Real (x q))) :=
      (ContinuousLinearMap.smulRightL Real V (V →L[Real] Real)).continuous₂.comp₂
        hd hright
    have hsecond : Continuous (fun q : A =>
        ((2 : Real)⁻¹ * baseHeat (x q)) •
          (innerSL Real (E := V)).toContinuousLinearMap) := by
      fun_prop
    unfold baseD2CurriedMap
    exact hfirst.sub hsecond
  have hmap : Continuous (fun q : A =>
      (((heatScale (t - q.1.1)) ^ Module.finrank Real V)⁻¹ *
        (heatScale (t - q.1.1))⁻¹ *
          (heatScale (t - q.1.1))⁻¹) •
            baseD2CurriedMap
              ((heatScale (t - q.1.1))⁻¹ • (z - q.1.2))) :=
    hcoef.smul hbase
  have hleft : Continuous (fun q : A =>
      (ContinuousLinearMap.smulRightL Real V F).flip (f q.1.1 q.1.2)) :=
    (ContinuousLinearMap.smulRightL Real V F).flip.continuous.comp hf
  unfold G heatD2SmulRightMap heatD2CurriedMap
  exact (ContinuousLinearMap.compL Real V (V →L[Real] Real)
    (V →L[Real] F)).continuous₂.comp₂ hleft hmap

end HeatEquation

end
