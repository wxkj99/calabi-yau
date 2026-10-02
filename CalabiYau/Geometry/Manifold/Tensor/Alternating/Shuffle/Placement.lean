-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Alternating/Shuffle/Placement.lean
-- Locally modified.
module
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.Group
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Reindexing.FiniteEquivalence

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Equiv.Perm

def TwoShuffle (k n : ℕ) := {S : Finset (Fin (k + n)) // S.card = k}

instance (k n : ℕ) : Fintype (TwoShuffle k n) :=
  Fintype.ofEquiv (Finset.powersetCard k (Finset.univ : Finset (Fin (k + n))))
    { toFun := fun S => ⟨S, (Finset.mem_powersetCard.mp S.2).2⟩
      invFun := fun S => ⟨S.1, Finset.mem_powersetCard.mpr ⟨by simp, S.2⟩⟩
      left_inv := by intro S; rfl
      right_inv := by intro S; rfl }

namespace TwoShuffle

variable {k n : ℕ}

private theorem card_compl (S : Finset (Fin (k + n))) (hS : S.card = k) :
    (Sᶜ : Finset (Fin (k + n))).card = n := by
  rw [Finset.card_compl, hS, Fintype.card_fin]
  omega

def toEquiv (S : TwoShuffle k n) : Fin k ⊕ Fin n ≃ Fin (k + n) where
  toFun := fun x =>
    match x with
    | Sum.inl i => ↑(S.1.orderIsoOfFin S.2 ⟨i.val, by omega⟩)
    | Sum.inr j => ↑((S.1ᶜ : Finset (Fin (k + n))).orderIsoOfFin (card_compl S.1 S.2) ⟨j.val,
      by omega⟩)
  invFun := by
    intro x
    by_cases hx : x ∈ S.1
    · exact Sum.inl ((S.1.orderIsoOfFin S.2).symm ⟨x, hx⟩)
    · exact Sum.inr (((S.1ᶜ : Finset (Fin (k + n))).orderIsoOfFin (card_compl S.1 S.2)).symm
        ⟨x, by rw [Finset.mem_compl]; exact hx⟩)
  left_inv := by
    intro x
    cases x with
    | inl i =>
      have hmem : (S.1.orderEmbOfFin S.2) i ∈ S.1 := Finset.orderEmbOfFin_mem S.1 S.2 i
      simp only [Fin.eta, Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_mem, ↓reduceDIte,
        Sum.inl.injEq]
      exact (S.1.orderIsoOfFin S.2).symm_apply_apply i
    | inr j =>
      have hmem : (S.1ᶜ.orderEmbOfFin (card_compl S.1 S.2)) j ∉ S.1 := by
        intro hj
        have hmem' : (S.1ᶜ.orderEmbOfFin (card_compl S.1 S.2)) j ∈ S.1ᶜ := by
          exact Finset.orderEmbOfFin_mem (S.1ᶜ) (card_compl S.1 S.2) j
        simpa using (Finset.mem_compl.mp hmem') hj
      simp only [Fin.eta, Finset.coe_orderIsoOfFin_apply, ↓reduceDIte, Sum.inr.injEq, hmem]
      exact ((S.1ᶜ : Finset (Fin (k + n))).orderIsoOfFin (card_compl S.1 S.2)).symm_apply_apply j
  right_inv := by
    intro x
    by_cases hx : x ∈ S.1
    · simp [hx]
    · have hx' : x ∈ S.1ᶜ := Finset.mem_compl.mpr hx
      simp [hx]

def toPerm (S : TwoShuffle k n) : Perm (Fin k ⊕ Fin n) :=
  (S.toEquiv).trans (finSumFinEquiv.symm)

def ofPerm (σ : Perm (Fin k ⊕ Fin n)) : TwoShuffle k n :=
  ⟨Finset.univ.image (fun i : Fin k => finSumFinEquiv (σ (Sum.inl i))),
    by
      have hinj : Function.Injective (fun i : Fin k => finSumFinEquiv (σ (Sum.inl i))) := by
        intro a b h
        have hρ : σ (Sum.inl a) = σ (Sum.inl b) := finSumFinEquiv.injective h
        have hs' : σ⁻¹ (σ (Sum.inl a)) = σ⁻¹ (σ (Sum.inl b)) := congrArg (fun x => σ⁻¹ x) hρ
        rw [show σ⁻¹ (σ (Sum.inl a)) = Sum.inl a by simp,
          show σ⁻¹ (σ (Sum.inl b)) = Sum.inl b by simp] at hs'
        exact Sum.inl.inj hs'
      simpa using (Finset.card_image_of_injective (s := Finset.univ)
        (f := fun i : Fin k => finSumFinEquiv (σ (Sum.inl i))) hinj)⟩

@[simp]
theorem ofPerm_toPerm (S : TwoShuffle k n) : TwoShuffle.ofPerm (S.toPerm) = S := by
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    simp [TwoShuffle.toPerm, TwoShuffle.toEquiv]
  · intro hx
    have hx' : x ∈ Set.range (S.1.orderEmbOfFin S.2) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    rcases hx' with ⟨i, hi⟩
    refine Finset.mem_image.mpr ⟨i, by simp, ?_⟩
    rw [TwoShuffle.toPerm, TwoShuffle.toEquiv]
    change finSumFinEquiv (finSumFinEquiv.symm (S.1.orderEmbOfFin S.2 i)) = x
    rw [Equiv.apply_symm_apply]
    exact hi

private theorem mem_ofPerm_left (σ : Perm (Fin k ⊕ Fin n)) (i : Fin k) :
    finSumFinEquiv (σ (Sum.inl i)) ∈ (TwoShuffle.ofPerm σ).1 := by
  exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

@[simp]
theorem toPerm_inl (S : TwoShuffle k n) (i : Fin k) :
    finSumFinEquiv (S.toPerm (Sum.inl i)) = S.1.orderEmbOfFin S.2 i := by
  simp [TwoShuffle.toPerm, TwoShuffle.toEquiv]

@[simp]
theorem toPerm_inr (S : TwoShuffle k n) (j : Fin n) :
    finSumFinEquiv (S.toPerm (Sum.inr j)) =
      (S.1ᶜ : Finset (Fin (k + n))).orderEmbOfFin (card_compl S.1 S.2) j := by
  simp [TwoShuffle.toPerm, TwoShuffle.toEquiv]

private theorem mem_ofPerm_right {σ : Perm (Fin k ⊕ Fin n)} (S : TwoShuffle k n)
    (h : TwoShuffle.ofPerm σ = S) (j : Fin n) :
    finSumFinEquiv (σ (Sum.inr j)) ∈ S.1ᶜ := by
  rw [Finset.mem_compl]
  intro hmem
  have hS : (TwoShuffle.ofPerm σ).1 = S.1 := congrArg Subtype.val h
  have hmem' : finSumFinEquiv (σ (Sum.inr j)) ∈ (TwoShuffle.ofPerm σ).1 := by
    simpa [hS] using hmem
  rcases Finset.mem_image.mp hmem' with ⟨i, hi, hij⟩
  have hσ : σ (Sum.inr j) = σ (Sum.inl i) := finSumFinEquiv.injective hij.symm
  have h2 := congrArg (fun x : Fin k ⊕ Fin n => σ⁻¹ x) hσ
  simp at h2

private def leftIndex {σ : Perm (Fin k ⊕ Fin n)} (S : TwoShuffle k n)
    (h : TwoShuffle.ofPerm σ = S) (i : Fin k) : Fin k :=
  (S.1.orderIsoOfFin S.2).symm ⟨finSumFinEquiv (σ (Sum.inl i)),
    by
      have hmem := TwoShuffle.mem_ofPerm_left σ i
      simpa [h] using hmem⟩

private def rightIndex {σ : Perm (Fin k ⊕ Fin n)} (S : TwoShuffle k n)
    (h : TwoShuffle.ofPerm σ = S) (j : Fin n) : Fin n :=
  ((S.1ᶜ : Finset (Fin (k + n))).orderIsoOfFin (card_compl S.1 S.2)).symm
    ⟨finSumFinEquiv (σ (Sum.inr j)), TwoShuffle.mem_ofPerm_right S h j⟩

private theorem leftIndex_val {σ : Perm (Fin k ⊕ Fin n)} (S : TwoShuffle k n)
    (h : TwoShuffle.ofPerm σ = S) (i : Fin k) :
    S.1.orderEmbOfFin S.2 (leftIndex S h i) = finSumFinEquiv (σ (Sum.inl i)) := by
  have hmem : finSumFinEquiv (σ (Sum.inl i)) ∈ S.1 := by
    have hmem' := TwoShuffle.mem_ofPerm_left σ i
    simpa [h] using hmem'
  exact congrArg Subtype.val ((S.1.orderIsoOfFin S.2).apply_symm_apply
    (⟨finSumFinEquiv (σ (Sum.inl i)), hmem⟩ : S.1))

private theorem rightIndex_val {σ : Perm (Fin k ⊕ Fin n)} (S : TwoShuffle k n)
    (h : TwoShuffle.ofPerm σ = S) (j : Fin n) :
    (S.1ᶜ : Finset (Fin (k + n))).orderEmbOfFin (card_compl S.1 S.2)
      (rightIndex S h j) = finSumFinEquiv (σ (Sum.inr j)) := by
  let Sc : Finset (Fin (k + n)) := S.1ᶜ
  exact congrArg Subtype.val ((Sc.orderIsoOfFin (card_compl S.1 S.2)).apply_symm_apply
    (⟨finSumFinEquiv (σ (Sum.inr j)), TwoShuffle.mem_ofPerm_right S h j⟩ : Sc))

private theorem leftIndex_toPerm {σ : Perm (Fin k ⊕ Fin n)} (S : TwoShuffle k n)
    (h : TwoShuffle.ofPerm σ = S) (i : Fin k) :
    S.toPerm (Sum.inl (leftIndex S h i)) = σ (Sum.inl i) := by
  simp [TwoShuffle.toPerm, TwoShuffle.toEquiv, leftIndex_val S h i]

private theorem rightIndex_toPerm {σ : Perm (Fin k ⊕ Fin n)} (S : TwoShuffle k n)
    (h : TwoShuffle.ofPerm σ = S) (j : Fin n) :
    S.toPerm (Sum.inr (rightIndex S h j)) = σ (Sum.inr j) := by
  simp [TwoShuffle.toPerm, TwoShuffle.toEquiv, rightIndex_val S h j]

private theorem leftIndex_bijective {σ : Perm (Fin k ⊕ Fin n)} (S : TwoShuffle k n)
    (h : TwoShuffle.ofPerm σ = S) : Function.Bijective (leftIndex S h) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    have h1 : S.1.orderEmbOfFin S.2 (leftIndex S h a) = S.1.orderEmbOfFin S.2
      (leftIndex S h b) := by
      rw [hab]
    have h2 : finSumFinEquiv (σ (Sum.inl a)) = finSumFinEquiv (σ (Sum.inl b)) := by
      rw [← leftIndex_val S h a, ← leftIndex_val S h b, h1]
    have hσ : σ (Sum.inl a) = σ (Sum.inl b) := finSumFinEquiv.injective h2
    have hs' : σ⁻¹ (σ (Sum.inl a)) = σ⁻¹ (σ (Sum.inl b)) := congrArg (fun x => σ⁻¹ x) hσ
    rw [show σ⁻¹ (σ (Sum.inl a)) = Sum.inl a by simp,
      show σ⁻¹ (σ (Sum.inl b)) = Sum.inl b by simp] at hs'
    exact Sum.inl.inj hs'
  · intro x
    let y : Fin (k + n) := S.1.orderEmbOfFin S.2 x
    have hy : y ∈ S.1 := Finset.orderEmbOfFin_mem S.1 S.2 x
    have hy' : y ∈ (TwoShuffle.ofPerm σ).1 := by simpa [← h] using hy
    rcases Finset.mem_image.mp hy' with ⟨i, hi, hiy⟩
    refine ⟨i, ?_⟩
    apply (S.1.orderIsoOfFin S.2).injective
    apply Subtype.ext
    change S.1.orderEmbOfFin S.2 (leftIndex S h i) = S.1.orderEmbOfFin S.2 x
    rw [leftIndex_val S h i, hiy]

private theorem rightIndex_bijective {σ : Perm (Fin k ⊕ Fin n)} (S : TwoShuffle k n)
    (h : TwoShuffle.ofPerm σ = S) : Function.Bijective (rightIndex S h) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    have h1 : (S.1ᶜ : Finset (Fin (k + n))).orderEmbOfFin (card_compl S.1 S.2) (rightIndex S h a) =
        (S.1ᶜ : Finset (Fin (k + n))).orderEmbOfFin (card_compl S.1 S.2) (rightIndex S h b) := by
      rw [hab]
    have h2 : finSumFinEquiv (σ (Sum.inr a)) = finSumFinEquiv (σ (Sum.inr b)) := by
      rw [← rightIndex_val S h a, ← rightIndex_val S h b, h1]
    have hσ : σ (Sum.inr a) = σ (Sum.inr b) := finSumFinEquiv.injective h2
    have hs' : σ⁻¹ (σ (Sum.inr a)) = σ⁻¹ (σ (Sum.inr b)) := congrArg (fun x => σ⁻¹ x) hσ
    rw [show σ⁻¹ (σ (Sum.inr a)) = Sum.inr a by simp,
      show σ⁻¹ (σ (Sum.inr b)) = Sum.inr b by simp] at hs'
    exact Sum.inr.inj hs'
  · intro x
    let y : Fin (k + n) := (S.1ᶜ : Finset (Fin (k + n))).orderEmbOfFin (card_compl S.1 S.2) x
    have hy : y ∈ S.1ᶜ := Finset.orderEmbOfFin_mem (S.1ᶜ) (card_compl S.1 S.2) x
    have hnot : y ∉ (TwoShuffle.ofPerm σ).1 := by
      simpa [← h] using (Finset.mem_compl.mp hy)
    have hright : y ∈ Set.range (fun j : Fin n => finSumFinEquiv (σ (Sum.inr j))) := by
      let R : Finset (Fin (k + n)) :=
        Finset.univ.image (fun j : Fin n => finSumFinEquiv (σ (Sum.inr j)))
      have hRsub : R ⊆ S.1ᶜ := by
        intro z hz
        rw [Finset.mem_compl]
        intro hzs
        have hzs' : z ∈ (TwoShuffle.ofPerm σ).1 := by simpa [h] using hzs
        rcases Finset.mem_image.mp hzs' with ⟨i, hi, hiz⟩
        rcases Finset.mem_image.mp hz with ⟨j, hj, hjz⟩
        have hσ : σ (Sum.inr j) = σ (Sum.inl i) := finSumFinEquiv.injective (hjz.trans hiz.symm)
        have h2 := congrArg (fun x : Fin k ⊕ Fin n => σ⁻¹ x) hσ
        simp at h2
      have hRcard : R.card = n := by
        have hinj : Function.Injective (fun j : Fin n => finSumFinEquiv (σ (Sum.inr j))) := by
          intro a b hab
          have hσ : σ (Sum.inr a) = σ (Sum.inr b) := finSumFinEquiv.injective hab
          have hs' : σ⁻¹ (σ (Sum.inr a)) = σ⁻¹ (σ (Sum.inr b)) := congrArg (fun x => σ⁻¹ x) hσ
          rw [show σ⁻¹ (σ (Sum.inr a)) = Sum.inr a by simp,
            show σ⁻¹ (σ (Sum.inr b)) = Sum.inr b by simp] at hs'
          exact Sum.inr.inj hs'
        simpa [R] using (Finset.card_image_of_injective (s := Finset.univ)
          (f := fun j : Fin n => finSumFinEquiv (σ (Sum.inr j))) hinj)
      have hReq : R = S.1ᶜ := by
        apply Finset.eq_of_subset_of_card_le
        · exact hRsub
        · rw [hRcard]
          exact le_of_eq (card_compl S.1 S.2)
      have hyR : y ∈ R := by
        rw [hReq]
        exact hy
      rcases Finset.mem_image.mp hyR with ⟨j, hj, hjy⟩
      exact ⟨j, hjy⟩
    rcases hright with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    apply ((S.1ᶜ : Finset (Fin (k + n))).orderIsoOfFin (card_compl S.1 S.2)).injective
    apply Subtype.ext
    change (S.1ᶜ : Finset (Fin (k + n))).orderEmbOfFin (card_compl S.1 S.2) (rightIndex S h j) =
      (S.1ᶜ : Finset (Fin (k + n))).orderEmbOfFin (card_compl S.1 S.2) x
    rw [rightIndex_val S h j]
    exact hj

private theorem eq_toPerm_mul {σ : Perm (Fin k ⊕ Fin n)} (S : TwoShuffle k n)
    (h : TwoShuffle.ofPerm σ = S) :
    σ = S.toPerm * Equiv.sumCongr (Equiv.ofBijective (leftIndex S h) (leftIndex_bijective S h))
      (Equiv.ofBijective (rightIndex S h) (rightIndex_bijective S h)) := by
  ext x
  cases x with
  | inl i =>
    change σ (Sum.inl i) =
      S.toPerm (Sum.inl ((Equiv.ofBijective (leftIndex S h) (leftIndex_bijective S h)) i))
    simpa using (leftIndex_toPerm S h i).symm
  | inr j =>
    change σ (Sum.inr j) =
      S.toPerm (Sum.inr ((Equiv.ofBijective (rightIndex S h) (rightIndex_bijective S h)) j))
    simpa using (rightIndex_toPerm S h j).symm

theorem quotient_eq_of_ofPerm_eq {σ τ : Perm (Fin k ⊕ Fin n)}
    (h : TwoShuffle.ofPerm σ = TwoShuffle.ofPerm τ) :
    (Quotient.mk'' σ : ModSumCongr (Fin k) (Fin n)) = Quotient.mk'' τ := by
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  let S := TwoShuffle.ofPerm σ
  have hσ : TwoShuffle.ofPerm σ = S := rfl
  have hτ : TwoShuffle.ofPerm τ = S := by simpa [S] using h.symm
  have h_eq := TwoShuffle.eq_toPerm_mul S hσ
  have h_eq' := TwoShuffle.eq_toPerm_mul S hτ
  let ασ := Equiv.ofBijective (leftIndex S hσ) (leftIndex_bijective S hσ)
  let ατ := Equiv.ofBijective (leftIndex S hτ) (leftIndex_bijective S hτ)
  let βσ := Equiv.ofBijective (rightIndex S hσ) (rightIndex_bijective S hσ)
  let βτ := Equiv.ofBijective (rightIndex S hτ) (rightIndex_bijective S hτ)
  refine ⟨⟨ασ⁻¹ * ατ, βσ⁻¹ * βτ⟩, ?_⟩
  change Equiv.sumCongr (ασ⁻¹ * ατ) (βσ⁻¹ * βτ) = σ⁻¹ * τ
  have h_eqσ : σ = S.toPerm * Equiv.sumCongr ασ βσ := by
    change σ = S.toPerm * Equiv.sumCongr
      (Equiv.ofBijective (leftIndex S hσ) (leftIndex_bijective S hσ))
      (Equiv.ofBijective (rightIndex S hσ) (rightIndex_bijective S hσ))
    exact TwoShuffle.eq_toPerm_mul S hσ
  have h_eqτ : τ = S.toPerm * Equiv.sumCongr ατ βτ := by
    change τ = S.toPerm * Equiv.sumCongr
      (Equiv.ofBijective (leftIndex S hτ) (leftIndex_bijective S hτ))
      (Equiv.ofBijective (rightIndex S hτ) (rightIndex_bijective S hτ))
    exact TwoShuffle.eq_toPerm_mul S hτ
  rw [h_eqσ, h_eqτ]
  rw [show Equiv.sumCongr (ασ⁻¹ * ατ) (βσ⁻¹ * βτ) =
      (Equiv.sumCongr ασ βσ)⁻¹ * Equiv.sumCongr ατ βτ by
    rw [show Equiv.sumCongr (ασ⁻¹ * ατ) (βσ⁻¹ * βτ) =
        Equiv.Perm.sumCongrHom (Fin k) (Fin n) (ασ⁻¹ * ατ, βσ⁻¹ * βτ) by rfl,
      show Equiv.sumCongr ασ βσ = Equiv.Perm.sumCongrHom (Fin k) (Fin n) (ασ, βσ) by rfl,
      show Equiv.sumCongr ατ βτ = Equiv.Perm.sumCongrHom (Fin k) (Fin n) (ατ, βτ) by rfl]
    rw [show (ασ⁻¹ * ατ, βσ⁻¹ * βτ) = ((ασ, βσ)⁻¹ * (ατ, βτ)) by
      ext <;> simp]
    rw [map_mul, map_inv]]
  group

theorem ofPerm_eq_of_quotient_eq {σ τ : Perm (Fin k ⊕ Fin n)}
    (h : (Quotient.mk'' σ : ModSumCongr (Fin k) (Fin n)) = Quotient.mk'' τ) :
    TwoShuffle.ofPerm σ = TwoShuffle.ofPerm τ := by
  have h' := Quotient.exact' h
  rw [QuotientGroup.leftRel_apply] at h'
  rcases h' with ⟨⟨α, β⟩, h⟩
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hτ : ∀ j : Fin k, τ (Sum.inl j) = σ (Sum.inl (α j)) := by
      intro j
      have hj := congrArg (fun f : Perm (Fin k ⊕ Fin n) => f (Sum.inl j)) h.symm
      simp only [Equiv.Perm.mul_def] at hj
      have hj' : σ⁻¹ (τ (Sum.inl j)) = Sum.inl (α j) := by
        simpa [Equiv.sumCongr_apply] using hj
      have hs := congrArg (fun y : Fin k ⊕ Fin n => σ y) hj'
      simpa using hs
    refine Finset.mem_image.mpr ⟨α.symm i, by simp, ?_⟩
    rw [hτ (α.symm i), Equiv.apply_symm_apply]
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hτ : ∀ j : Fin k, τ (Sum.inl j) = σ (Sum.inl (α j)) := by
      intro j
      have hj := congrArg (fun f : Perm (Fin k ⊕ Fin n) => f (Sum.inl j)) h.symm
      simp only [Equiv.Perm.mul_def] at hj
      have hj' : σ⁻¹ (τ (Sum.inl j)) = Sum.inl (α j) := by
        simpa [Equiv.sumCongr_apply] using hj
      have hs := congrArg (fun y : Fin k ⊕ Fin n => σ y) hj'
      simpa using hs
    refine Finset.mem_image.mpr ⟨α i, by simp, ?_⟩
    rw [hτ i]

noncomputable def modSumCongrTwoShuffle (k n : ℕ) :
    ModSumCongr (Fin k) (Fin n) ≃ TwoShuffle k n where
  toFun q := TwoShuffle.ofPerm (Quot.out q)
  invFun S := Quotient.mk'' (S.toPerm)
  left_inv := by
    intro q
    let S := TwoShuffle.ofPerm (Quot.out q)
    change Quotient.mk'' (S.toPerm) = q
    rw [← Quotient.out_eq q]
    change Quotient.mk'' (S.toPerm) = Quotient.mk'' (Quot.out q)
    apply TwoShuffle.quotient_eq_of_ofPerm_eq
    rw [TwoShuffle.ofPerm_toPerm S]
  right_inv := by
    intro S
    let q : ModSumCongr (Fin k) (Fin n) := Quotient.mk'' (S.toPerm)
    change TwoShuffle.ofPerm (Quot.out q) = S
    have hquot : Quotient.mk'' (Quot.out q) = q := Quotient.out_eq (q := q)
    have hperm : TwoShuffle.ofPerm (Quot.out q) = TwoShuffle.ofPerm (S.toPerm) :=
      TwoShuffle.ofPerm_eq_of_quotient_eq hquot
    simpa using hperm

end TwoShuffle

@[ext]
structure ThreeShuffle (m n p : ℕ) where
  mnBlock : {S : Finset (Fin (m + n + p)) // S.card = m + n}
  mBlock : {T : Finset (Fin (m + n + p)) // T.card = m}
  mBlock_subset : mBlock.1 ⊆ mnBlock.1

namespace ThreeShuffle

variable {m n p : ℕ}

def nBlock (P : ThreeShuffle m n p) : {S : Finset (Fin (m + n + p)) // S.card = n} :=
  ⟨P.mnBlock.1 \ P.mBlock.1, by
    have hST : P.mBlock.1 ∩ P.mnBlock.1 = P.mBlock.1 := Finset.inter_eq_left.mpr P.mBlock_subset
    rw [Finset.card_sdiff, hST, P.mBlock.2, P.mnBlock.2]
    omega⟩

def pBlock (P : ThreeShuffle m n p) : {S : Finset (Fin (m + n + p)) // S.card = p} :=
  ⟨P.mnBlock.1ᶜ, by
    rw [Finset.card_compl, P.mnBlock.2, Fintype.card_fin]
    omega⟩

private theorem mBlock_compl_card (P : ThreeShuffle m n p) :
    ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).card = n + p := by
  rw [Finset.card_compl, P.mBlock.2, Fintype.card_fin]
  omega

def finAssocOrder (m n p : ℕ) : Fin (m + n + p) ≃o Fin (m + (n + p)) :=
  Fin.castOrderIso (Nat.add_assoc m n p)

theorem finAssoc_finAssocOrder (m n p : ℕ) : Fin.finAssoc = (finAssocOrder m n p).toEquiv := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  rfl

theorem finAssoc_symm_finAssocOrder (m n p : ℕ) :
    Fin.finAssoc.symm = (finAssocOrder m n p).symm.toEquiv := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  rfl

def leftOuter (P : ThreeShuffle m n p) : TwoShuffle m (n + p) :=
  ⟨P.mBlock.1.map (finAssocOrder m n p).toEmbedding, by
    rw [Finset.card_map]
    exact P.mBlock.2⟩

private theorem filter_map_image {α β : Type*} [Fintype α] [DecidableEq β]
    (e : α ↪ β) (t : Finset β) (hsub : ↑t ⊆ Set.range e) :
    (Finset.univ.filter (fun a : α => e a ∈ t)).map e = t := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨a, ha, hxa⟩
    simpa [hxa] using (Finset.mem_filter.mp ha).2
  · intro hx
    have hx' : x ∈ Set.range e := hsub hx
    rcases hx' with ⟨a, ha⟩
    refine Finset.mem_map.mpr ⟨a, ?_, ha⟩
    rw [Finset.mem_filter]
    exact ⟨by simp, by simpa [ha] using hx⟩

private theorem filter_map_image_card {α β : Type*} [Fintype α] [DecidableEq β]
    (e : α ↪ β) (t : Finset β) (hsub : ↑t ⊆ Set.range e) :
    (Finset.univ.filter (fun a : α => e a ∈ t)).card = t.card := by
  have h := filter_map_image e t hsub
  conv_rhs => rw [← h]
  exact (Finset.card_map _).symm

def leftInner (P : ThreeShuffle m n p) : TwoShuffle n p :=
  ⟨Finset.univ.filter (fun r : Fin (n + p) =>
      ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P) r ∈
        (nBlock P).1), by
    let e : Fin (n + p) ↪o Fin (m + n + p) :=
      ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P)
    have hsub : ↑((nBlock P).1 : Finset (Fin (m + n + p))) ⊆ Set.range e := by
      intro x hx
      have hxM : x ∉ P.mBlock.1 := (Finset.mem_sdiff.mp hx).2
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_compl.mpr hxM
    exact (filter_map_image_card e.toEmbedding (nBlock P).1 (by
      simpa [RelEmbedding.coe_toEmbedding] using hsub)).trans (nBlock P).2⟩

def rightOuter (P : ThreeShuffle m n p) : TwoShuffle (m + n) p :=
  ⟨P.mnBlock.1, P.mnBlock.2⟩

def rightInner (P : ThreeShuffle m n p) : TwoShuffle m n :=
  ⟨Finset.univ.filter (fun r : Fin
    (m + n) => P.mnBlock.1.orderEmbOfFin P.mnBlock.2 r ∈ P.mBlock.1), by
    let e : Fin (m + n) ↪o Fin (m + n + p) := P.mnBlock.1.orderEmbOfFin P.mnBlock.2
    have hsub : ↑(P.mBlock.1 : Finset (Fin (m + n + p))) ⊆ Set.range e := by
      intro x hx
      rw [Finset.range_orderEmbOfFin]
      exact P.mBlock_subset hx
    exact (filter_map_image_card e.toEmbedding P.mBlock.1 (by
      simpa [RelEmbedding.coe_toEmbedding] using hsub)).trans P.mBlock.2⟩

def mergeRight {m n p : ℕ} (σ : Perm (Fin (m + n) ⊕ Fin p)) (τ : Perm (Fin m ⊕ Fin n)) :
    Perm ((Fin m ⊕ Fin n) ⊕ Fin p) :=
  (Equiv.sumCongr (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
    (Equiv.refl (Fin p))).symm.permCongr σ * Equiv.sumCongr τ (Equiv.refl (Fin p))

def mergeLeft {m n p : ℕ} (σ : Perm (Fin m ⊕ Fin (n + p))) (τ : Perm (Fin n ⊕ Fin p)) :
    Perm (Fin m ⊕ (Fin n ⊕ Fin p)) :=
  (Equiv.sumCongr (Equiv.refl (Fin m)) (finSumFinEquiv : Fin n ⊕ Fin p ≃ Fin
    (n + p))).symm.permCongr
      σ * Equiv.sumCongr (Equiv.refl (Fin m)) τ

@[simp]
theorem mergeRight_inl_inl {m n p : ℕ} (σ : Perm (Fin (m + n) ⊕ Fin p))
    (τ : Perm (Fin m ⊕ Fin n)) (i : Fin m) :
    mergeRight σ τ (Sum.inl (Sum.inl i)) =
      Equiv.sumCongr (finSumFinEquiv.symm : Fin (m + n) ≃ Fin m ⊕ Fin n) (Equiv.refl (Fin p))
        (σ (Sum.inl (finSumFinEquiv (τ (Sum.inl i))))) := by
  simp [mergeRight, Equiv.Perm.mul_def, Equiv.permCongr_apply, Equiv.sumCongr_apply]

@[simp]
theorem mergeRight_inl_inr {m n p : ℕ} (σ : Perm (Fin (m + n) ⊕ Fin p))
    (τ : Perm (Fin m ⊕ Fin n)) (j : Fin n) :
    mergeRight σ τ (Sum.inl (Sum.inr j)) =
      Equiv.sumCongr (finSumFinEquiv.symm : Fin (m + n) ≃ Fin m ⊕ Fin n) (Equiv.refl (Fin p))
        (σ (Sum.inl (finSumFinEquiv (τ (Sum.inr j))))) := by
  simp [mergeRight, Equiv.Perm.mul_def, Equiv.permCongr_apply, Equiv.sumCongr_apply]

@[simp]
theorem mergeRight_inr {m n p : ℕ} (σ : Perm (Fin (m + n) ⊕ Fin p))
    (τ : Perm (Fin m ⊕ Fin n)) (k : Fin p) :
    mergeRight σ τ (Sum.inr k) =
      Equiv.sumCongr (finSumFinEquiv.symm : Fin (m + n) ≃ Fin m ⊕ Fin n) (Equiv.refl (Fin p))
        (σ (Sum.inr k)) := by
  simp [mergeRight, Equiv.Perm.mul_def, Equiv.permCongr_apply, Equiv.sumCongr_apply]

@[simp]
theorem mergeLeft_inl {m n p : ℕ} (σ : Perm (Fin m ⊕ Fin (n + p)))
    (τ : Perm (Fin n ⊕ Fin p)) (i : Fin m) :
    mergeLeft σ τ (Sum.inl i) =
      Equiv.sumCongr (Equiv.refl (Fin m)) (finSumFinEquiv.symm : Fin (n + p) ≃ Fin n ⊕ Fin p)
        (σ (Sum.inl i)) := by
  simp [mergeLeft, Equiv.Perm.mul_def, Equiv.permCongr_apply, Equiv.sumCongr_apply]

@[simp]
theorem mergeLeft_inr_inl {m n p : ℕ} (σ : Perm (Fin m ⊕ Fin (n + p)))
    (τ : Perm (Fin n ⊕ Fin p)) (j : Fin n) :
    mergeLeft σ τ (Sum.inr (Sum.inl j)) =
      Equiv.sumCongr (Equiv.refl (Fin m)) (finSumFinEquiv.symm : Fin (n + p) ≃ Fin n ⊕ Fin p)
        (σ (Sum.inr (finSumFinEquiv (τ (Sum.inl j))))) := by
  simp [mergeLeft, Equiv.Perm.mul_def, Equiv.permCongr_apply, Equiv.sumCongr_apply]

@[simp]
theorem mergeLeft_inr_inr {m n p : ℕ} (σ : Perm (Fin m ⊕ Fin (n + p)))
    (τ : Perm (Fin n ⊕ Fin p)) (k : Fin p) :
    mergeLeft σ τ (Sum.inr (Sum.inr k)) =
      Equiv.sumCongr (Equiv.refl (Fin m)) (finSumFinEquiv.symm : Fin (n + p) ≃ Fin n ⊕ Fin p)
        (σ (Sum.inr (finSumFinEquiv (τ (Sum.inr k))))) := by
  simp [mergeLeft, Equiv.Perm.mul_def, Equiv.permCongr_apply, Equiv.sumCongr_apply]

@[simp]
theorem sign_mergeRight {m n p : ℕ} (σ : Perm (Fin (m + n) ⊕ Fin p)) (τ : Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (mergeRight σ τ) = Equiv.Perm.sign σ * Equiv.Perm.sign τ := by
  simp [mergeRight, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_mul]

@[simp]
theorem sign_mergeLeft {m n p : ℕ} (σ : Perm (Fin m ⊕ Fin (n + p))) (τ : Perm (Fin n ⊕ Fin p)) :
    Equiv.Perm.sign (mergeLeft σ τ) = Equiv.Perm.sign σ * Equiv.Perm.sign τ := by
  simp [mergeLeft, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_mul]

def canonicalLeft (P : ThreeShuffle m n p) : Perm (Fin m ⊕ (Fin n ⊕ Fin p)) :=
  mergeLeft (P.leftOuter.toPerm) (P.leftInner.toPerm)

def canonicalRight (P : ThreeShuffle m n p) : Perm ((Fin m ⊕ Fin n) ⊕ Fin p) :=
  mergeRight (P.rightOuter.toPerm) (P.rightInner.toPerm)

private theorem orderEmbOfFin_map {α β : Type*} [LinearOrder α] [LinearOrder β]
    (s : Finset α) {k : ℕ} (h : s.card = k) (e : α ↪o β) (i : Fin k) :
    (s.map e.toEmbedding).orderEmbOfFin (by rw [Finset.card_map]; exact h) i = e
      (s.orderEmbOfFin h i) := by
  rw [Finset.orderEmbOfFin_apply, Finset.orderEmbOfFin_apply]
  have hs : (s.sort (· ≤ ·)).map e.toEmbedding = (s.map e.toEmbedding).sort (· ≤ ·) :=
    Finset.map_sort (s := s) (r := (· ≤ ·)) (r' := (· ≤ ·)) (f := e.toEmbedding) (by
      intro a ha b hb
      exact (e.map_rel_iff).symm)
  simp [← hs, List.getElem_map]

theorem rightInner_emb (P : ThreeShuffle m n p) (i : Fin m) :
    P.mnBlock.1.orderEmbOfFin P.mnBlock.2 ((rightInner P).1.orderEmbOfFin (rightInner P).2 i) =
      P.mBlock.1.orderEmbOfFin P.mBlock.2 i := by
  let e : Fin (m + n) ↪o Fin (m + n + p) := P.mnBlock.1.orderEmbOfFin P.mnBlock.2
  have hsub : ↑(P.mBlock.1 : Finset (Fin (m + n + p))) ⊆ Set.range e := by
    intro x hx
    rw [Finset.range_orderEmbOfFin]
    exact P.mBlock_subset hx
  have himg : (Finset.univ.filter (fun r : Fin (m + n) => e r ∈ P.mBlock.1)).map e.toEmbedding =
      P.mBlock.1 :=
    filter_map_image e.toEmbedding P.mBlock.1 (by
      simpa [RelEmbedding.coe_toEmbedding] using hsub)
  have hmap := orderEmbOfFin_map (Finset.univ.filter (fun r : Fin (m + n) => e r ∈ P.mBlock.1))
    (rightInner P).2 e i
  simp [himg] at hmap
  simpa [rightInner] using hmap.symm

theorem leftInner_emb (P : ThreeShuffle m n p) (j : Fin n) :
    ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P)
        ((leftInner P).1.orderEmbOfFin (leftInner P).2 j) =
      (nBlock P).1.orderEmbOfFin (nBlock P).2 j := by
  let e : Fin (n + p) ↪o Fin (m + n + p) :=
    ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P)
  have hsub : ↑((nBlock P).1 : Finset (Fin (m + n + p))) ⊆ Set.range e := by
    intro x hx
    have hxM : x ∉ P.mBlock.1 := (Finset.mem_sdiff.mp hx).2
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_compl.mpr hxM
  have himg : (Finset.univ.filter (fun r : Fin (n + p) => e r ∈ (nBlock P).1)).map e.toEmbedding =
      (nBlock P).1 :=
    filter_map_image e.toEmbedding (nBlock P).1 (by
      simpa [RelEmbedding.coe_toEmbedding] using hsub)
  have hmap := orderEmbOfFin_map (Finset.univ.filter (fun r : Fin (n + p) => e r ∈ (nBlock P).1))
    (leftInner P).2 e j
  simp [himg] at hmap
  simpa [leftInner] using hmap.symm

theorem leftOuter_emb (P : ThreeShuffle m n p) (i : Fin m) :
    (finAssocOrder m n p).symm ((leftOuter P).1.orderEmbOfFin (leftOuter P).2 i) =
      P.mBlock.1.orderEmbOfFin P.mBlock.2 i := by
  have hmap := orderEmbOfFin_map P.mBlock.1 P.mBlock.2 (finAssocOrder m n p).toOrderEmbedding i
  change (finAssocOrder m n p).symm ((P.mBlock.1.map
    (finAssocOrder m n p).toOrderEmbedding.toEmbedding).orderEmbOfFin
    (by rw [Finset.card_map]; exact P.mBlock.2) i) = P.mBlock.1.orderEmbOfFin P.mBlock.2 i
  rw [hmap]
  simp

theorem leftOuter_compl_emb (P : ThreeShuffle m n p) (t : Fin (n + p)) :
    (finAssocOrder m n p).symm (((leftOuter P).1ᶜ : Finset (Fin (m + (n + p)))).orderEmbOfFin
        (by
          rw [show (leftOuter P).1 = P.mBlock.1.map (finAssocOrder m n p).toEmbedding from rfl]
          rw [Finset.card_compl, Finset.card_map, P.mBlock.2, Fintype.card_fin]
          omega) t) =
      ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P) t := by
  have himg : ((leftOuter P).1ᶜ : Finset (Fin (m + (n + p)))).map
      (finAssocOrder m n p).symm.toEmbedding = (P.mBlock.1ᶜ : Finset (Fin (m + n + p))) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
      rw [Finset.mem_compl]
      intro hxM
      have : a ∈ (leftOuter P).1 := by
        dsimp [leftOuter]
        refine Finset.mem_map.mpr ⟨(finAssocOrder m n p).symm a, ?_, ?_⟩
        · simpa using hxM
        · rfl
      exact (Finset.mem_compl.mp ha) this
    · intro hx
      rw [Finset.mem_compl] at hx
      refine Finset.mem_map.mpr ⟨(finAssocOrder m n p) x, ?_, ?_⟩
      · rw [Finset.mem_compl]
        intro hxL
        dsimp [leftOuter] at hxL
        rcases Finset.mem_map.mp hxL with ⟨x', hx', hx''⟩
        have hxx : x' = x := (finAssocOrder m n p).toEmbedding.injective (by simpa using hx'')
        exact hx (by simpa [hxx] using hx')
      · simp
  have hmap := orderEmbOfFin_map ((leftOuter P).1ᶜ : Finset (Fin (m + (n + p))))
    (by
      rw [show (leftOuter P).1 = P.mBlock.1.map (finAssocOrder m n p).toEmbedding from rfl]
      rw [Finset.card_compl, Finset.card_map, P.mBlock.2, Fintype.card_fin]
      omega)
    (finAssocOrder m n p).symm.toOrderEmbedding t
  change (finAssocOrder m n p).symm.toOrderEmbedding (((leftOuter P).1ᶜ : Finset (Fin (m +
    (n + p)))).orderEmbOfFin
    (by
      rw [show (leftOuter P).1 = P.mBlock.1.map (finAssocOrder m n p).toEmbedding from rfl]
      rw [Finset.card_compl, Finset.card_map, P.mBlock.2, Fintype.card_fin]
      omega) t) =
    ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P) t
  rw [← hmap]
  change (((leftOuter P).1ᶜ : Finset (Fin (m + (n + p)))).map
    (finAssocOrder m n p).symm.toEmbedding).orderEmbOfFin (by
      rw [show (leftOuter P).1 = P.mBlock.1.map (finAssocOrder m n p).toEmbedding from rfl]
      rw [Finset.card_map, Finset.card_compl, Finset.card_map, P.mBlock.2, Fintype.card_fin]
      omega) t =
    ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P) t
  have hu := Finset.orderEmbOfFin_unique' (mBlock_compl_card P) (f :=
    (((leftOuter P).1ᶜ : Finset (Fin (m + (n + p)))).map
      (finAssocOrder m n p).symm.toEmbedding).orderEmbOfFin (by
        rw [show (leftOuter P).1 = P.mBlock.1.map (finAssocOrder m n p).toEmbedding from rfl]
        rw [Finset.card_map, Finset.card_compl, Finset.card_map, P.mBlock.2, Fintype.card_fin]
        omega)) (by
      intro x
      rw [← himg]
      exact Finset.orderEmbOfFin_mem _ _ x)
  exact congr_fun (congrArg DFunLike.coe hu) t

theorem rightInner_compl_emb (P : ThreeShuffle m n p) (j : Fin n) :
    P.mnBlock.1.orderEmbOfFin P.mnBlock.2
        (((rightInner P).1ᶜ : Finset (Fin (m + n))).orderEmbOfFin
          (by rw [Finset.card_compl, (rightInner P).2, Fintype.card_fin]; omega) j) =
      (nBlock P).1.orderEmbOfFin (nBlock P).2 j := by
  let e : Fin (m + n) ↪o Fin (m + n + p) := P.mnBlock.1.orderEmbOfFin P.mnBlock.2
  have hsub : ↑(P.mBlock.1 : Finset (Fin (m + n + p))) ⊆ Set.range e := by
    intro x hx
    rw [Finset.range_orderEmbOfFin]
    exact P.mBlock_subset hx
  have himg : (Finset.univ.filter (fun r : Fin (m + n) => e r ∈ P.mBlock.1)).map e.toEmbedding =
      P.mBlock.1 :=
    filter_map_image e.toEmbedding P.mBlock.1 (by
      simpa [RelEmbedding.coe_toEmbedding] using hsub)
  have himg' : ((rightInner P).1ᶜ : Finset (Fin (m + n))).map e.toEmbedding = (nBlock P).1 := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨r, hr, rfl⟩
      change e r ∈ P.mnBlock.1 \ P.mBlock.1
      rw [Finset.mem_sdiff]
      constructor
      · exact Finset.orderEmbOfFin_mem P.mnBlock.1 P.mnBlock.2 r
      · intro hxM
        have hr' : r ∈ (rightInner P).1 := by
          change r ∈ Finset.univ.filter (fun r : Fin (m + n) =>
            P.mnBlock.1.orderEmbOfFin P.mnBlock.2 r ∈ P.mBlock.1)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [e] using hxM⟩
        exact (Finset.mem_compl.mp hr) hr'
    · intro hx
      change x ∈ P.mnBlock.1 \ P.mBlock.1 at hx
      rw [Finset.mem_sdiff] at hx
      have hxr : x ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]
        exact hx.1
      rcases hxr with ⟨r, hr⟩
      refine Finset.mem_map.mpr ⟨r, ?_, hr⟩
      rw [Finset.mem_compl]
      intro hr'
      have : e r ∈ (Finset.univ.filter (fun r : Fin (m + n) =>
          P.mnBlock.1.orderEmbOfFin P.mnBlock.2 r ∈ P.mBlock.1)).map e.toEmbedding := by
        exact Finset.mem_map.mpr ⟨r, by
          show r ∈ Finset.univ.filter (fun r : Fin (m + n) =>
            P.mnBlock.1.orderEmbOfFin P.mnBlock.2 r ∈ P.mBlock.1)
          exact hr', rfl⟩
      rw [himg] at this
      rw [hr] at this
      exact hx.2 this
  have hmap := orderEmbOfFin_map ((rightInner P).1ᶜ : Finset (Fin (m + n)))
    (by rw [Finset.card_compl, (rightInner P).2, Fintype.card_fin]; omega) e j
  change P.mnBlock.1.orderEmbOfFin P.mnBlock.2
    (((rightInner P).1ᶜ : Finset (Fin (m + n))).orderEmbOfFin
      (by rw [Finset.card_compl, (rightInner P).2, Fintype.card_fin]; omega) j) =
    (nBlock P).1.orderEmbOfFin (nBlock P).2 j
  rw [← hmap]
  simp [himg']

theorem leftInner_compl_emb (P : ThreeShuffle m n p) (k : Fin p) :
    ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P)
        (((leftInner P).1ᶜ : Finset (Fin (n + p))).orderEmbOfFin
          (by rw [Finset.card_compl, (leftInner P).2, Fintype.card_fin]; omega) k) =
      (pBlock P).1.orderEmbOfFin (pBlock P).2 k := by
  let e : Fin (n + p) ↪o Fin (m + n + p) :=
    ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P)
  have hsub : ↑((nBlock P).1 : Finset (Fin (m + n + p))) ⊆ Set.range e := by
    intro x hx
    have hxM : x ∉ P.mBlock.1 := (Finset.mem_sdiff.mp hx).2
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_compl.mpr hxM
  have himg : (Finset.univ.filter (fun r : Fin (n + p) => e r ∈ (nBlock P).1)).map e.toEmbedding =
      (nBlock P).1 :=
    filter_map_image e.toEmbedding (nBlock P).1 (by
      simpa [RelEmbedding.coe_toEmbedding] using hsub)
  have himg' : ((leftInner P).1ᶜ : Finset (Fin (n + p))).map e.toEmbedding = (pBlock P).1 := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨r, hr, rfl⟩
      change e r ∈ (P.mnBlock.1ᶜ : Finset (Fin (m + n + p)))
      rw [Finset.mem_compl]
      intro hxP
      have hxMc : e r ∈ (P.mBlock.1ᶜ : Finset (Fin (m + n + p))) := by
        exact Finset.orderEmbOfFin_mem (P.mBlock.1ᶜ) (mBlock_compl_card P) r
      have hxN : e r ∈ (nBlock P).1 := by
        change e r ∈ P.mnBlock.1 \ P.mBlock.1
        rw [Finset.mem_sdiff]
        exact ⟨hxP, Finset.mem_compl.mp hxMc⟩
      have hr' : r ∈ (leftInner P).1 := by
        change r ∈ Finset.univ.filter (fun r : Fin (n + p) =>
          ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P) r ∈
            (nBlock P).1)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [e] using hxN⟩
      exact (Finset.mem_compl.mp hr) hr'
    · intro hx
      change x ∈ (P.mnBlock.1ᶜ : Finset (Fin (m + n + p))) at hx
      rw [Finset.mem_compl] at hx
      have hxMc : x ∈ (P.mBlock.1ᶜ : Finset (Fin (m + n + p))) :=
        Finset.mem_compl.mpr (fun hxm => hx (P.mBlock_subset hxm))
      have hxr : x ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]
        exact hxMc
      rcases hxr with ⟨r, hr⟩
      refine Finset.mem_map.mpr ⟨r, ?_, hr⟩
      rw [Finset.mem_compl]
      intro hr'
      have : e r ∈ (Finset.univ.filter (fun r : Fin (n + p) =>
          ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P) r ∈
            (nBlock P).1)).map e.toEmbedding := by
        exact Finset.mem_map.mpr ⟨r, by
          show r ∈ Finset.univ.filter (fun r : Fin (n + p) =>
            ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P) r ∈
              (nBlock P).1)
          exact hr', rfl⟩
      rw [himg] at this
      rw [hr] at this
      exact hx (Finset.mem_sdiff.mp this).1
  have hmap := orderEmbOfFin_map ((leftInner P).1ᶜ : Finset (Fin (n + p)))
    (by rw [Finset.card_compl, (leftInner P).2, Fintype.card_fin]; omega) e k
  change ((P.mBlock.1)ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card P)
    (((leftInner P).1ᶜ : Finset (Fin (n + p))).orderEmbOfFin
      (by rw [Finset.card_compl, (leftInner P).2, Fintype.card_fin]; omega) k) =
    (pBlock P).1.orderEmbOfFin (pBlock P).2 k
  rw [← hmap]
  simp [himg']

private def assocSum (m n p : ℕ) : (Fin m ⊕ Fin n) ⊕ Fin p ≃ Fin m ⊕ (Fin n ⊕ Fin p) where
  toFun := fun x => match x with
    | Sum.inl (Sum.inl i) => Sum.inl i
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inl j)
    | Sum.inr k => Sum.inr (Sum.inr k)
  invFun := fun x => match x with
    | Sum.inl i => Sum.inl (Sum.inl i)
    | Sum.inr (Sum.inl j) => Sum.inl (Sum.inr j)
    | Sum.inr (Sum.inr k) => Sum.inr k
  left_inv := by intro x; rcases x with ((i | j) | k) <;> rfl
  right_inv := by intro x; rcases x with (i | (j | k)) <;> rfl

private def leftPosEquiv (m n p : ℕ) : Fin m ⊕ (Fin n ⊕ Fin p) ≃ Fin (m + n + p) :=
  (Equiv.sumCongr (Equiv.refl (Fin m)) (finSumFinEquiv : Fin n ⊕ Fin p ≃ Fin (n + p))).trans
    ((finSumFinEquiv : Fin m ⊕ Fin (n + p) ≃ Fin (m + (n + p))).trans
      (finAssocOrder m n p).symm.toEquiv)

private def rightPosEquiv (m n p : ℕ) : (Fin m ⊕ Fin n) ⊕ Fin p ≃ Fin (m + n + p) :=
  (Equiv.sumCongr (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)) (Equiv.refl (Fin p))).trans
    (finSumFinEquiv : Fin (m + n) ⊕ Fin p ≃ Fin (m + n + p))

private theorem rightPosEquiv_sumCongr_symm (m n p : ℕ) (y : Fin (m + n) ⊕ Fin p) :
    rightPosEquiv m n p (Equiv.sumCongr (finSumFinEquiv.symm : Fin (m + n) ≃ Fin m ⊕ Fin n)
      (Equiv.refl (Fin p)) y) = finSumFinEquiv y := by
  simp [rightPosEquiv, Equiv.sumCongr_apply]

private theorem leftPosEquiv_sumCongr_symm (m n p : ℕ) (y : Fin m ⊕ Fin (n + p)) :
    leftPosEquiv m n p (Equiv.sumCongr (Equiv.refl (Fin m)) (finSumFinEquiv.symm : Fin
      (n + p) ≃ Fin n ⊕ Fin p) y) =
      (finAssocOrder m n p).symm (finSumFinEquiv y) := by
  simp [leftPosEquiv, Equiv.sumCongr_apply]

private theorem canonicalRight_m (P : ThreeShuffle m n p) (i : Fin m) :
    rightPosEquiv m n p (canonicalRight P (Sum.inl (Sum.inl i))) =
      P.mBlock.1.orderEmbOfFin P.mBlock.2 i := by
  rw [canonicalRight, mergeRight_inl_inl]
  rw [rightPosEquiv_sumCongr_symm]
  rw [TwoShuffle.toPerm_inl]
  change P.mnBlock.1.orderEmbOfFin P.mnBlock.2
    (finSumFinEquiv (P.rightInner.toPerm (Sum.inl i))) = P.mBlock.1.orderEmbOfFin P.mBlock.2 i
  rw [TwoShuffle.toPerm_inl]
  exact rightInner_emb P i

private theorem canonicalRight_n (P : ThreeShuffle m n p) (j : Fin n) :
    rightPosEquiv m n p (canonicalRight P (Sum.inl (Sum.inr j))) =
      (nBlock P).1.orderEmbOfFin (nBlock P).2 j := by
  rw [canonicalRight, mergeRight_inl_inr]
  rw [rightPosEquiv_sumCongr_symm]
  rw [TwoShuffle.toPerm_inl]
  change P.mnBlock.1.orderEmbOfFin P.mnBlock.2
    (finSumFinEquiv (P.rightInner.toPerm (Sum.inr j))) = (nBlock P).1.orderEmbOfFin (nBlock P).2 j
  rw [TwoShuffle.toPerm_inr]
  exact rightInner_compl_emb P j

private theorem canonicalRight_p (P : ThreeShuffle m n p) (k : Fin p) :
    rightPosEquiv m n p (canonicalRight P (Sum.inr k)) =
      (pBlock P).1.orderEmbOfFin (pBlock P).2 k := by
  rw [canonicalRight, mergeRight_inr]
  rw [rightPosEquiv_sumCongr_symm]
  rw [TwoShuffle.toPerm_inr]
  rfl

private theorem canonicalLeft_m (P : ThreeShuffle m n p) (i : Fin m) :
    leftPosEquiv m n p (canonicalLeft P (Sum.inl i)) = P.mBlock.1.orderEmbOfFin P.mBlock.2 i := by
  rw [canonicalLeft, mergeLeft_inl]
  rw [leftPosEquiv_sumCongr_symm]
  rw [TwoShuffle.toPerm_inl]
  exact leftOuter_emb P i

private theorem canonicalLeft_n (P : ThreeShuffle m n p) (j : Fin n) :
    leftPosEquiv m n p (canonicalLeft P (Sum.inr (Sum.inl j))) =
      (nBlock P).1.orderEmbOfFin (nBlock P).2 j := by
  rw [canonicalLeft, mergeLeft_inr_inl]
  rw [leftPosEquiv_sumCongr_symm]
  rw [TwoShuffle.toPerm_inr]
  rw [TwoShuffle.toPerm_inl]
  exact (leftOuter_compl_emb P ((leftInner P).1.orderEmbOfFin (leftInner P).2 j)).trans
    (leftInner_emb P j)

private theorem canonicalLeft_p (P : ThreeShuffle m n p) (k : Fin p) :
    leftPosEquiv m n p (canonicalLeft P (Sum.inr (Sum.inr k))) =
      (pBlock P).1.orderEmbOfFin (pBlock P).2 k := by
  rw [canonicalLeft, mergeLeft_inr_inr]
  rw [leftPosEquiv_sumCongr_symm]
  rw [TwoShuffle.toPerm_inr]
  rw [TwoShuffle.toPerm_inr]
  exact (leftOuter_compl_emb P (((leftInner P).1ᶜ : Finset (Fin (n + p))).orderEmbOfFin
    (by rw [Finset.card_compl, (leftInner P).2, Fintype.card_fin]; omega) k)).trans
    (leftInner_compl_emb P k)

private theorem leftPosEquiv_assocSum (m n p : ℕ) (x : (Fin m ⊕ Fin n) ⊕ Fin p) :
    leftPosEquiv m n p (assocSum m n p x) = rightPosEquiv m n p x := by
  cases x with
  | inl x => cases x with
    | inl i => apply Fin.ext; rfl
    | inr j => apply Fin.ext; rfl
  | inr k =>
    apply Fin.ext
    simp only [leftPosEquiv, rightPosEquiv, assocSum]
    exact (Nat.add_assoc m n ↑k).symm

private theorem canonicalLeft_canonicalRight_pos (P : ThreeShuffle m n p) (x :
    (Fin m ⊕ Fin n) ⊕ Fin p) :
    leftPosEquiv m n p (canonicalLeft P (assocSum m n p x)) = rightPosEquiv m n p
      (canonicalRight P x) := by
  cases x with
  | inl x => cases x with
    | inl i =>
      exact (canonicalLeft_m P i).trans (canonicalRight_m P i).symm
    | inr j =>
      exact (canonicalLeft_n P j).trans (canonicalRight_n P j).symm
  | inr k =>
    exact (canonicalLeft_p P k).trans (canonicalRight_p P k).symm

private theorem canonicalLeft_permCongr (P : ThreeShuffle m n p) :
    canonicalLeft P = (assocSum m n p).permCongr (canonicalRight P) := by
  apply Equiv.ext
  intro x
  have h := canonicalLeft_canonicalRight_pos P ((assocSum m n p).symm x)
  rw [Equiv.apply_symm_apply] at h
  rw [← leftPosEquiv_assocSum m n p (canonicalRight P ((assocSum m n p).symm x))] at h
  have hx := (leftPosEquiv m n p).injective h
  simpa [Equiv.permCongr_def] using hx

theorem sign_canonicalLeft_canonicalRight (P : ThreeShuffle m n p) :
    Equiv.Perm.sign (canonicalLeft P) = Equiv.Perm.sign (canonicalRight P) := by
  rw [canonicalLeft_permCongr P]
  exact Equiv.Perm.sign_permCongr (assocSum m n p) (canonicalRight P)

private theorem map_map_round_trip {α β : Type*} (e : α ≃ β)
    (h : ∀ x, e (e.symm x) = x) (s : Finset β) :
    (s.map e.symm.toEmbedding).map e.toEmbedding = s := by
  rw [Finset.map_map]
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨a, ha, hxa⟩
    have hxa' : a = x := (h a).symm.trans hxa
    rw [← hxa']
    exact ha
  · intro hx
    exact Finset.mem_map.mpr ⟨x, hx, h x⟩

private theorem map_map_round_trip' {α β : Type*} (e : α ≃ β)
    (h : ∀ x, e.symm (e x) = x) (s : Finset α) :
    (s.map e.toEmbedding).map e.symm.toEmbedding = s := by
  rw [Finset.map_map]
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨a, ha, hxa⟩
    have hxa' : a = x := (h a).symm.trans hxa
    rw [← hxa']
    exact ha
  · intro hx
    exact Finset.mem_map.mpr ⟨x, hx, h x⟩

def leftAssocShuffle (m n p : ℕ) :
    TwoShuffle (m + n) p × TwoShuffle m n ≃ ThreeShuffle m n p where
  toFun := fun SR =>
    ⟨SR.1, ⟨SR.2.1.map (SR.1.1.orderEmbOfFin SR.1.2).toEmbedding, by
      rw [Finset.card_map]
      exact SR.2.2⟩, by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨r, hr, rfl⟩
      exact Finset.orderEmbOfFin_mem SR.1.1 SR.1.2 r⟩
  invFun := fun P => (P.rightOuter, P.rightInner)
  left_inv := by
    intro SR
    rcases SR with ⟨S, R⟩
    apply Prod.ext
    · change (⟨S, ⟨R.1.map (S.1.orderEmbOfFin S.2).toEmbedding, by
        rw [Finset.card_map]
        exact R.2⟩, by
        intro x hx
        rcases Finset.mem_map.mp hx with ⟨r, hr, rfl⟩
        exact Finset.orderEmbOfFin_mem S.1 S.2 r⟩ : ThreeShuffle m n p).rightOuter = S
      rfl
    · change (⟨S, ⟨R.1.map (S.1.orderEmbOfFin S.2).toEmbedding, by
        rw [Finset.card_map]
        exact R.2⟩, by
        intro x hx
        rcases Finset.mem_map.mp hx with ⟨r, hr, rfl⟩
        exact Finset.orderEmbOfFin_mem S.1 S.2 r⟩ : ThreeShuffle m n p).rightInner = R
      apply Subtype.ext
      dsimp [rightInner]
      change Finset.univ.filter (fun r : Fin (m + n) =>
        S.1.orderEmbOfFin S.2 r ∈ R.1.map (S.1.orderEmbOfFin S.2).toEmbedding) = R.1
      ext r
      constructor
      · intro hr
        rw [Finset.mem_filter] at hr
        rcases Finset.mem_map.mp hr.2 with ⟨r', hr', hr''⟩
        have hEq : r = r' := (S.1.orderEmbOfFin S.2).toEmbedding.injective hr''.symm
        simpa [hEq] using hr'
      · intro hr
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ _
        · show S.1.orderEmbOfFin S.2 r ∈ R.1.map (S.1.orderEmbOfFin S.2).toEmbedding
          exact Finset.mem_map.mpr (Exists.intro r (And.intro hr rfl))
  right_inv := by
    intro P
    rcases P with ⟨S, T, hT⟩
    apply ThreeShuffle.ext
    · change (⟨S.1, S.2⟩ : {S : Finset (Fin (m + n + p)) // S.card = m + n}) =
        (⟨S.1, S.2⟩ : {S : Finset (Fin (m + n + p)) // S.card = m + n})
      rfl
    · apply Subtype.ext
      change (Finset.univ.filter (fun r : Fin (m + n) => S.1.orderEmbOfFin S.2 r ∈ T.1)).map
        (S.1.orderEmbOfFin S.2).toEmbedding = T.1
      exact filter_map_image (S.1.orderEmbOfFin S.2).toEmbedding T.1 (by
        intro x hx
        simpa [RelEmbedding.coe_toEmbedding] using (by
          rw [Finset.range_orderEmbOfFin]
          exact hT hx : x ∈ Set.range (S.1.orderEmbOfFin S.2)))

@[simp]
theorem leftAssocShuffle_rightOuter (m n p : ℕ)
    (SR : TwoShuffle (m + n) p × TwoShuffle m n) :
    (leftAssocShuffle m n p SR).rightOuter = SR.1 := rfl

@[simp]
theorem leftAssocShuffle_rightInner (m n p : ℕ)
    (SR : TwoShuffle (m + n) p × TwoShuffle m n) :
    (leftAssocShuffle m n p SR).rightInner = SR.2 := by
  apply Subtype.ext
  apply Finset.ext
  intro r
  constructor
  · intro hr
    change r ∈ Finset.univ.filter (fun r : Fin (m + n) =>
      SR.1.1.orderEmbOfFin SR.1.2 r ∈ SR.2.1.map (SR.1.1.orderEmbOfFin SR.1.2).toEmbedding) at hr
    rcases Finset.mem_map.mp (Finset.mem_filter.mp hr).2 with ⟨r', hr', hr''⟩
    have hrr : r = r' := (SR.1.1.orderEmbOfFin SR.1.2).toEmbedding.injective hr''.symm
    simpa [hrr] using hr'
  · intro hr
    change r ∈ Finset.univ.filter (fun r : Fin (m + n) =>
      SR.1.1.orderEmbOfFin SR.1.2 r ∈ SR.2.1.map (SR.1.1.orderEmbOfFin SR.1.2).toEmbedding)
    rw [Finset.mem_filter]
    exact ⟨by simp, Finset.mem_map.mpr ⟨r, hr, rfl⟩⟩

def rightAssocShuffle (m n p : ℕ) :
    TwoShuffle m (n + p) × TwoShuffle n p ≃ ThreeShuffle m n p where
  toFun := fun MR =>
    let M : Finset (Fin (m + n + p)) :=
      MR.1.1.map (finAssocOrder m n p).symm.toEmbedding
    let e : Fin (n + p) ↪o Fin (m + n + p) :=
      (Mᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (by
        dsimp [M]
        rw [Finset.card_compl, Finset.card_map, MR.1.2, Fintype.card_fin]
        omega)
    let N : Finset (Fin (m + n + p)) := MR.2.1.map e.toEmbedding
    ⟨⟨M ∪ N, by
        have hMN : _root_.Disjoint M N := by
          rw [Finset.disjoint_left]
          intro x hxM hxN
          dsimp [N] at hxN
          rcases Finset.mem_map.mp hxN with ⟨r, hr, rfl⟩
          exact (Finset.mem_compl.mp (Finset.orderEmbOfFin_mem (Mᶜ) (by
            dsimp [M]
            rw [Finset.card_compl, Finset.card_map, MR.1.2, Fintype.card_fin]
            omega) r)) hxM
        rw [Finset.card_union_of_disjoint hMN]
        dsimp [M, N]
        rw [Finset.card_map, Finset.card_map, MR.1.2, MR.2.2]
        ⟩, ⟨M, by
          dsimp [M]
          rw [Finset.card_map]
          exact MR.1.2⟩, by
        intro x hx
        exact Finset.mem_union_left _ hx⟩
  invFun := fun P => (P.leftOuter, P.leftInner)
  left_inv := by
    intro MR
    rcases MR with ⟨M₀, R⟩
    let M : Finset (Fin (m + n + p)) := M₀.1.map (finAssocOrder m n p).symm.toEmbedding
    let e : Fin (n + p) ↪o Fin (m + n + p) :=
      (Mᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (by
        dsimp [M]
        rw [Finset.card_compl, Finset.card_map, M₀.2, Fintype.card_fin]
        omega)
    let N : Finset (Fin (m + n + p)) := R.1.map e.toEmbedding
    apply Prod.ext
    · apply Subtype.ext
      change M.map (finAssocOrder m n p).toEmbedding = M₀.1
      exact map_map_round_trip (finAssocOrder m n p).toEquiv
        (fun x => by rw [Equiv.apply_symm_apply]) M₀.1
    · apply Subtype.ext
      change Finset.univ.filter (fun r : Fin (n + p) => e r ∈ (M ∪ N) \ M) = R.1
      ext r
      constructor
      · intro hr
        rw [Finset.mem_filter] at hr
        have hrN : e r ∈ N :=
          (Finset.mem_union.mp (Finset.mem_sdiff.mp hr.2).1).resolve_left
            (Finset.mem_sdiff.mp hr.2).2
        dsimp [N] at hrN
        rcases Finset.mem_map.mp hrN with ⟨r', hr', hr''⟩
        have hrEq : r = r' := e.toEmbedding.injective hr''.symm
        simpa [hrEq] using hr'
      · intro hr
        rw [Finset.mem_filter]
        refine ⟨by simp, ?_⟩
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr ?_), ?_⟩
        · exact Finset.mem_map.mpr ⟨r, hr, rfl⟩
        · intro hxM
          dsimp [M] at hxM
          rcases Finset.mem_map.mp hxM with ⟨a, ha, ha'⟩
          have : e r ∈ M := Finset.mem_map.mpr ⟨a, ha, ha'⟩
          exact (Finset.mem_compl.mp (Finset.orderEmbOfFin_mem (Mᶜ) (by
            dsimp [M]
            rw [Finset.card_compl, Finset.card_map, M₀.2, Fintype.card_fin]
            omega) r)) this
  right_inv := by
    intro P
    rcases P with ⟨S, T, hT⟩
    let M' : Finset (Fin (m + n + p)) :=
      (T.1.map (finAssocOrder m n p).toEmbedding).map (finAssocOrder m n p).symm.toEmbedding
    let e : Fin (n + p) ↪o Fin (m + n + p) :=
      (T.1ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (mBlock_compl_card ⟨S, T, hT⟩)
    have hM' : M' = T.1 := by
      dsimp [M']
      exact map_map_round_trip' (finAssocOrder m n p).toEquiv
        (fun x => by rw [Equiv.symm_apply_apply]) T.1
    let e' : Fin (n + p) ↪o Fin (m + n + p) :=
      (M'ᶜ : Finset (Fin (m + n + p))).orderEmbOfFin (by
        dsimp [M']
        rw [Finset.card_compl, Finset.card_map, Finset.card_map, T.2, Fintype.card_fin]
        omega)
    have hsort : (M'ᶜ : Finset (Fin (m + n + p))).sort (· ≤ ·) =
        (T.1ᶜ : Finset (Fin (m + n + p))).sort (· ≤ ·) := by
      exact congrArg (fun s : Finset (Fin (m + n + p)) =>
        (sᶜ : Finset (Fin (m + n + p))).sort (· ≤ ·)) hM'
    have he : ∀ r : Fin (n + p),
        (e' : Fin (n + p) → Fin (m + n + p)) r = (e : Fin (n + p) → Fin (m + n + p)) r := by
      intro r
      dsimp [e, e']
      simp [Finset.orderEmbOfFin_apply, hsort]
    have hN' : (Finset.univ.filter (fun r : Fin (n + p) => e r ∈ S.1 \ T.1)).map e'.toEmbedding =
        S.1 \ T.1 := by
      apply Finset.ext
      intro x
      constructor
      · intro hx
        rcases Finset.mem_map.mp hx with ⟨r, hr, hr'⟩
        have hrS : e r ∈ S.1 \ T.1 := (Finset.mem_filter.mp hr).2
        have : e' r ∈ S.1 \ T.1 := by
          rw [he r]
          exact hrS
        rw [← hr']
        exact this
      · intro hx
        have hxM' : x ∉ (T.1.map (finAssocOrder m n p).toEmbedding).map
            (finAssocOrder m n p).symm.toEmbedding := by
          intro hxM'
          apply (Finset.mem_sdiff.mp hx).2
          rw [← hM']
          exact hxM'
        have hxr : x ∈ Set.range e' := by
          rw [Finset.range_orderEmbOfFin]
          exact Finset.mem_compl.mpr hxM'
        rcases hxr with ⟨r, hr⟩
        refine Finset.mem_map.mpr ⟨r, ?_, hr⟩
        rw [Finset.mem_filter]
        refine ⟨by simp, ?_⟩
        rw [← he r, hr]
        exact hx
    apply ThreeShuffle.ext
    · apply Subtype.ext
      change M' ∪ (Finset.univ.filter (fun r : Fin
        (n + p) => e r ∈ S.1 \ T.1)).map e'.toEmbedding = S.1
      rw [hM', hN', Finset.union_sdiff_of_subset hT]
    · apply Subtype.ext
      change M' = T.1
      exact hM'

@[simp]
theorem rightAssocShuffle_leftOuter (m n p : ℕ)
    (MR : TwoShuffle m (n + p) × TwoShuffle n p) :
    (rightAssocShuffle m n p MR).leftOuter = MR.1 := by
  dsimp [leftOuter, rightAssocShuffle]
  apply Subtype.ext
  change (MR.1.1.map (finAssocOrder m n p).symm.toEmbedding).map
      (finAssocOrder m n p).toEmbedding = MR.1.1
  exact map_map_round_trip (finAssocOrder m n p).toEquiv
    (fun x => by rw [Equiv.apply_symm_apply]) MR.1.1

@[simp]
theorem rightAssocShuffle_leftInner (m n p : ℕ)
    (MR : TwoShuffle m (n + p) × TwoShuffle n p) :
    (rightAssocShuffle m n p MR).leftInner = MR.2 := by
  change (fun P : ThreeShuffle m n p => P.leftInner)
    ((rightAssocShuffle m n p) MR) = MR.2
  change Prod.snd ((rightAssocShuffle m n p).symm ((rightAssocShuffle m n p) MR)) =
    Prod.snd MR
  exact congrArg Prod.snd ((Equiv.left_inv (rightAssocShuffle m n p)) MR)

noncomputable def leftShuffle (m n p : ℕ) :
    (ModSumCongr (Fin (m + n)) (Fin p) × ModSumCongr (Fin m) (Fin n)) ≃ ThreeShuffle m n p :=
  (TwoShuffle.modSumCongrTwoShuffle (m + n) p).prodCongr
    (TwoShuffle.modSumCongrTwoShuffle m n) |>.trans
    (leftAssocShuffle m n p)

noncomputable def rightShuffle (m n p : ℕ) :
    (ModSumCongr (Fin m) (Fin (n + p)) × ModSumCongr (Fin n) (Fin p)) ≃ ThreeShuffle m n p :=
  (TwoShuffle.modSumCongrTwoShuffle m (n + p)).prodCongr
    (TwoShuffle.modSumCongrTwoShuffle n p) |>.trans
    (rightAssocShuffle m n p)

noncomputable instance (m n p : ℕ) : Fintype (ThreeShuffle m n p) :=
  Fintype.ofEquiv
    (TwoShuffle (m + n) p × TwoShuffle m n)
    (Equiv.trans
      ((TwoShuffle.modSumCongrTwoShuffle (m + n) p).prodCongr
        (TwoShuffle.modSumCongrTwoShuffle m n)).symm
      (leftShuffle m n p))

instance (m n p : ℕ) : Finite (ThreeShuffle m n p) :=
  Finite.of_fintype (ThreeShuffle m n p)

end ThreeShuffle

end Equiv.Perm
