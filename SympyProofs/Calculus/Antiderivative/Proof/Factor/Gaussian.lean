module

public import SympyProofs.Calculus.Antiderivative.Proof.Factor.GaussianNorm

/-! A nonreal monic translate of a reducible Gaussian polynomial has a proper gcd with a
rational irreducible factor of its norm. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.WithI

open Polynomial

variable {F : Type} [Field F] [DecidableEq F]
variable [Fact (∀ x : F, x ^ 2 ≠ -1 + 0 * x)]
local notation "G" => WithI F
variable [CharZero F]


private theorem degree_le_of_dvd {A : Type} [Field A] [DecidableEq A] {a b : Poly A}
    (hd : a ∣ b) (hb : b ≠ 0) : a.natDegree ≤ b.natDegree := by
  simpa only [Poly.natDegree_equiv] using
    natDegree_le_of_dvd (map_dvd Poly.equiv hd) ((map_ne_zero_iff _ Poly.equiv.injective).mpr hb)

omit [CharZero F] in
private theorem small_divisor (q : Poly G) (hq : 2 ≤ q.natDegree) (hi : ¬ Irreducible q) :
    ∃ a : Poly G, a ∣ q ∧ 0 < a.natDegree ∧ a.natDegree ≤ q.natDegree / 2 := by
  have hq₀ : q ≠ 0 := fun h => by simp [h] at hq
  have hpos : 0 < (Poly.equiv q).natDegree := by simp; omega
  have h : ¬ Irreducible (Poly.equiv q) := fun h =>
    hi ((MulEquiv.irreducible_iff (Poly.equiv (R := G))).mp h)
  rw [Polynomial.irreducible_iff_lt_natDegree_lt
    ((map_ne_zero_iff _ Poly.equiv.injective).mpr hq₀) (not_isUnit_of_natDegree_pos _ hpos)] at h
  push Not at h
  obtain ⟨a,_,ha,hdiv⟩ := h
  rw [Finset.mem_Ioc, Poly.natDegree_equiv] at ha
  refine ⟨Poly.equiv.symm a, by simpa using map_dvd Poly.equiv.symm hdiv, ?_⟩
  simpa only [← Poly.natDegree_equiv, RingEquiv.apply_symm_apply] using ha

variable [ConstantFactors F] [LawfulConstantFactors F]

private theorem prime_norm_factor {q u : Poly G} (hq : q ≠ 0) (hu : Prime u) (huq : u ∣ q) :
    ∃ h ∈ ConstantFactors.factors (normPoly q), u ∣ includeBase h := by
  let N := normPoly q
  have hN := normPoly_ne_zero hq
  have hprod : Poly.C N.leadingCoeff * (ConstantFactors.factors N).prod = N :=
    LawfulConstantFactors.product N hN
  have hc : IsUnit (includeBase (Poly.C N.leadingCoeff)) :=
    ((isUnit_iff_ne_zero.mpr (Poly.leadingCoeff_ne_zero hN)).map Poly.CRingHom).map includeBase
  have hd : u ∣ includeBase N := by
    rw [show N = normPoly q from rfl, includeBase_normPoly]
    exact huq.trans (dvd_mul_right _ _)
  rw [← hprod, map_mul, map_list_prod] at hd
  obtain hscalar | hlist := hu.dvd_or_dvd hd
  · exact (hu.not_isUnit (isUnit_of_dvd_unit hscalar hc)).elim
  obtain ⟨b,hb,hu'⟩ := hu.dvd_prod_iff.mp hlist
  obtain ⟨h,hm,rfl⟩ := List.mem_map.mp hb
  exact ⟨h,hm,hu'⟩

private theorem norm_factor_proper (q : Poly G) (hm : (Poly.equiv q).Monic)
    (hd : 2 ≤ q.natDegree) (hn : (Poly.equiv q).nextCoeff.im ≠ 0) (hI : ¬ Irreducible q) :
    ∃ h ∈ ConstantFactors.factors (normPoly q), Factor.proper q (gcd q (includeBase h)) := by
  obtain ⟨a,ha,hapos,had⟩ := small_divisor q hd hI
  have ha₀ : a ≠ 0 := fun h => by simp [h] at hapos
  have hq₀ : q ≠ 0 := (map_ne_zero_iff _ Poly.equiv.injective).mp hm.ne_zero
  have hpa := exists_monic_irreducible_factor (Poly.equiv a)
    (not_isUnit_of_natDegree_pos _ (by simpa using hapos))
  obtain ⟨P,_,hi,hdiv⟩ := hpa
  let u := Poly.equiv.symm P
  have hu : Prime u := (hi.map (Poly.equiv (R := G)).symm).prime
  have hua : u ∣ a := by simpa [u] using map_dvd (Poly.equiv (R := G)).symm hdiv
  obtain ⟨b,hb,hub⟩ := prime_norm_factor hq₀ hu (hua.trans ha)
  obtain ⟨hmon,hirr⟩ := LawfulConstantFactors.irreducible _ (normPoly_ne_zero hq₀) b hb
  have hbn : b ∣ normPoly a := by
    by_contra h
    have hc := (hirr.coprime_iff_not_dvd.mpr h).map includeBase
    rw [includeBase_normPoly] at hc
    exact hu.not_isUnit (hc.isUnit_of_dvd' hub (hua.trans (dvd_mul_right a _)))
  have hdeg := degree_le_of_dvd hbn (normPoly_ne_zero ha₀)
  rw [normPoly_degree ha₀] at hdeg
  let f := gcd q (includeBase b)
  have hfq : f ∣ q := gcd_dvd_left ..
  have hfb : f ∣ includeBase b := gcd_dvd_right ..
  have hf₀ : f ≠ 0 := fun hz => hq₀ (zero_dvd_iff.mp (hz ▸ hfq))
  have hug : u ∣ f := dvd_gcd (hua.trans ha) hub
  have hfpos : 0 < f.natDegree := by
    apply lt_of_lt_of_le _ (degree_le_of_dvd hug hf₀)
    rw [← Poly.natDegree_equiv, show Poly.equiv u = P from Poly.equiv.apply_symm_apply _]
    exact hi.natDegree_pos
  refine ⟨b,hb,(Factor.proper_iff q f).mpr ⟨hfpos,?_,hfq⟩⟩
  by_contra hlt
  have hmf : (Poly.equiv f).Monic := by
    change (Poly.equiv f).leadingCoeff = 1
    rw [Poly.leadingCoeff_equiv, show f = gcd q (includeBase b) from rfl,
      Poly.leadingCoeff_gcd_of_left_ne_zero hq₀]
  have hf := eq_of_monic_of_dvd_of_natDegree_le hmf hm (map_dvd Poly.equiv hfq)
    (by simpa only [Poly.natDegree_equiv] using le_of_not_gt hlt)
  have hmb : (Poly.equiv (includeBase b)).Monic := by rw [equiv_includeBase]; exact hmon.map _
  have hqd : q ∣ includeBase b := (Poly.equiv.injective hf) ▸ hfb
  have he := eq_of_monic_of_dvd_of_natDegree_le hm hmb (map_dvd Poly.equiv hqd)
    (by simp only [Poly.natDegree_equiv, includeBase_degree]; omega)
  apply hn
  rw [← he, equiv_includeBase, nextCoeff_map (algebraMap F G).injective]
  rfl

/-- The quadratic divisor search returns a proper factor of every reducible input of degree ≥ 2. -/
theorem divisor_complete (p : Poly G) (hd : 2 ≤ p.natDegree) (hI : ¬ Irreducible p) :
    ∃ b, divisor p = some b ∧ Factor.proper p b := by
  let m := normalize p
  let a := shift m
  let q := translate m a
  have hp₀ : p ≠ 0 := fun h => by simp [h] at hd
  have hm : (Poly.equiv m).Monic := by
    change (Poly.equiv (normalize p)).leadingCoeff = 1
    rw [Poly.leadingCoeff_equiv, Poly.leadingCoeff_normalize, ite_eq_right hp₀]
  have hq : (Poly.equiv q).Monic := by
    change (Poly.equiv (translate m a)).leadingCoeff = 1
    simp [hm.leadingCoeff]
  have hdeg : q.natDegree = p.natDegree := by simp [q, m]
  have hqr : ¬ Irreducible q := fun h =>
    hI ((normalize_associated p).irreducible_iff.mp
      ((MulEquiv.irreducible_iff (translation a)).mp (by simpa [q] using h)))
  have hnr := shift_nonreal m hm (by simp [m]; omega)
  obtain ⟨b,hb,hprop⟩ := norm_factor_proper q hq (hdeg ▸ hd) hnr hqr
  let f := gcd q (includeBase b)
  obtain ⟨hf0,hfd,hfq⟩ := (Factor.proper_iff q f).mp hprop
  have hpf : Factor.proper p (translate f (-a)) := by
    apply (Factor.proper_iff ..).mpr
    have h := map_dvd (translation (-a)) hfq
    have h' : translate f (-a) ∣ m := by simpa only [translation_apply, q, translate_back] using h
    exact ⟨by simpa using hf0, by simpa [hdeg] using hfd, h'.trans (normalize_associated p).dvd⟩
  have hs : (normDivisor p).isSome := by
    apply List.findSome?_isSome_iff.mpr
    refine ⟨b,hb,?_⟩
    change (if Factor.proper p (translate (gcd q (b.map _)) (-a)) then some _ else none).isSome
    rw [← includeBase_apply, ite_eq_left hpf]
    rfl
  rw [divisor]
  split
  · rename_i h
    exact ⟨_,rfl,h⟩
  · cases h : normDivisor p with
    | none => simp [h] at hs
    | some b =>
      refine ⟨b,rfl,?_⟩
      obtain ⟨c,_,hc⟩ := List.exists_of_findSome?_eq_some h
      dsimp only at hc
      split at hc
      · cases hc
        assumption
      · contradiction

/-- The quadratic factorization returns monic irreducibles with the stated product. -/
instance : LawfulConstantFactors G where
  irreducible p _ b h := ⟨Factor.split_monic _ _ _ h,
    Factor.split_irreducible _ divisor_complete _ _ le_rfl h⟩
  product p hp := by
    change Poly.C p.leadingCoeff * (Factor.split _ _ p).prod = p
    rw [Factor.split_prod _ _ _ hp, Poly.normalize_eq_C_mul, ← mul_assoc, ← Poly.C_mul,
      mul_inv_cancel₀ (Poly.leadingCoeff_ne_zero hp), Poly.C_one, one_mul]

end SympyProofs.Calculus.Antiderivative.WithI
