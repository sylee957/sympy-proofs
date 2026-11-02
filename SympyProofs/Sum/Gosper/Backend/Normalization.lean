module

public import SympyProofs.Sum.Gosper.Backend.Resultant

/-! Polynomial normalization primitives that keep their coefficients in an integral domain. -/

@[expose] public section

namespace Gosper.Algorithm

open Polynomial IsLocalization

/-- Gcd, exact division, resultant, and natural roots over the input coefficient ring. -/
structure NormalizationBackend (R : Type*) [CommRing R] [IsDomain R] where
  gcd : R[X] → R[X] → R[X]
  exactDiv : R[X] → R[X] → R[X]
  resultant : R[X][X] → R[X][X] → R[X]
  naturalRoots : R[X] → Finset ℕ

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The gcd is greatest in the ring and its fraction field, and exact division
cancels known divisors. Resultants agree up to a nonzero coefficient, and natural
root extraction returns exactly the natural roots of nonzero polynomials. -/
structure NormalizationBackend.Valid (backend : NormalizationBackend R) : Prop where
  gcd_dvd_left : ∀ p q, backend.gcd p q ∣ p
  gcd_dvd_right : ∀ p q, backend.gcd p q ∣ q
  gcd_greatest : ∀ (p q d : R[X]), d ∣ p → d ∣ q → d ∣ backend.gcd p q
  gcd_map_greatest : ∀ (p q : R[X]) (g : (FractionRing R)[X]),
    g ∣ p.map (algebraMap R (FractionRing R)) →
    g ∣ q.map (algebraMap R (FractionRing R)) →
    g ∣ (backend.gcd p q).map (algebraMap R (FractionRing R))
  exactDiv_mul : ∀ (p d : R[X]), d ≠ 0 → d ∣ p → d * backend.exactDiv p d = p
  resultant_eq : ∀ p q : R[X][X], p ≠ 0 → q ≠ 0 →
    ∃ c : R, c ≠ 0 ∧ backend.resultant p q = C c * Polynomial.resultant p q
  mem_naturalRoots : ∀ p : R[X], p ≠ 0 → ∀ j : ℕ,
    j ∈ backend.naturalRoots p ↔ p.eval (j : R) = 0

/-- The common divisor of a nonzero polynomial cannot vanish. -/
theorem NormalizationBackend.gcd_ne_zero (backend : NormalizationBackend R)
    (hbackend : backend.Valid) (p q : R[X]) (hp : p ≠ 0) : backend.gcd p q ≠ 0 := by
  intro hd
  obtain ⟨a, ha⟩ := hbackend.gcd_dvd_left p q
  exact hp (by simpa [hd] using ha)

/-- The greatest-divisor contract is equivalent to the usual gcd up to a unit. -/
theorem NormalizationBackend.gcd_map_associated [DecidableEq (FractionRing R)]
    (backend : NormalizationBackend R) (hbackend : backend.Valid) (p q : R[X]) :
    Associated ((backend.gcd p q).map (algebraMap R (FractionRing R)))
      (GCDMonoid.gcd (p.map (algebraMap R (FractionRing R)))
        (q.map (algebraMap R (FractionRing R)))) := by
  apply associated_of_dvd_dvd
  · exact dvd_gcd
      ((Polynomial.mapRingHom _).map_dvd (hbackend.gcd_dvd_left p q))
      ((Polynomial.mapRingHom _).map_dvd (hbackend.gcd_dvd_right p q))
  · exact hbackend.gcd_map_greatest p q _ (gcd_dvd_left _ _) (gcd_dvd_right _ _)

/-- Exact cancellation of a greatest common divisor leaves coprime polynomials
in the fraction field; this follows from the primitive divisor contracts. -/
theorem NormalizationBackend.exactDiv_gcd_isCoprime (backend : NormalizationBackend R)
    (hbackend : backend.Valid) (p q : R[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    IsCoprime
      ((backend.exactDiv p (backend.gcd p q)).map (algebraMap R (FractionRing R)))
      ((backend.exactDiv q (backend.gcd p q)).map (algebraMap R (FractionRing R))) := by
  let i := algebraMap R (FractionRing R)
  let d := backend.gcd p q
  have hd : d ≠ 0 := backend.gcd_ne_zero hbackend p q hp
  have hdi : d.map i ≠ 0 := (Polynomial.map_ne_zero_iff (IsFractionRing.injective R _)).mpr hd
  have hpi : p.map i = d.map i * (backend.exactDiv p d).map i := by
    simpa only [Polynomial.map_mul] using
      congrArg (Polynomial.map i) (hbackend.exactDiv_mul p d hd (hbackend.gcd_dvd_left p q)).symm
  have hqi : q.map i = d.map i * (backend.exactDiv q d).map i := by
    simpa only [Polynomial.map_mul] using
      congrArg (Polynomial.map i) (hbackend.exactDiv_mul q d hd (hbackend.gcd_dvd_right p q)).symm
  apply isCoprime_of_dvd
  · rintro ⟨_, hz⟩
    have hq' : q.map i ≠ 0 :=
      (Polynomial.map_ne_zero_iff (IsFractionRing.injective R _)).mpr hq
    exact hq' (by rw [hqi, hz, mul_zero])
  · intro e he _ hep heq
    have hdiv : d.map i * e ∣ d.map i := hbackend.gcd_map_greatest p q _
      (by rw [hpi]; exact mul_dvd_mul_left _ hep)
      (by rw [hqi]; exact mul_dvd_mul_left _ heq)
    have he1 : e ∣ 1 := (mul_dvd_mul_iff_left hdi).mp (by simpa using hdiv)
    exact he (isUnit_iff_dvd_one.mpr he1)

/-- The general resultant contract applies to Gosper's translated inputs. -/
theorem NormalizationBackend.resultant_shift_eq (backend : NormalizationBackend R)
    (hbackend : backend.Valid) (p q : R[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ c : R, c ≠ 0 ∧
      backend.resultant (p.map (Polynomial.C : R →+* R[X]))
        (taylor (X : R[X]) (q.map (Polynomial.C : R →+* R[X]))) =
        C c * sylvesterShiftResultant p q := by
  have hp' : p.map (Polynomial.C : R →+* R[X]) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Polynomial.C_injective).mpr hp
  have hq' : taylor (X : R[X]) (q.map (Polynomial.C : R →+* R[X])) ≠ 0 :=
    (Polynomial.taylor_eq_zero _ _).not.mpr
      ((Polynomial.map_ne_zero_iff Polynomial.C_injective).mpr hq)
  obtain ⟨c, hc, he⟩ := hbackend.resultant_eq _ _ hp' hq'
  refine ⟨c, hc, ?_⟩
  simpa [sylvesterShiftResultant,
    natDegree_map_eq_of_injective Polynomial.C_injective] using he

/-- The resultant used to detect shifts is nonzero for nonzero input polynomials. -/
theorem NormalizationBackend.resultant_shift_ne_zero (backend : NormalizationBackend R)
    (hbackend : backend.Valid) (p q : R[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    backend.resultant (p.map (Polynomial.C : R →+* R[X]))
      (taylor (X : R[X]) (q.map (Polynomial.C : R →+* R[X]))) ≠ 0 := by
  obtain ⟨c, hc, he⟩ := backend.resultant_shift_eq hbackend p q hp hq
  rw [he]
  exact mul_ne_zero (C_ne_zero.mpr hc) (sylvesterShiftResultant_ne_zero p q hp hq)

/-- Natural roots of the translated resultant detect exactly the noncoprime shifts
in the fraction field. This criterion follows from the two primitive contracts. -/
theorem NormalizationBackend.mem_naturalRoots_shiftResultant
    (backend : NormalizationBackend R) (hbackend : backend.Valid)
    (p q : R[X]) (hp : p ≠ 0) (hq : q ≠ 0) (j : ℕ) :
    j ∈ backend.naturalRoots
      (backend.resultant (p.map (Polynomial.C : R →+* R[X]))
        (taylor (X : R[X]) (q.map (Polynomial.C : R →+* R[X])))) ↔
      ¬IsCoprime (p.map (algebraMap R (FractionRing R)))
        (taylor (j : FractionRing R) (q.map (algebraMap R (FractionRing R)))) := by
  rw [hbackend.mem_naturalRoots _ (backend.resultant_shift_ne_zero hbackend p q hp hq)]
  obtain ⟨c, hc, he⟩ := backend.resultant_shift_eq hbackend p q hp hq
  rw [he, eval_mul, eval_C, mul_eq_zero]
  simp only [hc, false_or]
  simpa using sylvesterShiftResultant_zero_iff p q hp hq (j : ℤ)

/-- Use the usual field-polynomial gcd and division, and the backend's resultant
and factorization operations for shift detection. -/
noncomputable def Backend.toNormalization {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    [DecidablePred (IsInteger ℤ : K → Prop)] (backend : Backend K) : NormalizationBackend K where
  gcd p q := gcd p q
  exactDiv p d := p / d
  resultant := backend.resultant
  naturalRoots := backend.naturalRoots

private theorem polynomial_fractionRing_map_back {K : Type*} [Field K]
    (p : (FractionRing K)[X]) :
    (p.map (FractionRing.algEquiv K K).toRingHom).map
      (algebraMap K (FractionRing K)) = p := by
  ext n
  simp only [coeff_map]
  have h := (FractionRing.algEquiv K K).symm_apply_apply (p.coeff n)
  have hc := (FractionRing.algEquiv K K).symm.commutes
    (FractionRing.algEquiv K K (p.coeff n))
  simpa using hc.symm.trans h

private theorem polynomial_fractionRing_map {K : Type*} [Field K] (p : K[X]) :
    (p.map (algebraMap K (FractionRing K))).map
      (FractionRing.algEquiv K K).toRingHom = p := by
  ext n
  simp

/-- A valid field backend satisfies the ring normalization contract. -/
theorem Backend.toNormalization_valid {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    [DecidablePred (IsInteger ℤ : K → Prop)] (backend : Backend K)
    (hbackend : backend.Valid) : backend.toNormalization.Valid where
  gcd_dvd_left p q := gcd_dvd_left p q
  gcd_dvd_right p q := gcd_dvd_right p q
  gcd_greatest _ _ _ hp hq := dvd_gcd hp hq
  gcd_map_greatest p q g hgp hgq := by
    have hp : g.map (FractionRing.algEquiv K K).toRingHom ∣ p := by
      have h := (Polynomial.mapRingHom (FractionRing.algEquiv K K).toRingHom).map_dvd hgp
      change g.map (FractionRing.algEquiv K K).toRingHom ∣
        (p.map (algebraMap K (FractionRing K))).map
          (FractionRing.algEquiv K K).toRingHom at h
      rwa [polynomial_fractionRing_map] at h
    have hq : g.map (FractionRing.algEquiv K K).toRingHom ∣ q := by
      have h := (Polynomial.mapRingHom (FractionRing.algEquiv K K).toRingHom).map_dvd hgq
      change g.map (FractionRing.algEquiv K K).toRingHom ∣
        (q.map (algebraMap K (FractionRing K))).map
          (FractionRing.algEquiv K K).toRingHom at h
      rwa [polynomial_fractionRing_map] at h
    have h := (Polynomial.mapRingHom (algebraMap K (FractionRing K))).map_dvd (dvd_gcd hp hq)
    change (g.map (FractionRing.algEquiv K K).toRingHom).map
      (algebraMap K (FractionRing K)) ∣ (gcd p q).map (algebraMap K (FractionRing K)) at h
    rw [polynomial_fractionRing_map_back] at h
    exact h

  exactDiv_mul p d hd hdp := EuclideanDomain.mul_div_cancel' hd hdp
  resultant_eq := hbackend.resultant_eq
  mem_naturalRoots := backend.mem_naturalRoots hbackend

end Gosper.Algorithm
