module

public import SympyProofs.Sum.Gosper.Backend.Descent

/-! Properties of the normalization primitives supplied by the Gosper backend. -/

@[expose] public section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K R : Type*} [CommRing K] [IsDomain K] [CommRing R] [IsDomain R] [Algebra K R]

/-- Multiplying the resultant by a nonzero coefficient preserves validity. -/
theorem TermBackend.Valid.scaleResultant {backend : TermBackend K R} (h : backend.Valid)
    (c : R) (hc : c ≠ 0) :
    ({ backend with resultant := fun p q => C c * backend.resultant p q } : TermBackend K R).Valid := by
  refine { h with resultant_eq := ?_ }
  intro p q hp hq
  obtain ⟨d, hd, he⟩ := h.resultant_eq p q hp hq
  exact ⟨c * d, mul_ne_zero hc hd, by simp [he, map_mul, mul_assoc]⟩

/-- The common divisor of a nonzero polynomial cannot vanish. -/
theorem TermBackend.gcd_ne_zero (backend : TermBackend K R)
    (hbackend : backend.Valid) (p q : R[X]) (hp : p ≠ 0) : backend.gcd p q ≠ 0 := by
  intro hd
  obtain ⟨a, ha⟩ := hbackend.gcd_dvd_left p q
  exact hp (by simpa [hd] using ha)

/-- Gcds of constant polynomials induce gcds in the coefficient domain. -/
private theorem TermBackend.isGCDMonoid (backend : TermBackend K R) (hbackend : backend.Valid) :
    IsGCDMonoid R := by
  classical
  let d (a b : R) := (backend.gcd (C a) (C b)).eval 0
  apply IsGCDMonoid.intro
  apply gcdMonoidOfGCD d
  · intro a b
    have h := (Polynomial.evalRingHom (0 : R)).map_dvd (hbackend.gcd_dvd_left (C a) (C b))
    simpa [d] using h
  · intro a b
    have h := (Polynomial.evalRingHom (0 : R)).map_dvd (hbackend.gcd_dvd_right (C a) (C b))
    simpa [d] using h
  · intro c b a hca hcb
    have h := hbackend.gcd_greatest (C a) (C b) (C c)
      ((Polynomial.C : R →+* R[X]).map_dvd hca)
      ((Polynomial.C : R →+* R[X]).map_dvd hcb)
    have h' := (Polynomial.evalRingHom (0 : R)).map_dvd h
    simpa [d] using h'

/-- A backend gcd remains greatest after mapping to the fraction field. -/
theorem TermBackend.gcd_map_greatest (backend : TermBackend K R)
    (hbackend : backend.Valid) (p q : R[X]) (g : (FractionRing R)[X])
    (hgp : g ∣ p.map (algebraMap R (FractionRing R)))
    (hgq : g ∣ q.map (algebraMap R (FractionRing R))) :
    g ∣ (backend.gcd p q).map (algebraMap R (FractionRing R)) := by
  classical
  let : IsGCDMonoid R := backend.isGCDMonoid hbackend
  let : NormalizedGCDMonoid R := Classical.arbitrary _
  let i := algebraMap R (FractionRing R)
  by_cases hg : g = 0
  · have hp : p = 0 := by
      apply Polynomial.map_injective i (IsFractionRing.injective R _)
      simpa [hg] using (zero_dvd_iff.mp (hg ▸ hgp))
    have hq : q = 0 := by
      apply Polynomial.map_injective i (IsFractionRing.injective R _)
      simpa [hg] using (zero_dvd_iff.mp (hg ▸ hgq))
    have hd : backend.gcd p q = 0 := by
      apply zero_dvd_iff.mp
      exact hbackend.gcd_greatest p q 0 (by simp [hp]) (by simp [hq])
    simp [hg, hd]
  -- Clear denominators and take the primitive part in the coefficient domain.
  let v : R[X] := IsLocalization.integerNormalization (nonZeroDivisors R) g
  let w := v.primPart
  have hv : v ≠ 0 := by
    change IsLocalization.integerNormalization (nonZeroDivisors R) g ≠ 0
    exact IsFractionRing.integerNormalization_eq_zero_iff.not.mpr hg
  have hcontent : v.content ≠ 0 := content_eq_zero_iff.not.mpr hv
  obtain ⟨b, hb, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) g
  have hi : Function.Injective i := IsFractionRing.injective R (FractionRing R)
  have hb0 : i b ≠ 0 := fun hz => nonZeroDivisors.ne_zero hb ((map_eq_zero_iff i hi).mp hz)
  have hc0 : i v.content ≠ 0 := fun hz => hcontent ((map_eq_zero_iff i hi).mp hz)
  have hbunit : IsUnit (C (i b) : (FractionRing R)[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb0)
  have hcunit : IsUnit (C (i v.content) : (FractionRing R)[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
  have he' : v.map i = C (i b) * g := by
    change v.map i = b • g at he
    rw [Algebra.smul_def, Polynomial.algebraMap_apply] at he
    exact he
  have hwmap : w.map i ∣ v.map i :=
    (Polynomial.mapRingHom i).map_dvd v.primPart_dvd
  have hvp : v.map i ∣ p.map i := by
    rw [he', hbunit.mul_left_dvd]
    exact hgp
  have hvq : v.map i ∣ q.map i := by
    rw [he', hbunit.mul_left_dvd]
    exact hgq
  -- Gauss's lemma brings the primitive common divisor back to R[X].
  have hwp : w ∣ p :=
    v.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hwmap.trans hvp)
  have hwq : w ∣ q :=
    v.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hwmap.trans hvq)
  have hwd : w ∣ backend.gcd p q := hbackend.gcd_greatest p q w hwp hwq
  have hgv : g ∣ v.map i := by
    rw [he']
    exact dvd_mul_left g _
  have hprod : g ∣ C (i v.content) * w.map i := by
    have hvprod : v.map i = C (i v.content) * w.map i := by
      calc
        v.map i = (C v.content * w).map i :=
          congrArg (Polynomial.map i) v.eq_C_content_mul_primPart
        _ = _ := by rw [Polynomial.map_mul, Polynomial.map_C]
    rw [← hvprod]
    exact hgv
  exact (hcunit.dvd_mul_left.mp hprod).trans ((Polynomial.mapRingHom i).map_dvd hwd)

/-- The greatest-divisor contract is equivalent to the usual gcd up to a unit. -/
theorem TermBackend.gcd_map_associated [DecidableEq (FractionRing R)]
    (backend : TermBackend K R) (hbackend : backend.Valid) (p q : R[X]) :
    Associated ((backend.gcd p q).map (algebraMap R (FractionRing R)))
      (GCDMonoid.gcd (p.map (algebraMap R (FractionRing R)))
        (q.map (algebraMap R (FractionRing R)))) := by
  apply associated_of_dvd_dvd
  · exact dvd_gcd
      ((Polynomial.mapRingHom _).map_dvd (hbackend.gcd_dvd_left p q))
      ((Polynomial.mapRingHom _).map_dvd (hbackend.gcd_dvd_right p q))
  · exact backend.gcd_map_greatest hbackend p q _ (gcd_dvd_left _ _) (gcd_dvd_right _ _)

/-- Exact cancellation of a greatest common divisor leaves coprime polynomials
in the fraction field; this follows from the primitive divisor contracts. -/
theorem TermBackend.exactDiv_gcd_isCoprime (backend : TermBackend K R)
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
    have hdiv : d.map i * e ∣ d.map i := backend.gcd_map_greatest hbackend p q _
      (by rw [hpi]; exact mul_dvd_mul_left _ hep)
      (by rw [hqi]; exact mul_dvd_mul_left _ heq)
    have he1 : e ∣ 1 := (mul_dvd_mul_iff_left hdi).mp (by simpa using hdiv)
    exact he (isUnit_iff_dvd_one.mpr he1)

/-- The general resultant contract applies to Gosper's translated inputs. -/
theorem TermBackend.resultant_shift_eq (backend : TermBackend K R)
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
theorem TermBackend.resultant_shift_ne_zero (backend : TermBackend K R)
    (hbackend : backend.Valid) (p q : R[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    backend.resultant (p.map (Polynomial.C : R →+* R[X]))
      (taylor (X : R[X]) (q.map (Polynomial.C : R →+* R[X]))) ≠ 0 := by
  obtain ⟨c, hc, he⟩ := backend.resultant_shift_eq hbackend p q hp hq
  rw [he]
  exact mul_ne_zero (C_ne_zero.mpr hc) (sylvesterShiftResultant_ne_zero p q hp hq)

/-- Natural roots of the translated resultant detect exactly the noncoprime shifts
in the fraction field. This criterion follows from the two primitive contracts. -/
theorem TermBackend.mem_naturalRoots_shiftResultant
    (backend : TermBackend K R) (hbackend : backend.Valid)
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

/-- Sorting the detected shifts does not change the shift criterion. -/
theorem TermBackend.mem_shifts (backend : TermBackend K R) (hbackend : backend.Valid)
    (p q : R[X]) (hp : p ≠ 0) (hq : q ≠ 0) (j : ℕ) :
    j ∈ (backend.naturalRoots
      (backend.resultant (p.map (Polynomial.C : R →+* R[X]))
        (taylor (X : R[X]) (q.map (Polynomial.C : R →+* R[X]))))).sort (· ≤ ·) ↔
      ¬IsCoprime (p.map (algebraMap R (FractionRing R)))
        (taylor (j : FractionRing R) (q.map (algebraMap R (FractionRing R)))) := by
  simpa only [Finset.mem_sort] using
    backend.mem_naturalRoots_shiftResultant hbackend p q hp hq j

end Gosper.Algorithm
