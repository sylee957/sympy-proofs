module

public import SympyProofs.Sum.Gosper.Algorithm.Polynomial

/-! Gosper's shift resultant is an interpretation of the general resultant primitive.
Its root criterion follows from the primitive's contract, allowing a different sign. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type*} [Field K]

/-- Res_X(p(X), q(X+h)), as a polynomial in h. In `R[X][X]` the inner
variable is h and the outer variable is X. Mathlib computes the resultant. -/
def sylvesterShiftResultant {R : Type*} [CommRing R] (p q : R[X]) : R[X] :=
  Polynomial.resultant (p.map (Polynomial.C : R →+* R[X]))
    (taylor (X : R[X]) (q.map (Polynomial.C : R →+* R[X])))
    p.natDegree q.natDegree

theorem sylvesterShiftResultant_eval {R : Type*} [CommRing R] (p q : R[X]) (a : R) :
    (sylvesterShiftResultant p q).eval a =
      Polynomial.resultant p (taylor a q) p.natDegree q.natDegree := by
  have hc : (Polynomial.evalRingHom a).comp (Polynomial.C : R →+* R[X]) = RingHom.id R := by
    ext c
    exact Polynomial.eval_C
  have h := Polynomial.resultant_map_map
    (p.map (Polynomial.C : R →+* R[X]))
    (taylor (X : R[X]) (q.map (Polynomial.C : R →+* R[X])))
    p.natDegree q.natDegree (Polynomial.evalRingHom a)
  change (Polynomial.evalRingHom a) _ = _
  unfold sylvesterShiftResultant
  rw [← h]
  congr 1 <;> simp [Polynomial.map_map, hc]

theorem sylvesterShiftResultant_map_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (p q : R[X]) :
    (sylvesterShiftResultant p q).map f = sylvesterShiftResultant (p.map f) (q.map f) := by
  unfold sylvesterShiftResultant
  have h := Polynomial.resultant_map_map (p.map (Polynomial.C : R →+* R[X]))
    (taylor (X : R[X]) (q.map (Polynomial.C : R →+* R[X])))
    p.natDegree q.natDegree (Polynomial.mapRingHom f)
  change (Polynomial.mapRingHom f) _ = _
  rw [← h]
  congr 1 <;> simp [Polynomial.map_map, Polynomial.mapRingHom_comp_C,
    Polynomial.natDegree_map_eq_of_injective hf]

theorem sylvesterShiftResultant_map {L : Type*} [Field L] (f : K →+* L) (p q : K[X]) :
    (sylvesterShiftResultant p q).map f = sylvesterShiftResultant (p.map f) (q.map f) :=
  sylvesterShiftResultant_map_of_injective f f.injective p q

theorem sylvesterShiftResultant_ne_zero_of_splits (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (hs : p.Splits) : sylvesterShiftResultant p q ≠ 0 := by
  have hpC : p.map (Polynomial.C : K →+* K[X]) ≠ 0 := by simpa using hp
  unfold sylvesterShiftResultant
  rw [← Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective (p := p)]
  rw [Polynomial.resultant_eq_prod_eval _ _ _ (by simp) (hs.map _)]
  apply mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hpC))
  rw [hs.roots_map (Polynomial.C : K →+* K[X]), Multiset.map_map]
  apply Multiset.prod_ne_zero
  intro hz
  obtain ⟨a, _, he⟩ := Multiset.mem_map.mp hz
  have hn : ((taylor (X : K[X]) (q.map Polynomial.C)).eval (Polynomial.C a)) ≠ 0 := by
    simp only [taylor_eval, Polynomial.eval_map]
    change q.comp (Polynomial.C a + X) ≠ 0
    rw [add_comm]
    exact (Polynomial.taylor_eq_zero a q).not.mpr hq
  exact hn he

private theorem sylvesterShiftResultant_ne_zero_field (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    sylvesterShiftResultant p q ≠ 0 := by
  let f := algebraMap K (AlgebraicClosure K)
  have h := sylvesterShiftResultant_ne_zero_of_splits (p.map f) (q.map f)
    (by simpa using hp) (by simpa using hq) (IsAlgClosed.splits _)
  rw [← sylvesterShiftResultant_map f] at h
  exact fun hz => h (by rw [hz, Polynomial.map_zero])

/-- Translation makes the shift resultant nonzero for nonzero inputs over any integral domain. -/
theorem sylvesterShiftResultant_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (p q : R[X]) (hp : p ≠ 0) (hq : q ≠ 0) : sylvesterShiftResultant p q ≠ 0 := by
  let f := algebraMap R (FractionRing R)
  have hf : Function.Injective f := IsFractionRing.injective R (FractionRing R)
  have h := sylvesterShiftResultant_ne_zero_field (p.map f) (q.map f)
    ((Polynomial.map_ne_zero_iff hf).mpr hp) ((Polynomial.map_ne_zero_iff hf).mpr hq)
  rw [← sylvesterShiftResultant_map_of_injective f hf] at h
  exact fun hz => h (by rw [hz, Polynomial.map_zero])

/-- A root of the shift resultant detects a common factor after passing to the fraction field. -/
theorem sylvesterShiftResultant_eval_zero_iff {R : Type*} [CommRing R] [IsDomain R]
    (p q : R[X]) (hp : p ≠ 0) (_hq : q ≠ 0) (a : R) :
    (sylvesterShiftResultant p q).eval a = 0 ↔
      ¬IsCoprime (p.map (algebraMap R (FractionRing R)))
        (taylor (algebraMap R (FractionRing R) a) (q.map (algebraMap R (FractionRing R)))) := by
  let f := algebraMap R (FractionRing R)
  have hf : Function.Injective f := IsFractionRing.injective R (FractionRing R)
  have hp' : p.map f ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hp
  have he : (sylvesterShiftResultant (p.map f) (q.map f)).eval (f a) =
      f ((sylvesterShiftResultant p q).eval a) := by
    rw [← sylvesterShiftResultant_map_of_injective f hf, Polynomial.eval_map_apply]
  rw [← map_eq_zero_iff f hf, ← he, sylvesterShiftResultant_eval]
  simpa [hp'] using
    (Polynomial.resultant_eq_zero_iff (f := p.map f) (g := taylor (f a) (q.map f)))

/-- Signed integer roots are exactly the shifts with a common factor in the fraction field. -/
theorem sylvesterShiftResultant_zero_iff {R : Type*} [CommRing R] [IsDomain R]
    (p q : R[X]) (hp : p ≠ 0) (hq : q ≠ 0) (j : ℤ) :
    (sylvesterShiftResultant p q).eval (j : R) = 0 ↔
      ¬IsCoprime (p.map (algebraMap R (FractionRing R)))
        (taylor (j : FractionRing R) (q.map (algebraMap R (FractionRing R)))) := by
  simpa using sylvesterShiftResultant_eval_zero_iff p q hp hq (j : R)

end Gosper.Algorithm
