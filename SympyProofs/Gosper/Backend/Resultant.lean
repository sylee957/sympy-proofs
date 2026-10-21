module

public import SympyProofs.Gosper.Backend.Basic

/-! Gosper's shift resultant is an interpretation of the general resultant primitive.
Its root criterion follows from the primitive's contract, allowing a different sign. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type*} [Field K]

/-- Construct the bivariate inputs and eliminate the summation variable.
In `K[X][X]`, the inner variable is the shift and the outer one is eliminated. -/
def Backend.shiftResultant (backend : Backend K) (p q : K[X]) : K[X] :=
  backend.resultant (p.map (Polynomial.C : K →+* K[X]))
    (taylor (X : K[X]) (q.map (Polynomial.C : K →+* K[X])))

/-- Res_X(p(X), q(X+h)), as a polynomial in h. In `K[X][X]` the inner
variable is h and the outer variable is X. Mathlib computes the resultant. -/
def sylvesterShiftResultant (p q : K[X]) : K[X] :=
  Polynomial.resultant (p.map (Polynomial.C : K →+* K[X]))
    (taylor (X : K[X]) (q.map (Polynomial.C : K →+* K[X])))
    p.natDegree q.natDegree

theorem sylvesterShiftResultant_eval (p q : K[X]) (a : K) :
    (sylvesterShiftResultant p q).eval a =
      Polynomial.resultant p (taylor a q) p.natDegree q.natDegree := by
  have hc : (Polynomial.evalRingHom a).comp (Polynomial.C : K →+* K[X]) = RingHom.id K := by
    ext c
    exact Polynomial.eval_C
  have h := Polynomial.resultant_map_map
    (p.map (Polynomial.C : K →+* K[X]))
    (taylor (X : K[X]) (q.map (Polynomial.C : K →+* K[X])))
    p.natDegree q.natDegree (Polynomial.evalRingHom a)
  change (Polynomial.evalRingHom a) _ = _
  unfold sylvesterShiftResultant
  rw [← h]
  congr 1 <;> simp [Polynomial.map_map, hc]

theorem sylvesterShiftResultant_map {L : Type*} [Field L] (f : K →+* L) (p q : K[X]) :
    (sylvesterShiftResultant p q).map f = sylvesterShiftResultant (p.map f) (q.map f) := by
  unfold sylvesterShiftResultant
  have h := Polynomial.resultant_map_map (p.map (Polynomial.C : K →+* K[X]))
    (taylor (X : K[X]) (q.map (Polynomial.C : K →+* K[X])))
    p.natDegree q.natDegree (Polynomial.mapRingHom f)
  change (Polynomial.mapRingHom f) _ = _
  rw [← h]
  congr 1 <;> simp [Polynomial.map_map, Polynomial.mapRingHom_comp_C,
    Polynomial.natDegree_map_eq_of_injective f.injective]

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

theorem sylvesterShiftResultant_ne_zero (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    sylvesterShiftResultant p q ≠ 0 := by
  let f := algebraMap K (AlgebraicClosure K)
  have h := sylvesterShiftResultant_ne_zero_of_splits (p.map f) (q.map f)
    (by simpa using hp) (by simpa using hq) (IsAlgClosed.splits _)
  rw [← sylvesterShiftResultant_map f] at h
  exact fun hz => h (by rw [hz, Polynomial.map_zero])

/-- The contract for arbitrary bivariate resultants specializes to Gosper's
translated inputs. Translation and the constant embedding preserve degree. -/
theorem Backend.shiftResultant_eq (backend : Backend K) (h : backend.Valid)
    (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ backend.shiftResultant p q = C c * sylvesterShiftResultant p q := by
  have hp' : p.map (Polynomial.C : K →+* K[X]) ≠ 0 := by simpa using hp
  have hq' : taylor (X : K[X]) (q.map (Polynomial.C : K →+* K[X])) ≠ 0 := by
    simpa using hq
  obtain ⟨c, hc, he⟩ := h.resultant_eq _ _ hp' hq'
  refine ⟨c, hc, ?_⟩
  simpa [Backend.shiftResultant, sylvesterShiftResultant,
    natDegree_map_eq_of_injective Polynomial.C_injective] using he

theorem Backend.shiftResultant_ne_zero (backend : Backend K) (h : backend.Valid)
    (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) : backend.shiftResultant p q ≠ 0 := by
  obtain ⟨c, hc, he⟩ := backend.shiftResultant_eq h p q hp hq
  rw [he]
  exact mul_ne_zero (C_ne_zero.mpr hc) (sylvesterShiftResultant_ne_zero p q hp hq)

theorem Backend.shiftResultant_zero_iff (backend : Backend K) (h : backend.Valid)
    (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) (j : ℕ) :
    (backend.shiftResultant p q).eval (j : K) = 0 ↔ ¬IsCoprime p (taylor (j : K) q) := by
  obtain ⟨c, hc, he⟩ := backend.shiftResultant_eq h p q hp hq
  rw [he, eval_mul, eval_C, mul_eq_zero]
  simp only [hc, false_or, sylvesterShiftResultant_eval]
  simpa [hp] using (Polynomial.resultant_eq_zero_iff (f := p) (g := taylor (j : K) q))

/-- Both shift construction and root extraction are derived from primitive contracts. -/
theorem Backend.mem_shifts [DecidableEq K] [CharZero K] [DecidablePred (IsInteger ℤ : K → Prop)] (backend : Backend K) (h : backend.Valid)
    (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) (j : ℕ) :
    j ∈ (backend.nonnegativeIntegerRoots (backend.shiftResultant p q)).sort (· ≤ ·) ↔
      ¬IsCoprime p (taylor (j : K) q) := by
  rw [Finset.mem_sort, backend.mem_nonnegativeIntegerRoots h _
    (backend.shiftResultant_ne_zero h p q hp hq), backend.shiftResultant_zero_iff h p q hp hq]

end Gosper.Algorithm
