module

public import SympyProofs.Gosper.Basic

/-! # Existence of Gosper normal form, equations (5), (6), and (6') -/

@[expose] public section
noncomputable section

namespace Gosper

open Polynomial

variable {K : Type*} [Field K]

/-- The resultant test mentioned after (6'): its zeros are exactly the
shifts at which a common factor must be removed. -/
theorem shiftCoprime_iff_resultant (q r : K[X]) (hq : q ≠ 0) :
    ShiftCoprime q r ↔ ∀ j : ℕ, q.resultant (taylor (j : K) r) ≠ 0 := by
  simp only [ShiftCoprime, ne_eq, resultant_eq_zero_iff, hq, not_false_eq_true,
    true_or, true_and, not_not]

/-- The product inserted into `p` by the change of variables (6'). -/
def shiftProduct (g : K[X]) (j : ℕ) : K[X] :=
  ∏ i ∈ Finset.range j, taylor (-(i : K)) g

@[simp] theorem shiftProduct_zero (g : K[X]) : shiftProduct g 0 = 1 := by
  simp [shiftProduct]

theorem shiftProduct_succ (g : K[X]) (j : ℕ) :
    shiftProduct g (j + 1) = shiftProduct g j * taylor (-(j : K)) g := by
  simp [shiftProduct, Finset.prod_range_succ]

theorem shiftProduct_ne_zero (g : K[X]) (hg : g ≠ 0) (j : ℕ) :
    shiftProduct g j ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun i _ => (taylor_eq_zero _ _).not.mpr hg

/-- The telescoping product identity underlying (6'). -/
theorem shiftProduct_identity (g : K[X]) (j : ℕ) :
    shiftProduct g j * taylor (-(j : K)) g = taylor (-1) (shiftProduct g j) * g := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [shiftProduct_succ, taylor_mul, taylor_taylor, ih]
    have h : -(↑(j + 1) : K) = -1 + -(j : K) := by push_cast; ring
    rw [h]
    ring

/-- One cancellation preserves the cross-multiplied term ratio. -/
theorem normalization_step (p g q r : K[X]) (j : ℕ) :
    (p * (g * q)) * (taylor (-1) (p * shiftProduct g j) * r) =
      (taylor (-1) p * (taylor (-(j : K)) g * r)) *
        ((p * shiftProduct g j) * q) := by
  rw [taylor_mul]
  have h := shiftProduct_identity g j
  linear_combination -(p * taylor (-1) p * q * r) * h

/-- Every quotient of nonzero polynomials admits the normal form (5)–(6).
The induction decreases the numerator degree at each cancellation, so it also
proves termination of the abstract cancellation procedure. -/
theorem exists_normalForm (A B : K[X]) (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ p q r : K[X], p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ ShiftCoprime q r ∧
      A * (taylor (-1) p * r) = B * (p * q) := by
  classical
  induction hn : A.natDegree using Nat.strong_induction_on generalizing A B with
  | h n ih =>
    by_cases hnorm : ShiftCoprime A B
    · exact ⟨1, A, B, one_ne_zero, hA, hB, hnorm, by simp [mul_comm]⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, ¬IsCoprime A (taylor (j : K) B) := by
      simpa only [ShiftCoprime, not_forall] using hnorm
    have hex : ∃ g : K[X], ¬IsUnit g ∧ g ≠ 0 ∧ g ∣ A ∧ g ∣ taylor (j : K) B := by
      by_contra hn
      apply hj
      apply isCoprime_of_dvd A (taylor (j : K) B) (fun h => hA h.1)
      intro g hgu hg0 hgA hgB
      exact hn ⟨g, hgu, hg0, hgA, hgB⟩
    obtain ⟨g, hgu, hg, ⟨Q, hQ⟩, ⟨T, hT⟩⟩ := hex
    let R := taylor (-(j : K)) T
    have hR : B = taylor (-(j : K)) g * R := by
      have h := congrArg (taylor (-(j : K))) hT
      simpa [taylor_taylor, taylor_mul, R] using h
    have hQ0 : Q ≠ 0 := by intro h; simp [h] at hQ; exact hA hQ
    have hR0 : R ≠ 0 := by intro h; simp [h] at hR; exact hB hR
    have hgdeg : 0 < g.natDegree := by
      by_contra h
      have hdeg : g.natDegree = 0 := by omega
      apply hgu
      apply isUnit_iff_degree_eq_zero.mpr
      rw [degree_eq_natDegree hg, hdeg]
      rfl
    have hlt : Q.natDegree < n := by
      have hdeg := natDegree_mul hg hQ0
      rw [← hQ, hn] at hdeg
      omega
    obtain ⟨p, q, r, hp, hq, hr, hnorm, he⟩ := ih Q.natDegree hlt Q R hQ0 hR0 rfl
    refine ⟨shiftProduct g j * p, q, r, mul_ne_zero (shiftProduct_ne_zero g hg j) hp,
      hq, hr, hnorm, ?_⟩
    rw [hQ, hR, taylor_mul]
    have hs := shiftProduct_identity g j
    calc
      (g * Q) * (taylor (-1) (shiftProduct g j) * taylor (-1) p * r) =
          (g * taylor (-1) (shiftProduct g j)) * (Q * (taylor (-1) p * r)) := by ring
      _ = (shiftProduct g j * taylor (-(j : K)) g) * (R * (p * q)) := by
        rw [he, mul_comm g, ← hs]
      _ = (taylor (-(j : K)) g * R) * (shiftProduct g j * p * q) := by ring

end Gosper
