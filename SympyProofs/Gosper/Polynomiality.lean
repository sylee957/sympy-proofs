module

public import SympyProofs.Gosper.Basic

/-!
# Gosper's polynomiality theorem

The proof of the theorem on pp. 40–41 is expressed using the two endpoints of
a finite integer orbit of roots of the reduced denominator. This is the root
version of the paper's maximal-shift gcd argument (10a–10d).
-/

@[expose] public section

namespace Gosper

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

private theorem coprime_eval_ne {c d : K[X]} (h : IsCoprime c d) (z : K)
    (hd : d.eval z = 0) : c.eval z ≠ 0 := by
  rcases h with ⟨u, v, huv⟩
  intro hc
  have he := congrArg (fun p : K[X] => p.eval z) huv
  simp [hc, hd] at he

/-- A root has a final root in either direction along its integer orbit. -/
private theorem root_endpoint (d : K[X]) (hd : d ≠ 0) (z ε : K)
    (hε : ε ≠ 0) (hz : d.eval z = 0) :
    ∃ j : ℕ, d.eval (z + j * ε) = 0 ∧ d.eval (z + (j + 1) * ε) ≠ 0 := by
  classical
  have hi : Function.Injective (fun j : ℕ => z + (j : K) * ε) := by
    intro i j hij
    exact Nat.cast_injective (mul_right_cancel₀ hε (add_left_cancel hij))
  have hfin : Set.Finite {j : ℕ | d.eval (z + j * ε) = 0} :=
    (finite_setOfPred_isRoot hd).preimage hi.injOn
  obtain ⟨j, hj, hmax⟩ := hfin.exists_maximal ⟨0, by simpa using hz⟩
  refine ⟨j, hj, ?_⟩
  intro hn
  have hmem : j + 1 ∈ {j : ℕ | d.eval (z + j * ε) = 0} := by
    simpa only [Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one] using hn
  have := hmax hmem (Nat.le_succ j)
  omega

/-- The cleared-denominator form (8') forces the reduced denominator to be a
unit over an algebraically closed field of characteristic zero. -/
theorem denominator_isUnit_of_isAlgClosed [IsAlgClosed K]
    (p q r c d : K[X]) (hd : d ≠ 0) (hcd : IsCoprime c d)
    (hqr : ShiftCoprime q r)
    (he : d * taylor (-1) d * p =
      c * taylor (-1) d * taylor 1 q - d * taylor (-1) c * r) :
    IsUnit d := by
  by_contra hu
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root d
    (fun h => hu (isUnit_iff_degree_eq_zero.mpr h))
  obtain ⟨u, hu, hu1⟩ := root_endpoint d hd z 1 one_ne_zero hz
  let top := z + (u : K)
  have ht : d.eval top = 0 := by simpa [top] using hu
  have ht1 : d.eval (top + 1) ≠ 0 := by simpa [top, add_assoc] using hu1
  obtain ⟨j, hj, hj1⟩ := root_endpoint d hd top (-1) (neg_ne_zero.mpr one_ne_zero) ht
  let bot := top - (j : K)
  have hb : d.eval bot = 0 := by simpa [bot, sub_eq_add_neg] using hj
  have hb1 : d.eval (bot - 1) ≠ 0 := by
    convert hj1 using 1
    dsimp [bot]
    congr 1
    ring
  have hc := coprime_eval_ne hcd bot hb
  have hct := coprime_eval_ne hcd top ht
  have hq : q.eval (bot + 1) = 0 := by
    have h := congrArg (fun P : K[X] => P.eval bot) he
    simp only [eval_mul, eval_sub, taylor_eval] at h
    simp only [hb, zero_mul, sub_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left
      (mul_ne_zero hc (by simpa only [sub_eq_add_neg] using hb1))
  have hr : r.eval (top + 1) = 0 := by
    have h := congrArg (fun P : K[X] => P.eval (top + 1)) he
    simp only [eval_mul, eval_sub, taylor_eval] at h
    simp only [add_neg_cancel_right, ht, mul_zero, zero_mul, zero_sub] at h
    exact (mul_eq_zero.mp (neg_eq_zero.mp h.symm)).resolve_left (mul_ne_zero ht1 hct)
  have hrc : (taylor (j : K) r).eval (bot + 1) = 0 := by
    rw [taylor_eval]
    convert hr using 1
    dsimp [bot]
    congr 1
    ring
  exact coprime_eval_ne (hqr j) (bot + 1) hrc hq

/-- Gosper's denominator theorem over any characteristic-zero field, by
passing to its algebraic closure and reflecting polynomial degree. -/
theorem denominator_isUnit (p q r c d : K[X]) (hd : d ≠ 0)
    (hcd : IsCoprime c d) (hqr : ShiftCoprime q r)
    (he : d * taylor (-1) d * p =
      c * taylor (-1) d * taylor 1 q - d * taylor (-1) c * r) :
    IsUnit d := by
  let φ := algebraMap K (AlgebraicClosure K)
  have hi := φ.injective
  apply isUnit_iff_degree_eq_zero.mpr
  rw [← degree_map_eq_of_injective hi]
  apply isUnit_iff_degree_eq_zero.mp
  apply denominator_isUnit_of_isAlgClosed (p.map φ) (q.map φ) (r.map φ) (c.map φ) (d.map φ)
  · exact fun h => hd ((Polynomial.map_injective φ hi) (by simpa using h))
  · exact hcd.map (Polynomial.mapRingHom φ)
  · intro j
    simpa [map_taylor] using (hqr j).map (Polynomial.mapRingHom φ)
  · simpa only [Polynomial.map_mul, Polynomial.map_sub, map_taylor, map_neg, map_one]
      using congrArg (Polynomial.map φ) he

end Gosper
