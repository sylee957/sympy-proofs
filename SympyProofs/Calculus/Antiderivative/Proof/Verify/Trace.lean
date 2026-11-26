module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.BigOperators.Field

/-! The coefficient trace formula in a split squarefree quotient, by Lagrange interpolation. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Polynomial

variable {F k : Type*} [Field F] [Field k]

/-- The coefficient of degree one below the modulus degree computes the sum of the values
at its distinct roots, after multiplication by the derivative and reduction modulo the modulus. -/
theorem coefficient_trace {ι : Type*} {s : Finset ι} {z : ι → F} (hz : Set.InjOn z s)
    {a : F} (ha : a ≠ 0) {p q : F[X]} (hp : p = C a * Lagrange.nodal s z)
    (hq : q.degree < s.card) (f : ι → F)
    (h : ∀ i ∈ s, q.eval (z i) = f i * p.derivative.eval (z i)) :
    q.coeff (s.card - 1) / a = ∑ i ∈ s, f i := by
  classical
  rw [Lagrange.coeff_eq_sum hz hq, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i hi,hp,derivative_C_mul,eval_mul,eval_C,Lagrange.eval_nodal_derivative_eval_node_eq hi,
    Lagrange.eval_nodal]
  have hn : (∏ j ∈ s.erase i, (z i - z j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    obtain ⟨hji,hjs⟩ := Finset.mem_erase.mp hj
    exact sub_ne_zero.mpr fun eq => hji (hz hjs hi eq.symm)
  field_simp

/-- The squarefree modulus over an algebraically closed field factors into its distinct
linear factors after any coefficient embedding. -/
theorem map_eq_nodal [DecidableEq k] [CharZero k] [IsAlgClosed k]
    (ι : k →+* F) {p : k[X]} (hp : Squarefree p) :
    p.map ι = C (ι p.leadingCoeff) * Lagrange.nodal p.roots.toFinset ι := by
  classical
  have hd := Polynomial.nodup_roots (PerfectField.separable_iff_squarefree.mpr hp)
  have he := congrArg (Polynomial.map ι) (IsAlgClosed.splits p).eq_prod_roots
  rw [Polynomial.map_mul,Polynomial.map_C] at he
  rw [Lagrange.nodal,Finset.prod_eq_multiset_prod,Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr hd]
  rw [he]
  congr 1
  change (mapRingHom ι) _ = _
  rw [map_multiset_prod,Multiset.map_map]
  simp

end SympyProofs.Calculus.Antiderivative
