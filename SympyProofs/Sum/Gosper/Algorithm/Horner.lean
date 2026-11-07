module

public import SympyProofs.Sum.Gosper.Backend.Elimination

/-! Proofs for polynomial reconstruction fused with fraction-free back substitution. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L] {n : ℕ}

abbrev FusedBackState (K L : Type*) [CommRing L] :=
  K × L[X] × ℕ × L[X] × L[X]

/-- The fraction-free coefficient update with polynomial storage. -/
def polynomialBackStep (state : K × L[X]) (step : EliminationStep K L n) : K × L[X] :=
  let value := algebraMap K L state.1 * step.2.2.2 -
    directDot (fun j : Fin n => step.2.2.1[j.val]) (fun j => state.2.coeff j.val)
  (step.2.1 * state.1,
    C (algebraMap K L step.2.1) * state.2 + monomial step.1.val value)

/-- One proof-model step of the fused back-substitution and Horner loop. -/
def fusedBackStep (A B : L[X]) (state : FusedBackState K L)
    (step : EliminationStep K L n) : FusedBackState K L :=
  let value := algebraMap K L state.1 * step.2.2.2 -
    directDot (fun j : Fin n => step.2.2.1[j.val]) (fun j => state.2.1.coeff j.val)
  let result := polynomialBackStep (state.1, state.2.1) step
  let gap := state.2.2.1 - step.1.val
  let scale := C (algebraMap K L step.2.1)
  let a := C value
  (result.1, result.2, step.1.val,
    scale * X ^ gap * state.2.2.2.1 + a * B,
    scale * (X + 1) ^ gap * state.2.2.2.2 + a * A)

/-- The fused loop as a proof-only expression; the solver executes the loop inline. -/
def fusedBackSub (steps : List (EliminationStep K L n)) (A B : L[X]) :
    K × L[X] × L[X] × L[X] := Id.run do
  let mut δ := (1 : K)
  let mut x : L[X] := 0
  let mut position := n
  let mut U : L[X] := 0
  let mut shifted : L[X] := 0
  for (col, p, row, pivotRhs) in steps do
    let value := algebraMap K L δ * pivotRhs -
      directDot (fun j : Fin n => row[j.val]) (fun j => x.coeff j.val)
    let scale := C (algebraMap K L p)
    x := scale * x + monomial col.val value
    δ := p * δ
    let gap := position - col.val
    let a := C value
    U := scale * X ^ gap * U + a * B
    shifted := scale * (X + 1) ^ gap * shifted + a * A
    position := col.val
  U := X ^ position * U
  shifted := (X + 1) ^ position * shifted
  return (δ, x, U, shifted)

theorem fusedBackSub_eq_fold (steps : List (EliminationStep K L n)) (A B : L[X]) :
    fusedBackSub steps A B =
      let state := steps.foldl (fusedBackStep A B) (1, 0, n, 0, 0)
      (state.1, state.2.1, X ^ state.2.2.1 * state.2.2.2.1,
        (X + 1) ^ state.2.2.1 * state.2.2.2.2) := by
  simp only [fusedBackSub, List.forIn_pure_yield_eq_foldl]
  rfl

/-- The fused loop leaves the denominator and polynomial update unchanged. -/
theorem fusedBackSub_base (steps : List (EliminationStep K L n)) (A B : L[X])
    (state : FusedBackState K L) :
    let final := steps.foldl (fusedBackStep A B) state
    (final.1, final.2.1) = steps.foldl polynomialBackStep (state.1, state.2.1) := by
  induction steps generalizing state with
  | nil => rfl
  | cons step steps ih =>
    simp only [List.foldl_cons]
    exact ih _

/-- Multiplication by the skipped powers preserves the current Horner value. -/
theorem horner_gap_step (T U F scale a : L[X]) (position col : ℕ)
    (h : col ≤ position) :
    T ^ col * (scale * T ^ (position - col) * U + a * F) =
      scale * (T ^ position * U) + a * T ^ col * F := by
  have hp : T ^ col * T ^ (position - col) = T ^ position := by
    rw [← pow_add, Nat.add_sub_of_le h]
  calc
    _ = scale * (T ^ col * T ^ (position - col)) * U + a * T ^ col * F := by ring
    _ = _ := by rw [hp]; ring

theorem eliminationBackStep_poly
    (step : EliminationStep K L n) (d : K) (x : Vector L n) (T : L[X]) :
    (∑ j : Fin n, C (eliminationBackStep step (d, x)).2[j.val] * T ^ j.val) =
      C (algebraMap K L step.2.1) * (∑ j : Fin n, C x[j.val] * T ^ j.val) +
        C (algebraMap K L d * step.2.2.2 -
          directDot (fun j : Fin n => step.2.2.1[j.val]) (fun j => x[j.val])) *
            T ^ step.1.val := by
  rcases step with ⟨c, p, row, rhs⟩
  have hentry (j : Fin n) :
      C (eliminationBackStep (c, p, row, rhs) (d, x)).2[j.val] * T ^ j.val =
        C (algebraMap K L p) * (C x[j.val] * T ^ j.val) +
          if j = c then
            C (algebraMap K L d * rhs -
              directDot (fun k : Fin n => row[k.val]) (fun k => x[k.val])) * T ^ j.val
          else 0 := by
    rw [eliminationBackStep_get]
    split_ifs <;> simp [mul_assoc, add_mul]
  simp only [hentry, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, ← Finset.mul_sum]

/-- The missing low powers are recorded by `position` throughout the loop. -/
def fusedBackInvariant (A B : L[X]) (state : FusedBackState K L) : Prop :=
  X ^ state.2.2.1 * state.2.2.2.1 = B * state.2.1 ∧
    (X + 1) ^ state.2.2.1 * state.2.2.2.2 = A * taylor 1 state.2.1

theorem fusedBackStep_invariant (A B : L[X]) (state : FusedBackState K L)
    (step : EliminationStep K L n) (hcol : step.1.val ≤ state.2.2.1)
    (hstate : fusedBackInvariant A B state) :
    fusedBackInvariant A B (fusedBackStep A B state step) := by
  rcases state with ⟨d, x, position, U, shifted⟩
  rcases hstate with ⟨hU, hshifted⟩
  simp only [fusedBackInvariant, fusedBackStep, polynomialBackStep]
  constructor
  · rw [horner_gap_step _ _ _ _ _ _ _ hcol, hU, ← C_mul_X_pow_eq_monomial]
    ring
  · rw [horner_gap_step _ _ _ _ _ _ _ hcol, hshifted]
    simp only [map_add, taylor_mul, taylor_C, taylor_monomial, C_1]
    ring

theorem fusedBackSub_invariant (steps : List (EliminationStep K L n)) (A B : L[X])
    (state : FusedBackState K L)
    (hsteps : steps.Pairwise (fun s t => t.1.val < s.1.val))
    (hbound : ∀ step ∈ steps, step.1.val ≤ state.2.2.1)
    (hstate : fusedBackInvariant A B state) :
    fusedBackInvariant A B (steps.foldl (fusedBackStep A B) state) := by
  induction steps generalizing state with
  | nil => exact hstate
  | cons step steps ih =>
    rw [List.foldl_cons]
    apply ih _ (List.pairwise_cons.mp hsteps).2
    · intro next hnext
      exact Nat.le_of_lt ((List.pairwise_cons.mp hsteps).1 next hnext)
    · exact fusedBackStep_invariant A B state step (hbound step (by simp)) hstate

theorem monomialSum_coeff (x : Vector L n) (j : Fin n) :
    (∑ k : Fin n, monomial k.val x[k.val]).coeff j.val = x[j.val] := by
  simp [finsetSum_coeff, coeff_monomial, Fin.val_inj]

theorem polynomial_backStep_eq (step : EliminationStep K L n) (d : K) (x : Vector L n) :
    C (algebraMap K L step.2.1) * (∑ j : Fin n, monomial j.val x[j.val]) +
      monomial step.1.val
        (algebraMap K L d * step.2.2.2 -
          directDot (fun j : Fin n => step.2.2.1[j.val])
            (fun j => (∑ k : Fin n, monomial k.val x[k.val]).coeff j.val)) =
      ∑ j : Fin n, monomial j.val (eliminationBackStep step (d, x)).2[j.val] := by
  simp only [monomialSum_coeff]
  simpa only [C_mul_X_pow_eq_monomial] using
    (eliminationBackStep_poly step d x (X : L[X])).symm

theorem polynomialBackStep_vector (step : EliminationStep K L n)
    (d : K) (x : Vector L n) :
    polynomialBackStep (d, ∑ j : Fin n, monomial j.val x[j.val]) step =
      let result := eliminationBackStep step (d, x)
      (result.1, ∑ j : Fin n, monomial j.val result.2[j.val]) := by
  apply Prod.ext
  · rfl
  · exact polynomial_backStep_eq step d x

/-- Polynomial storage represents the same complete coefficient vector at every step. -/
theorem polynomialBackStep_fold (steps : List (EliminationStep K L n))
    (d : K) (x : Vector L n) :
    steps.foldl polynomialBackStep (d, ∑ j : Fin n, monomial j.val x[j.val]) =
      let result := steps.foldl (fun result step => eliminationBackStep step result) (d, x)
      (result.1, ∑ j : Fin n, monomial j.val result.2[j.val]) := by
  induction steps generalizing d x with
  | nil => rfl
  | cons step steps ih =>
    simp only [List.foldl_cons]
    rw [polynomialBackStep_vector]
    exact ih _ _

/-- Polynomial back substitution and fused Horner reconstruction agree with the
fraction-free coefficient model, including empty and skipped pivot columns. -/
theorem fusedBackSub_eq (steps : List (EliminationStep K L n)) (A B : L[X])
    (hsteps : steps.Pairwise (fun s t => t.1.val < s.1.val)) :
    fusedBackSub steps A B =
      let result := steps.foldl (fun result step => eliminationBackStep step result)
        (1, Vector.replicate n 0)
      (result.1, ∑ j : Fin n, monomial j.val result.2[j.val],
        B * ∑ j : Fin n, monomial j.val result.2[j.val],
        A * taylor 1 (∑ j : Fin n, monomial j.val result.2[j.val])) := by
  rw [fusedBackSub_eq_fold]
  have hbase := fusedBackSub_base steps A B (1, 0, n, 0, 0)
  have hvector := polynomialBackStep_fold steps (1 : K) (Vector.replicate n (0 : L))
  simp only [Vector.getElem_replicate, monomial_zero_right, Finset.sum_const_zero] at hvector
  have hbase := hbase.trans hvector
  have hvalue := fusedBackSub_invariant steps A B (1, 0, n, 0, 0)
    hsteps (fun step _ => step.1.isLt.le) (by simp [fusedBackInvariant])
  have hx := congrArg (fun result : K × L[X] => result.2) hbase
  dsimp only at hx ⊢
  apply Prod.ext
  · exact congrArg (fun result : K × L[X] => result.1) hbase
  · apply Prod.ext
    · exact hx
    · apply Prod.ext
      · have hU := hvalue.1
        rw [hx] at hU
        exact hU
      · have hshifted := hvalue.2
        rw [hx] at hshifted
        exact hshifted

end Gosper.Algorithm
