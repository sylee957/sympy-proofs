module

public import SympyProofs.Python.Cost.SequenceBounds

/-!
# An attained quadratic cost for sequential multiplication

Multiplying a list of twos repeatedly grows the accumulator. Under the declared
schoolbook policy this family has Θ(n²) cost, matching `prod_schoolbook_isBigO`
because its total input width is 2n. This is a statement about `Sequence.prod`,
not about the balanced product or measured CPython performance.
-/

@[expose] public section

namespace Python.Cost.Sequence

open PythonInt Models Asymptotics

variable {I : Type} [PythonInt I]

private theorem width_two_pow (p : ℕ) : width (toInt ((2 : I)^p)) = p + 1 := by
  have ht : equivInt (2 : I) = (2 : ℤ) := by change toInt (2 : I) = 2; simp
  simp only [toInt, _root_.map_pow, ht, width, Int.natAbs_pow]
  change max 1 (2^p).size = p+1
  rw [Nat.size_pow]
  omega

private theorem two_step (p : ℕ) :
    RunsWith schoolbook
      (do MonadCost.emit (.control "prod.next"); Python.Cost.Int.mul ((2 : I)^p) 2)
      ((2 : I)^(p+1)) (3*p+6) := by
  have hm : RunsWith schoolbook (Python.Cost.Int.mul ((2 : I)^p) 2)
      ((2 : I)^(p+1)) (3*p+5) := by
    have h := RunsWith.perform (model := schoolbook)
      (.integer ⟨.mul, [toInt ((2:I)^p), toInt (2:I)], toInt ((2:I)^p*2)⟩) ((2:I)^p*2)
    have hp := width_two_pow (I := I) p
    have hp' := width_two_pow (I := I) (p+1)
    have ht : width (toInt (2:I)) = 2 := by simpa using width_two_pow (I := I) 1
    simpa only [Int.mul, Int.binary, ← pow_succ, schoolbook, integerSchoolbook, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, hp, hp', ht,
      show 1 + ((p+1)*2+(p+1+1)) = 3*p+5 by omega] using h
  have h := (RunsWith.emit (.control "prod.next")).bind
    (next := fun _ => Python.Cost.Int.mul ((2:I)^p) 2) hm
  simpa only [schoolbook, show 1 + (3*p+5) = 3*p+6 by omega] using h

private theorem twos_fold (n p : ℕ) :
    RunsWith schoolbook
      ((List.replicate n (2:I)).foldlM (fun result x => do
        MonadCost.emit (.control "prod.next")
        Python.Cost.Int.mul result x) ((2:I)^p))
      ((2:I)^(p+n)) (3 * (List.range n).sum + 3*p*n + 6*n) := by
  induction n generalizing p with
  | zero => simpa using (RunsWith.pure (model := schoolbook) ((2:I)^p))
  | succ n ih =>
    have h := (two_step (I := I) p).bind (next := fun result =>
      (List.replicate n (2:I)).foldlM (fun result x => do
        MonadCost.emit (.control "prod.next")
        Python.Cost.Int.mul result x) result) (ih (p+1))
    have he : p + (n+1) = p+1+n := by omega
    have hc : 3 * (List.range (n+1)).sum + 3*p*(n+1) + 6*(n+1) =
        3*p+6 + (3 * (List.range n).sum + 3*(p+1)*n + 6*n) := by
      simp only [List.range_succ, List.sum_append, List.sum_cons, List.sum_nil]
      ring
    simpa only [List.replicate_succ, List.foldlM_cons, he, hc] using h

/-- Exact cost and value for the family attaining quadratic sequential-product work. -/
theorem prod_twos (n : ℕ) :
    RunsWith schoolbook (prod (m := CostT Id) (List.replicate n (2:I)).toArray)
      ((2:I)^n) (3 * (List.range n).sum + 6*n + 1) := by
  have hf := twos_fold (I := I) n 0
  have hs : RunsWith schoolbook
      (do MonadCost.emit (.control "prod.stop"); pure ((2:I)^(0+n))) ((2:I)^(0+n)) 1 :=
    (RunsWith.emit _).bind (next := fun _ => pure ((2:I)^(0+n))) (RunsWith.pure _)
  have h := hf.bind (next := fun result => do
    MonadCost.emit (.control "prod.stop")
    pure result) hs
  unfold prod
  rw [← Array.foldlM_toList]
  simpa only [List.toList_toArray, Nat.zero_add, pow_zero, Nat.mul_zero, Nat.zero_mul,
    Nat.add_zero] using h

private theorem twice_range_sum (n : ℕ) : 2 * (List.range n).sum + n = n*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.sum_append, List.sum_cons, List.sum_nil]
    nlinarith

theorem inputBits_twos (n : ℕ) : inputBits (List.replicate n (2:I)).toArray = 2*n := by
  have ht : width (toInt (2:I)) = 2 := by simpa using width_two_pow (I := I) 1
  rw [inputBits, List.toList_toArray, List.map_replicate, ht]
  simp [Nat.mul_comm]

theorem prod_twos_cost_twice (n : ℕ) :
    2 * (CostT.run (prod (m := CostT Id) (List.replicate n (2:I)).toArray) schoolbook).2 =
      3*n*n + 9*n + 2 := by
  rw [prod_twos n 0]
  simp only [Nat.zero_add]
  have h := twice_range_sum n
  nlinarith

/-- A concrete input family attains quadratic cost; this is not merely an upper estimate. -/
theorem prod_twos_isTheta :
    (fun n : ℕ => ((CostT.run
      (prod (m := CostT Id) (List.replicate n (2:I)).toArray) schoolbook).2 : ℝ)) =Θ[Filter.atTop]
      (fun n => (((n+1)^2 : ℕ) : ℝ)) := by
  apply nat_isTheta_of_bounds 4
  · intro n
    rw [prod_twos n 0]
    simp only [Nat.zero_add]
    have h := twice_range_sum n
    nlinarith [Nat.zero_le n, sq_nonneg n]
  · intro n
    rw [prod_twos n 0]
    simp only [Nat.zero_add]
    have h := twice_range_sum n
    nlinarith [Nat.zero_le n, sq_nonneg n]

end Python.Cost.Sequence
