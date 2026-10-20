module

public import SympyProofs.Python.Cost.Sequence
public import SympyProofs.Python.Cost.ComputationBounds
public import SympyProofs.Python.Cost.Asymptotics

/-!
# Loop costs for the executed product

The exact unit cost is obtained by composing a fold-body contract. It includes
each loop iteration, its multiplication, and the final loop-exit event.
-/

@[expose] public section

namespace Python.Cost.Sequence

open PythonInt Models Asymptotics

variable {I : Type} [PythonInt I]

theorem prod_operations (xs : Array I) :
    RunsWith operations (prod (m := CostT Id) xs) (Python.Math.prod xs) (2 * xs.size + 1) := by
  have hf := RunsWith.foldlM (model := operations) xs.toList
    (fun result x => do
      MonadCost.emit (.control "prod.next")
      Python.Cost.Int.mul result x)
    (· * ·) (fun _ => 2) (fun _ _ _ => by intro initial; rfl) (1 : I)
  have hstop : RunsWith operations
      (do
        MonadCost.emit (.control "prod.stop")
        pure (xs.toList.foldl (· * ·) (1 : I)))
      (xs.toList.foldl (· * ·) (1 : I)) 1 := by intro initial; rfl
  have h := hf.bind (next := fun result => do
    MonadCost.emit (.control "prod.stop")
    pure result) hstop
  simpa [prod, Python.Math.prod, Array.foldl_toList, Nat.mul_comm] using h

theorem prod_operations_isTheta_length {X : Type} (l : Filter X) (xs : X → Array I) :
    (fun x => ((CostT.run (prod (m := CostT Id) (xs x)) operations).2 : ℝ)) =Θ[l]
      (fun x => (((xs x).size + 1 : ℕ) : ℝ)) := by
  apply nat_isTheta_of_bounds 2
  · intro x
    rw [prod_operations (xs x) 0]
    simp
    omega
  · intro x
    rw [prod_operations (xs x) 0]
    simp

/-- Sum of the input widths; unlike output width, this accounts for factors equal to zero or one. -/
def inputBits (xs : Array I) : ℕ := (xs.toList.map (fun x => width (toInt x))).sum

private theorem mul_potential_bound (xs : List I) (w : ℕ) (start : I)
    (hw : 1 ≤ w) (hstart : width (toInt start) ≤ w) :
    Bounded schoolbook
      (xs.foldlM (fun result x => do
        MonadCost.emit (.control "prod.next")
        Python.Cost.Int.mul result x) start)
      (fun result => 1 ≤ w + (xs.map (fun x => width (toInt x))).sum ∧
        width (toInt result) ≤ w + (xs.map (fun x => width (toInt x))).sum)
      ((w + (xs.map (fun x => width (toInt x))).sum + 1)^2 - (w + 1)^2) := by
  apply Bounded.foldlM_potential xs _
    (fun w s => 1 ≤ w ∧ width (toInt s) ≤ w) (fun x => width (toInt x)) (fun w => (w+1)^2)
  · intro a b hab
    nlinarith
  · intro w s hs x _hx
    let v := width (toInt x)
    have hv : 1 ≤ v := one_le_width _
    have hm := (Sized.value s hs.2).mul (Sized.value x (le_refl v))
    have he : Bounded schoolbook (MonadCost.emit (.control "prod.next"))
        (fun _ => True) 1 := (RunsWith.emit _).bounded trivial (by rfl)
    have hb := he.bind (next := fun _ => Python.Cost.Int.mul s x) (fun _ _ => hm)
    apply hb.mono
    · intro result hr
      exact ⟨by omega, hr⟩
    · have hprod := Nat.mul_le_mul_left w hv
      have hv2 : 1 ≤ v * v := by nlinarith
      change 1 + (0 + 0 + (1 + w * v + w + v)) ≤ (w + v + 1)^2 - (w + 1)^2
      apply Nat.le_sub_of_add_le
      nlinarith
  · exact ⟨hw, hstart⟩

/-- A compositional contract: the actual execution returns a bounded-width value
and spends a quadratic cumulative bit budget, from any initial counter. -/
theorem prod_bounded (xs : Array I) :
    Bounded schoolbook (prod (m := CostT Id) xs)
      (fun result => width (toInt result) ≤ 1 + inputBits xs) ((inputBits xs + 2)^2) := by
  have hf := mul_potential_bound xs.toList 1 (1 : I) (by omega)
    (by simp [width, toInt_one])
  have hstop (result : I) : Bounded schoolbook
      (do MonadCost.emit (.control "prod.stop"); pure result) (fun r => r = result) 1 :=
    (RunsWith.bind (RunsWith.emit _) (RunsWith.pure result)).bounded rfl (by rfl)
  have h := hf.bind (post' := fun result => width (toInt result) ≤ 1 + inputBits xs)
    (fun result hr => (hstop result).mono (by intro r he; subst r; exact hr.2) (le_refl _))
  rw [Array.foldlM_toList] at h
  apply h.mono (fun _ h => h)
  change (1 + inputBits xs + 1)^2 - 4 + 1 ≤ (inputBits xs + 2)^2
  have h₀ : 4 ≤ (inputBits xs + 2)^2 :=
    Nat.pow_le_pow_left (show 2 ≤ inputBits xs + 2 by omega) 2
  rw [show 1 + inputBits xs + 1 = inputBits xs + 2 by omega]
  omega

/-- A quadratic cumulative bit budget pays for all intermediate multiplications. -/
theorem prod_schoolbook_le (xs : Array I) :
    (CostT.run (prod (m := CostT Id) xs) schoolbook).2 ≤ (inputBits xs + 2)^2 :=
  (prod_bounded xs).cost_le

theorem prod_schoolbook_isBigO {X : Type} (l : Filter X) (xs : X → Array I) :
    (fun x => ((CostT.run (prod (m := CostT Id) (xs x)) schoolbook).2 : ℝ)) =O[l]
      (fun x => (((inputBits (xs x) + 1)^2 : ℕ) : ℝ)) := by
  apply nat_isBigO_of_le_mul 4
  intro x
  have h := prod_schoolbook_le (xs x)
  have hS := Nat.zero_le (inputBits (xs x))
  nlinarith [sq_nonneg (inputBits (xs x))]

end Python.Cost.Sequence
