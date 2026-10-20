module

public import SympyProofs.Binomial.Costs.ByteSieve

/-! Value refinement from the instrumented table to the verified sieve. -/

@[expose] public section

open Python.Cost PythonByteArray
open scoped PythonBytes

namespace SympyBinomial.ByteSieve

variable (B : Type) [PythonByteArray B]

/-- Ignoring events preserves allocation, repetition, and clearing slot zero. -/
theorem initialM_id (n : ℕ) : Id.run (initialM (m := Id) B n) =
    let bytes : B := (bytearray (b[0x01]) : B)*((n+1)/2)
    if 0 < size bytes then PythonByteArray.set! bytes 0 0 else bytes := by
  dsimp (config := { instances := true }) only
    [initialM, perform, Bind.bind, Pure.pure, Id.run, MonadCost.emit]
  simp only [decide_eq_true_eq]

/-- The cost adapter performs exactly the valid Python slice assignment. -/
theorem markM_id (p : ℕ) (bytes : B) (hp : 0 < p) :
    Id.run (markM (m := Id) B p bytes) =
      if bytes[p/2]! ≠ 0 then
        PythonByteArray.setSlice bytes (p*p/2) p
          ((b[0x00] : Bytes B) * ((len bytes-1-((p*p/2 : ℕ) : ℤ)).fdiv p+1)) hp
          (size_singleton_mul_sliceCount bytes 0 (p*p/2) p hp)
      else bytes := by
  dsimp only [markM, perform, Bind.bind, Pure.pure, Id.run, MonadCost.emit]
  simp only [decide_eq_true_eq]
  change (if bytes[p/2]! ≠ 0 then _ else bytes) = _
  by_cases h : bytes[p/2]! ≠ 0
  · repeat rw [ite_eq_left h]
    change (if hs : 0 < p then
      if hl : PythonBytes.size ((b[0x00] : Bytes B) * ((len bytes-1-((p*p/2 : ℕ) : ℤ)).fdiv p+1)) =
          sliceLength bytes (p*p/2) p then
        PythonByteArray.setSlice bytes (p*p/2) p _ hs hl else bytes
      else bytes) = _
    simp only [hp,size_singleton_mul_sliceCount bytes 0 (p*p/2) p hp,↓reduceDIte]
  · repeat rw [ite_eq_right h]

/-- The instrumented table agrees with the sieve whose slots are proved prime. -/
theorem sieveM_id (n : ℕ) : Id.run (sieveM (m := Id) B n) = sieve B n := by
  rw [sieveM_eq]
  change Id.run (ForIn.forIn ([3:n.sqrt+1:2] : Std.Legacy.Range)
    (Id.run (initialM (m := Id) B n))
    (fun p bytes => pure (ForInStep.yield (Id.run (markM (m := Id) B p bytes))))) = _
  rw [initialM_id]
  unfold sieve
  simp only [Id.run]
  split
  all_goals
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn'_eq_forIn'_range']
    rw [← forIn'_eq_forIn]
    apply List.forIn'_congr (f := fun p _ bytes => pure (ForInStep.yield (Id.run (markM (m := Id) B p bytes)))) rfl rfl
    intro p hp bytes
    have hp3 : 3 ≤ p := by
      obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hp
      omega
    have he := markM_id B p bytes (by omega)
    change ForInStep.yield (Id.run (markM (m := Id) B p bytes)) = _
    rw [he]
    split <;> rfl
  all_goals intros; rfl

end SympyBinomial.ByteSieve
