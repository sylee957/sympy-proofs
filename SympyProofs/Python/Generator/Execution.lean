module

public import SympyProofs.Python.Generator.Correctness
/-! # Finite generator execution, including its return value -/

@[expose] public section

namespace Generator
variable {V α β : Type}
/-- A finite execution with both its returned value and its emitted trace. -/
inductive Returns : Computation V α → α → List V → Prop
  | done (a) : Returns (.done a) a []
  | yield {c next value values a} : c.step = .yield next ⟨value⟩ →
      Returns next a values → Returns c a (value :: values)
  | skip {c next values a} : c.step = .skip next → Returns next a values → Returns c a values

theorem Returns.produces {c : Computation V α} {a xs} (h : Returns c a xs) :
    Produces c xs := by
  induction h with
  | done => exact .done rfl
  | yield h _ ih => exact .yield h ih
  | skip h _ ih => exact .skip h ih

private theorem step_bind_skip {c next : Computation V α} (h : c.step = .skip next)
    (f : α → Computation V β) : (bind c f).step = .skip (bind next f) := by
  cases c <;> simp only [Computation.step] at h <;> cases h
  · rfl
  · simp only [bind, Computation.step, bind_assoc]
    congr 2
    funext s
    cases s <;> rfl

private theorem step_bind_yield {c next : Computation V α} {value}
    (h : c.step = .yield next ⟨value⟩) (f : α → Computation V β) :
    (bind c f).step = .yield (bind next f) ⟨value⟩ := by
  cases c <;> simp only [Computation.step] at h <;> cases h
  rfl

theorem Returns.bind {c : Computation V α} {a xs} (h : Returns c a xs)
    {f : α → Computation V β} {b ys} (hf : Returns (f a) b ys) :
    Returns (c >>= f) b (xs ++ ys) := by
  induction h with
  | done => exact hf
  | yield hs _ ih => exact .yield (step_bind_yield hs f) (ih hf)
  | skip hs _ ih => exact .skip (step_bind_skip hs f) (ih hf)

/-- A single suspension emits one value and resumes to unit. -/
theorem Returns.yield_one (v : V) : Returns (Generator.yield v) () [v] :=
  .yield rfl (.skip rfl (.done ()))
end Generator
