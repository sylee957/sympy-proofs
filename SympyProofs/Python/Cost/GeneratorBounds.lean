module

public import SympyProofs.Python.Generator.Budget
public import SympyProofs.Python.Cost.Generator
public import SympyProofs.Python.Cost.Bounds
/-!
# Transferring a generator's trace budget to an executed consumer

The trace is obtained from finite interpreter steps, including deferred resumes.
The consumer contract may accumulate a separate size invariant on each output.
-/

@[expose] public section

namespace Generator.Budgeted
open Python.Cost
variable {model : Model} {V α σ : Type} {weight count : V → ℕ} {allowed : V → Prop}
/-- Delivering the actual suspended trace transfers its resource budget to a consumer. -/
theorem forIn_bounded {c : Computation V α} {post : α → Prop} {budget outputs : ℕ}
    (h : Budgeted weight count allowed c post budget outputs)
    (body : V → σ → CostT Id σ) (inv : ℕ → σ → Prop)
    (hbody : ∀ q s, inv q s → ∀ v, allowed v →
      Bounded model (body v s) (inv (q+count v)) (weight v))
    (s : σ) (hs : inv 0 s) :
    Bounded model
      (ForIn.forIn c s (fun v s => ForInStep.yield <$> body v s))
      (fun s => ∃ q ≤ outputs, inv q s) budget := by
  obtain ⟨a,xs,hr,_,hv,hcost,hcount⟩ := h
  rw [hr.produces.forIn, List.forIn_yield_eq_foldlM]
  have hf := Bounded.foldlM_accumulate (model := model) xs (fun s v => body v s)
    inv count weight (fun q s hs v hmem => hbody q s hs v (hv v hmem)) 0 s hs
  exact hf.mono (fun s hs => ⟨(xs.map count).sum, hcount, by simpa using hs⟩) hcost
end Generator.Budgeted

namespace Python.Cost

variable {V α : Type} {model : Model} {weight count : Event ⊕ V → ℕ}
    {allowed : Event ⊕ V → Prop}
/-- Primitive value/cost contracts lift to a suspended event without losing its trace. -/
theorem perform_budgeted (event : Event) (value : α) {post : α → Prop} {budget : ℕ}
    (hw : weight (.inl event) = model event) (hc : count (.inl event) = 0)
    (ha : allowed (.inl event))
    (h : Bounded model (perform event value) post budget) :
    Generator.Budgeted weight count allowed
      (letI := eventCost (V := V)
       perform (m := Generator.Computation (Event ⊕ V)) event value)
      post budget 0 := by
  obtain ⟨a,c,he,hp,hb⟩ := h 0
  change (value, 0+model event) = (a,0+c) at he
  have hv : value = a := congrArg Prod.fst he
  have hcost : model event = c := by simpa using congrArg Prod.snd he
  subst a
  refine ⟨value,[.inl event],.yield rfl (.skip rfl (.done value)),hp,?_,?_,?_⟩
  · simpa using ha
  · simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,hw,hcost] using hb
  · simp [hc]
end Python.Cost
