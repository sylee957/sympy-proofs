module

public import SympyProofs.Python.Generator.Execution
/-!
# Compositional resource bounds for finite generator traces

Both charges and an output measure compose through binds and terminating loops.
`Returns` certifies actual suspension and resumption steps; no trace is assumed
merely from a terminating value calculation.
-/

@[expose] public section

namespace Generator
variable {V α β σ : Type}
/-- A finite trace with an execution charge, an output measure, and allowed entries. -/
def Budgeted (weight count : V → ℕ) (allowed : V → Prop)
    (program : Computation V α) (post : α → Prop) (budget outputs : ℕ) : Prop :=
  ∃ a xs, Returns program a xs ∧ post a ∧ (∀ v ∈ xs, allowed v) ∧
    (xs.map weight).sum ≤ budget ∧ (xs.map count).sum ≤ outputs
namespace Budgeted
variable {weight count : V → ℕ} {allowed : V → Prop}
theorem pure (a : α) {post : α → Prop} (ha : post a) :
    Budgeted weight count allowed (Pure.pure a) post 0 0 :=
  ⟨a, [], .done a, ha, by simp, by simp, by simp⟩

theorem yield (v : V) (hv : allowed v) :
    Budgeted weight count allowed (Generator.yield v) (fun _ => True) (weight v) (count v) :=
  ⟨(), [v], Returns.yield_one v, trivial, by simpa, by simp, by simp⟩

theorem mono {c : Computation V α} {post post' : α → Prop} {b b' q q' : ℕ}
    (h : Budgeted weight count allowed c post b q)
    (hp : ∀a, post a → post' a) (hb : b ≤ b') (hq : q ≤ q') :
    Budgeted weight count allowed c post' b' q' := by
  obtain ⟨a,xs,hr,ha,hv,hb0,hq0⟩ := h
  exact ⟨a,xs,hr,hp a ha,hv,hb0.trans hb,hq0.trans hq⟩

theorem bind {c : Computation V α} {f : α → Computation V β}
    {post : α → Prop} {post' : β → Prop} {b d q r : ℕ}
    (h : Budgeted weight count allowed c post b q)
    (hf : ∀ a, post a → Budgeted weight count allowed (f a) post' d r) :
    Budgeted weight count allowed (c >>= f) post' (b+d) (q+r) := by
  obtain ⟨a,xs,hx,ha,hax,hbx,hqx⟩ := h
  obtain ⟨a',ys,hy,ha',hay,hby,hqy⟩ := hf a ha
  refine ⟨a', xs++ys, hx.bind hy, ha', ?_, ?_, ?_⟩
  · simpa only [List.mem_append, or_imp, forall_and] using And.intro hax hay
  · simpa using Nat.add_le_add hbx hby
  · simpa using Nat.add_le_add hqx hqy

/-- A finite loop composes value refinement, its invariant, and both resources. -/
theorem foldlM (xs : List α) (step : σ → α → Computation V σ)
    (f : σ → α → σ) (inv : σ → Prop) (cost emitted : α → ℕ)
    (hstep : ∀ s, inv s → ∀ x ∈ xs,
      Budgeted weight count allowed (step s x) (fun t => t = f s x ∧ inv t)
        (cost x) (emitted x))
    (s : σ) (hs : inv s) :
    Budgeted weight count allowed (xs.foldlM step s)
      (fun t => t = xs.foldl f s ∧ inv t) ((xs.map cost).sum) ((xs.map emitted).sum) := by
  induction xs generalizing s with
  | nil => exact pure s ⟨rfl,hs⟩
  | cons x xs ih =>
    have h := (hstep s hs x (by simp)).bind
      (f := fun t => xs.foldlM step t)
      (post' := fun t => t = xs.foldl f (f s x) ∧ inv t)
      (d := (xs.map cost).sum) (r := (xs.map emitted).sum) (fun t ht => by
      rcases ht with ⟨rfl,ht⟩
      exact ih (fun s hs x hx => hstep s hs x (by simp [hx])) (f s x) ht)
    simpa only [List.foldlM_cons,List.foldl_cons,List.map_cons,List.sum_cons] using h

/-- The finite trace is constructed along the decreasing loop measure. -/
theorem loop (body : σ → Computation V (ForInStep σ)) (inv post : σ → Prop)
    (rank : σ → ℕ) (stepCost stepOutputs : ℕ)
    (hbody : ∀s, inv s → Budgeted weight count allowed (body s)
      (fun r => match r with
        | .done t => post t
        | .yield t => inv t ∧ rank t < rank s) stepCost stepOutputs)
    (s : σ) (hs : inv s) :
    Budgeted weight count allowed (Computation.loop σ body s Computation.done)
      post ((rank s+1)*stepCost) ((rank s+1)*stepOutputs) := by
  have hnext : ∀ (r : ForInStep σ), (match r with
      | .done t => post t
      | .yield t => inv t ∧ rank t < rank s) →
      Budgeted weight count allowed
        (match r with
          | .done t => Computation.done t
          | .yield t => Computation.loop σ body t Computation.done)
        post (rank s*stepCost) (rank s*stepOutputs) := by
    intro r hr
    cases r with
    | done t => exact (pure t hr).mono (fun _ h => h) (Nat.zero_le _) (Nat.zero_le _)
    | yield t =>
      exact (loop body inv post rank stepCost stepOutputs hbody t hr.1).mono (fun _ h => h)
        (Nat.mul_le_mul_right _ (by omega)) (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨t,xs,hret,ht,hallowed,hcost,hcount⟩ := (hbody s hs).bind hnext
  refine ⟨t,xs,.skip rfl hret,ht,hallowed,?_,?_⟩
  · simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm] using hcost
  · simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm] using hcount
termination_by rank s
end Budgeted
end Generator
