module

public import SympyProofs.Python.Generator
public import Std.Data.Iterators.Lemmas
public import Mathlib.Tactic

/-! # Suspension laws and finite traces of the generator monad -/

@[expose] public section

namespace Generator

open Std Std.Iterators

variable {V α β γ : Type}

@[simp] theorem bind_done (a : α) (f : α → Computation V β) : bind (.done a) f = f a := rfl

/-- `yield` saves the entire following computation without running it. -/
@[simp] theorem yield_bind (value : V) (rest : Unit → Computation V α) :
    (yield value >>= rest) = .suspended value rest := rfl

/-- The iterator stores the continuation at a yield without evaluating it. -/
theorem step_suspended (value : V) (rest : Unit → Computation V α) :
    (Computation.suspended value rest).step = .yield (.deferred rest) ⟨value⟩ := rfl

/-- A deferred body runs only on its own interpreter step. -/
theorem step_deferred (body : Unit → Computation V α) :
    (Computation.deferred body).step = .skip (body ()) := rfl

@[simp] theorem bind_pure (c : Computation V α) : bind c Computation.done = c := by
  induction c with
  | done => rfl
  | suspended v k ih => simp only [bind]; congr; funext u; exact ih u
  | deferred k ih => simp only [bind]; congr; funext u; exact ih u
  | loop S body s after _ ih => simp only [bind]; congr; funext s; exact ih s

@[simp] theorem bind_assoc (c : Computation V α) (f : α → Computation V β)
    (g : β → Computation V γ) : bind (bind c f) g = bind c (fun a => bind (f a) g) := by
  induction c with
  | done => rfl
  | suspended v k ih => simp only [bind]; congr; funext u; exact ih u f
  | deferred k ih => simp only [bind]; congr; funext u; exact ih u f
  | loop S body s after _ ih => simp only [bind]; congr; funext s; exact ih s f

instance : LawfulMonad (Computation V) := LawfulMonad.mk' _
  (by intros; exact bind_pure _)
  (by intros; rfl)
  (by intros; exact bind_assoc _ _ _)

/-- A finite execution trace, including internal transitions with no emitted value. -/
inductive Produces : Computation V α → List V → Prop
  | done {c} : c.step = .done → Produces c []
  | yield {c next value values} : c.step = .yield next ⟨value⟩ →
      Produces next values → Produces c (value :: values)
  | skip {c next values} : c.step = .skip next → Produces next values → Produces c values

/-- A generator halts if its interpreter transition relation is accessible. -/
def Halts (c : Computation V α) : Prop :=
  Acc (fun next current => current.step.successor = some next) c

/-- A finite trace guarantees termination, including termination of internal steps. -/
theorem Produces.halts {c : Computation V α} {values : List V} (h : Produces c values) :
    Halts c := by
  induction h with
  | done h => exact .intro _ (by intro next hn; simp [h] at hn)
  | yield h _ ih =>
    refine .intro _ fun next hn => ?_
    simp only [h, IterStep.successor_yield, Option.some.injEq] at hn
    subst next
    exact ih
  | skip h _ ih =>
    refine .intro _ fun next hn => ?_
    simp only [h, IterStep.successor_skip, Option.some.injEq] at hn
    subst next
    exact ih

/-- Every saved continuation of a terminating generator also terminates. -/
theorem Halts.reachable {initial c : Computation V α} (h : Halts initial)
    (hr : Reachable initial c) : Halts c := by
  induction hr with
  | refl => exact h
  | next _ hs ih => exact ih.inv hs

/-- The iterator exposes exactly the small step of its saved frame. -/
theorem iterator_step {initial : Computation V α} (frame : Frame initial) :
    (⟨frame⟩ : Iter (ULift.{1} V)).step.val =
      frame.step.mapIterator (fun frame => (⟨frame⟩ : Iter (ULift.{1} V))) := by
  simp [Iter.step, IterM.step, Iterator.step, IterM.Step.toPure]
  rfl

/-- A frame transition is an underlying computation transition. -/
theorem frame_step_successor {initial : Computation V α} {f f' : Frame initial}
    (h : f.step.successor = some f') : f.val.step.successor = some f'.val := by
  unfold Frame.step at h
  split at h
  · simp at h
  all_goals
    simp only [IterStep.successor_yield, IterStep.successor_skip, Option.some.injEq] at h
    subst f'
    simp_all

/-- A terminating initial computation gives a finite iterator on its reachable states. -/
theorem finite_of_halts {initial : Computation V α} (h : Halts initial) :
    Finite (Frame initial) Id := by
  apply Finite.of_finitenessRelation
  exact {
    Rel := fun a b => b.internalState.val.step.successor = some a.internalState.val
    wf := ⟨fun it => InvImage.accessible
      (fun it : IterM (α := Frame initial) Id (ULift.{1} V) => it.internalState.val)
      (h.reachable it.internalState.property)⟩
    subrelation := by
      intro it it' hs
      obtain ⟨step, he, hp⟩ := hs
      change step = it.internalState.step.mapIterator (fun f => ⟨f⟩) at hp
      subst step
      have he' : it.internalState.step.successor = some it'.internalState := by
        cases ht : it.internalState.step <;> simp_all
        all_goals exact congrArg IterM.internalState he
      exact frame_step_successor he' }

@[simp] theorem frame_step_done {initial c : Computation V α} (hr : Reachable initial c)
    (hs : c.step = .done) : Frame.step (⟨c, hr⟩ : Frame initial) = .done := by
  unfold Frame.step
  split <;> rename_i heq
  all_goals
    change c.step = _ at heq
    cases heq.symm.trans hs
  all_goals rfl

@[simp] theorem frame_step_yield {initial c d : Computation V α} (v : ULift.{1} V)
    (hr : Reachable initial c) (hs : c.step = .yield d v) :
    Frame.step (⟨c, hr⟩ : Frame initial) = .yield ⟨d, .next hr (by simp [hs])⟩ v := by
  unfold Frame.step
  split <;> rename_i heq
  all_goals
    change c.step = _ at heq
    cases heq.symm.trans hs
  all_goals rfl

@[simp] theorem frame_step_skip {initial c d : Computation V α}
    (hr : Reachable initial c) (hs : c.step = .skip d) :
    Frame.step (⟨c, hr⟩ : Frame initial) = .skip ⟨d, .next hr (by simp [hs])⟩ := by
  unfold Frame.step
  split <;> rename_i heq
  all_goals
    change c.step = _ at heq
    cases heq.symm.trans hs
  all_goals rfl

/-- Reading any reachable frame agrees with its finite trace. -/
theorem toList_of_produces {initial c : Computation V α} {values : List V}
    [Finite (Frame initial) Id] (hr : Reachable initial c) (h : Produces c values) :
    (⟨⟨c, hr⟩⟩ : Iter (α := Frame initial) (ULift.{1} V)).toList.map ULift.down = values := by
  induction h with
  | done hs =>
    rw [Iter.toList_eq_match_step, iterator_step, frame_step_done hr hs]
    rfl
  | @yield c next value values hs _ ih =>
    rw [Iter.toList_eq_match_step, iterator_step, frame_step_yield _ hr hs]
    simpa using congrArg (List.cons value) (ih (.next hr (by simp [hs])))
  | skip hs _ ih =>
    rw [Iter.toList_eq_match_step, iterator_step, frame_step_skip hr hs]
    exact ih (.next hr (by simp [hs]))

/-- Collecting a terminating body returns exactly its proved trace. -/
theorem Produces.toList {c : Computation V α} {values : List V} (h : Produces c values) :
    c.toList = values := by
  let := finite_of_halts h.halts
  exact toList_of_produces .refl h

/-- A finite trace also determines every consuming loop, including early exit. -/
theorem Produces.forIn {c : Computation V α} {values : List V} (h : Produces c values)
    {m : Type → Type v} [Monad m] [LawfulMonad m] {σ : Type}
    (initial : σ) (body : V → σ → m (ForInStep σ)) :
    ForIn.forIn c initial body = ForIn.forIn values initial body := by
  let := finite_of_halts h.halts
  change ForIn.forIn c.iter initial (fun v s => body v.down s) = _
  rw [← Iter.forIn_toList, ← List.forIn_map]
  change ForIn.forIn c.toList initial body = _
  rw [h.toList]

end Generator
