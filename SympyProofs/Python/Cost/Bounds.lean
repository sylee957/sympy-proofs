module

public import SympyProofs.Python.Cost
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic

/-!
# Compositional bounds on executed programs

`RunsWith` describes a value and its exact additional cost. `Bounded` additionally
supports a result invariant and an upper budget. Both quantify over the initial
counter, so a theorem remains valid when its program is used inside a larger one.
These are propositions about ordinary `CostT` programs, not a second program syntax.
-/

@[expose] public section

namespace Python.Cost

variable {α β σ : Type} {model : Model}

def RunsWith (model : Model) (program : CostT Id α) (value : α) (cost : ℕ) : Prop :=
  ∀ initial, CostT.run program model initial = (value, initial + cost)

def Bounded (model : Model) (program : CostT Id α) (post : α → Prop) (budget : ℕ) : Prop :=
  ∀ initial, ∃ value cost, CostT.run program model initial = (value, initial + cost) ∧
    post value ∧ cost ≤ budget

namespace RunsWith

theorem pure (value : α) : RunsWith model (pure value) value 0 := by
  intro initial
  rfl

theorem perform (event : Event) (value : α) :
    RunsWith model (perform event value) value (model event) := by intro initial; rfl

theorem emit (event : Event) :
    RunsWith model (MonadCost.emit event) () (model event) := by intro initial; rfl

theorem bind {program : CostT Id α} {next : α → CostT Id β} {a : α} {b : β} {c d : ℕ}
    (h : RunsWith model program a c) (hn : RunsWith model (next a) b d) :
    RunsWith model (program >>= next) b (c + d) := by
  intro initial
  rw [CostT.run_bind, h]
  dsimp only
  rw [hn]
  simp [Nat.add_assoc]

theorem bounded {program : CostT Id α} {value : α} {cost budget : ℕ} {post : α → Prop}
    (h : RunsWith model program value cost) (hp : post value) (hc : cost ≤ budget) :
    Bounded model program post budget := by
  intro initial
  exact ⟨value, cost, h initial, hp, hc⟩

/-- Exact per-iteration charges add, while the returned accumulator follows `f`. -/
theorem foldlM (xs : List α) (step : σ → α → CostT Id σ)
    (f : σ → α → σ) (cost : α → ℕ)
    (hstep : ∀ s x, x ∈ xs → RunsWith model (step s x) (f s x) (cost x)) (s : σ) :
    RunsWith model (xs.foldlM step s) (xs.foldl f s) ((xs.map cost).sum) := by
  induction xs generalizing s with
  | nil => exact pure s
  | cons x xs ih =>
    exact (hstep s x (by simp)).bind
      (ih (fun s x hx => hstep s x (by simp [hx])) (f s x))

end RunsWith

namespace Bounded

theorem pure (value : α) {post : α → Prop} (h : post value) :
    Bounded model (pure value) post 0 := (RunsWith.pure value).bounded h (by rfl)

theorem mono {program : CostT Id α} {post post' : α → Prop} {budget budget' : ℕ}
    (h : Bounded model program post budget)
    (hp : ∀ a, post a → post' a) (hc : budget ≤ budget') :
    Bounded model program post' budget' := by
  intro initial
  rcases h initial with ⟨a, c, hr, ha, hc'⟩
  exact ⟨a, c, hr, hp a ha, hc'.trans hc⟩

theorem bind {program : CostT Id α} {next : α → CostT Id β}
    {post : α → Prop} {post' : β → Prop} {c d : ℕ}
    (h : Bounded model program post c)
    (hn : ∀ a, post a → Bounded model (next a) post' d) :
    Bounded model (program >>= next) post' (c + d) := by
  intro initial
  rcases h initial with ⟨a, c₀, hr, ha, hc⟩
  rcases hn a ha (initial + c₀) with ⟨b, d₀, hnr, hb, hd⟩
  refine ⟨b, c₀ + d₀, ?_, hb, Nat.add_le_add hc hd⟩
  rw [CostT.run_bind, hr]
  dsimp only
  rw [hnr]
  simp [Nat.add_assoc]

/-- A loop invariant and a budget per element suffice; its implementation stays unchanged. -/
theorem foldlM (xs : List α) (step : σ → α → CostT Id σ)
    (inv : σ → Prop) (cost : α → ℕ)
    (hstep : ∀ s, inv s → ∀ x ∈ xs, Bounded model (step s x) inv (cost x))
    (s : σ) (hs : inv s) :
    Bounded model (xs.foldlM step s) inv ((xs.map cost).sum) := by
  induction xs generalizing s with
  | nil => exact pure s hs
  | cons x xs ih =>
    exact (hstep s hs x (by simp)).bind fun t ht =>
      ih (fun s hs x hx => hstep s hs x (by simp [hx])) t ht

/-- Accumulate a size invariant separately from the charged work. -/
theorem foldlM_accumulate (xs : List α) (step : σ → α → CostT Id σ)
    (inv : ℕ → σ → Prop) (weight cost : α → ℕ)
    (hstep : ∀ w s, inv w s → ∀ x ∈ xs,
      Bounded model (step s x) (inv (w + weight x)) (cost x))
    (w : ℕ) (s : σ) (hs : inv w s) :
    Bounded model (xs.foldlM step s) (inv (w + (xs.map weight).sum))
      ((xs.map cost).sum) := by
  induction xs generalizing w s with
  | nil => simpa using pure s hs
  | cons x xs ih =>
    have h := (hstep w s hs x (by simp)).bind fun t ht =>
      ih (fun w s hs x hx => hstep w s hs x (by simp [hx])) (w + weight x) t ht
    simpa only [List.foldlM_cons, List.map_cons, List.sum_cons, Nat.add_assoc] using h

/-- An increasing size budget pays for a loop through increments of a potential.
This telescopes the per-iteration charges rather than charging every iteration
at the largest intermediate size. -/
theorem foldlM_potential (xs : List α) (step : σ → α → CostT Id σ)
    (inv : ℕ → σ → Prop) (weight : α → ℕ) (potential : ℕ → ℕ)
    (hmono : Monotone potential)
    (hstep : ∀ w s, inv w s → ∀ x ∈ xs,
      Bounded model (step s x) (inv (w + weight x))
        (potential (w + weight x) - potential w))
    (w : ℕ) (s : σ) (hs : inv w s) :
    Bounded model (xs.foldlM step s) (inv (w + (xs.map weight).sum))
      (potential (w + (xs.map weight).sum) - potential w) := by
  induction xs generalizing w s with
  | nil => simpa using pure s hs
  | cons x xs ih =>
    have h := (hstep w s hs x (by simp)).bind fun t ht =>
      ih (fun w s hs x hx => hstep w s hs x (by simp [hx])) (w + weight x) t ht
    apply h.mono
    · intro t ht
      simpa [Nat.add_assoc] using ht
    · have h₁ := hmono (show w ≤ w + weight x by omega)
      have h₂ := hmono (show w + weight x ≤ w + weight x + (xs.map weight).sum by omega)
      simp only [List.map_cons, List.sum_cons]
      rw [← Nat.add_assoc]
      omega

/-- The invariant applies to the actual returned value, not an auxiliary reference program. -/
theorem result {program : CostT Id α} {post : α → Prop} {budget : ℕ}
    (h : Bounded model program post budget) : post (CostT.run program model).1 := by
  rcases h 0 with ⟨a, c, hr, ha, _⟩
  simpa [hr] using ha

theorem cost_le {program : CostT Id α} {post : α → Prop} {budget : ℕ}
    (h : Bounded model program post budget) : (CostT.run program model).2 ≤ budget := by
  rcases h 0 with ⟨a, c, hr, _, hc⟩
  simpa [hr] using hc

end Bounded

end Python.Cost

namespace Python.Cost.Bounded

/-- Reprice a single primitive; this does not assert monotonicity for arbitrary
`CostT` functions, which could inspect their model or counter. -/
theorem reprice_perform {α : Type} {model cheaper : Model} {event : Event} {value : α}
    {post : α → Prop} {budget : ℕ}
    (h : Bounded model (perform event value) post budget) (hle : cheaper event ≤ model event) :
    Bounded cheaper (perform event value) post budget := by
  apply (RunsWith.perform event value).bounded
  · simpa using h.result
  · exact hle.trans (by simpa using h.cost_le)

end Python.Cost.Bounded
