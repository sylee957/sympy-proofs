module

public import SympyProofs.Calculus.Risch.Spec.Analytic
public import SympyProofs.Calculus.Risch.Proof.Specialize
public import SympyProofs.Calculus.Risch.Proof.Integrate
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Soundness for functions of a complex variable. An identity `f = F′` in the field of a
tower is an identity between the functions the terms stand for:

* the symbolic derivative of a term is the derivative of its function, by the chain rule,
  wherever the generators are functions that satisfy the differential equations of the
  tower (`Term.hasDerivAt_eval`);
* an identity in the field holds at every point where both sides are defined
  (`SpecializesOn`);
* the functions `Tower.realize` satisfy the differential equations of the tower at its
  regular points (`Tower.realize_spec`).

`integrate_hasDerivAt` combines them with `integrate_sound`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : ℕ}

namespace Term

variable {m : ℕ}

/-- **The chain rule for terms.** If the generators are functions of `w` whose derivatives
at `z` are given by the terms `vel`, then a term defined at `z` is a function of `w` whose
derivative at `z` is the value of its symbolic derivative. -/
theorem hasDerivAt_eval {vel : Fin m → Term m} {g : ℂ → Fin m → ℂ} {z : ℂ}
    (hg : ∀ i, HasDerivAt (fun w => g w i) ((vel i).eval (g z)) z) :
    ∀ e : Term m, e.Defined (g z) →
      HasDerivAt (fun w => e.eval (g w)) ((e.deriv vel).eval (g z)) z
  | .const q, _ => by
    have e : ((Term.const q : Term m).deriv vel).eval (g z) = 0 := by simp [deriv, eval]
    rw [e]
    exact hasDerivAt_const z _
  | .gen i, _ => hg i
  | .neg a, h => (hasDerivAt_eval hg a h).neg
  | .add a b, h => (hasDerivAt_eval hg a h.1).add (hasDerivAt_eval hg b h.2)
  | .sub a b, h => (hasDerivAt_eval hg a h.1).sub (hasDerivAt_eval hg b h.2)
  | .mul a b, h => (hasDerivAt_eval hg a h.1).mul (hasDerivAt_eval hg b h.2)
  | .div a b, h => by
    refine ((hasDerivAt_eval hg a h.1).div (hasDerivAt_eval hg b h.2.1) h.2.2).congr_deriv ?_
    simp only [deriv, eval]
    rw [sq]

end Term

/-- The derivation of a tower on a term evaluated at elements of the field whose derivatives
are given by the terms `V`. -/
theorem Tower.der_eval {k : Type} [Field k] [CharZero k] (t : Tower n) {m : ℕ}
    {V : Fin m → Term m} {E : Fin m → K k n} (hE : ∀ i, t.der k (E i) = (V i).eval E)
    (e : Term m) : t.der k (e.eval E) = (e.deriv V).eval E := by
  induction e with
  | const q =>
    change t.der k (q : K k n) = ((0 : ℚ) : K k n)
    rw [Rat.cast_def]
    simp [Derivation.leibniz_div]
  | gen i => exact hE i
  | neg a ha =>
    change t.der k (-(a.eval E)) = -((a.deriv V).eval E)
    rw [map_neg, ha]
  | add a b ha hb =>
    change t.der k (a.eval E + b.eval E) = (a.deriv V).eval E + (b.deriv V).eval E
    rw [map_add, ha, hb]
  | sub a b ha hb =>
    change t.der k (a.eval E - b.eval E) = (a.deriv V).eval E - (b.deriv V).eval E
    rw [map_sub, ha, hb]
  | mul a b ha hb =>
    change t.der k (a.eval E * b.eval E) =
      (a.deriv V).eval E * b.eval E + a.eval E * (b.deriv V).eval E
    rw [Derivation.leibniz, ha, hb, smul_eq_mul, smul_eq_mul]
    ring
  | div a b ha hb =>
    change t.der k (a.eval E / b.eval E) =
      ((a.deriv V).eval E * b.eval E - a.eval E * (b.deriv V).eval E) /
        (b.eval E * b.eval E)
    rw [Derivation.leibniz_div, ha, hb]
    simp [smul_eq_mul, div_eq_mul_inv]
    ring

theorem hasDerivAt_list_sum {α : Type*} {F : α → ℂ → ℂ} {F' : α → ℂ} {z : ℂ} :
    ∀ l : List α, (∀ a ∈ l, HasDerivAt (F a) (F' a) z) →
      HasDerivAt (fun w => (l.map fun a => F a w).sum) (l.map F').sum z
  | [], _ => by simpa using hasDerivAt_const z (0 : ℂ)
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add
      (hasDerivAt_list_sum l fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The derivatives of the generators when a constant is adjoined for a root. -/
def rootVel (t : Tower n) : Fin (n + 1) → Term (n + 1) := (Tower.prim t (.const 0)).vel

theorem rootVel_last (t : Tower n) : rootVel t (Fin.last n) = .const 0 := by
  simp [rootVel, Tower.vel, Term.weaken]

theorem rootVel_castSucc (t : Tower n) (i : Fin n) :
    rootVel t i.castSucc = (t.vel i).weaken := by
  simp [rootVel, Tower.vel]

theorem rootVel_defined {t : Tower n} {p : Fin n → ℂ} (hv : ∀ i, (t.vel i).Defined p) (c : ℂ) :
    ∀ i, (rootVel t i).Defined (Fin.lastCases c p : Fin (n + 1) → ℂ) := by
  refine Fin.lastCases ?_ fun i => ?_
  · rw [rootVel_last]
    trivial
  · rw [rootVel_castSucc, Term.defined_weaken]
    exact hv i

/-- The derivative of an answer at values `p` of the generators, as a number. -/
noncomputable def Answer.derivAt (t : Tower n) (a : Answer n) (p : Fin n → ℂ) : ℂ :=
  (t.D a.field).eval p + (a.sums.map fun s => ∑ c ∈ s.roots ℂ,
    c * ((s.arg.deriv (rootVel t)).eval (Fin.lastCases c p : Fin (n + 1) → ℂ) /
      s.arg.eval (Fin.lastCases c p))).sum

/-- The function of an answer has the derivative `Answer.derivAt` wherever the generators
are functions that satisfy the differential equations of the tower. -/
theorem Answer.hasDerivAt_realize_derivAt {t : Tower n} (a : Answer n) {g : ℂ → Fin n → ℂ}
    {z : ℂ} (hg : ∀ i, HasDerivAt (fun w => g w i) ((t.vel i).eval (g z)) z)
    (ha : a.RegularAt (g z)) :
    HasDerivAt (fun w => a.realize (g w)) (a.derivAt t (g z)) z := by
  -- with a constant for the root, the generators still satisfy their equations
  have hG (c : ℂ) : ∀ i, HasDerivAt (fun w => (Fin.lastCases c (g w) : Fin (n + 1) → ℂ) i)
      ((rootVel t i).eval (Fin.lastCases c (g z) : Fin (n + 1) → ℂ)) z := by
    refine Fin.lastCases ?_ fun i => ?_
    · simpa [rootVel_last, Term.eval] using hasDerivAt_const z c
    · simpa [rootVel_castSucc] using hg i
  refine (Term.hasDerivAt_eval hg a.field ha.1).add (hasDerivAt_list_sum a.sums fun s hs => ?_)
  refine HasDerivAt.fun_sum fun c hc => ?_
  obtain ⟨dc, sc⟩ := ha.2 s hs c hc
  exact ((Term.hasDerivAt_eval (hG c) s.arg dc).clog sc).const_mul c

/-- The derivative of an answer in the field has the values `Answer.derivAt` wherever the
tower and the answer are regular. -/
theorem Answer.specializesOn_deriv {t : Tower n} (a : Answer n) {S : Set (Fin n → ℂ)}
    (hS : ∀ p ∈ S, (∀ i, (t.vel i).Defined p) ∧ a.RegularAt p) :
    SpecializesOn S (a.deriv ℂ t) (a.derivAt t) := by
  unfold Answer.deriv Answer.derivAt
  refine SpecializesOn.add ?_ (SpecializesOn.list_sum a.sums fun s hs => ?_)
  · rw [Tower.der_value]
    exact SpecializesOn.value _ fun p hp => Term.defined_deriv (hS p hp).1 a.field (hS p hp).2.1
  · refine SpecializesOn.sum _ fun c hc => ?_
    have env : ∀ i, SpecializesOn S (RootSum.env ℂ c i)
        fun p => (Fin.lastCases c p : Fin (n + 1) → ℂ) i := by
      refine Fin.lastCases ?_ fun i => ?_
      · simpa [RootSum.env] using SpecializesOn.const (S := S) c
      · simpa [RootSum.env] using SpecializesOn.gen (S := S) i
    have der : t.der ℂ (s.argAt ℂ c) = (s.arg.deriv (rootVel t)).eval (RootSum.env ℂ c) := by
      refine t.der_eval (Fin.lastCases ?_ fun i => ?_) s.arg
      · simp [RootSum.env, rootVel_last, Term.eval, Tower.der_constHom]
      · rw [rootVel_castSucc, show (t.vel i).weaken.eval (RootSum.env ℂ c) =
          Term.value ℂ (t.vel i) from Term.eval_weaken _ _ _, ← t.der_gens]
        simp [RootSum.env]
    rw [der]
    exact (SpecializesOn.const c).mul
      ((SpecializesOn.eval env _ fun p hp =>
          Term.defined_deriv (rootVel_defined (hS p hp).1 c) s.arg ((hS p hp).2.2 s hs c hc).1).div
        (SpecializesOn.eval env _ fun p hp => ((hS p hp).2.2 s hs c hc).1)
        fun p hp => Complex.slitPlane_ne_zero ((hS p hp).2.2 s hs c hc).2)

/-- **An identity in the field is an identity of functions.** Let `f = F′` hold in the field
of the tower for an answer `F`, and let the generators be functions `g` that satisfy the
differential equations of the tower at `z`. If the tower, the integrand and the answer are
defined at `z`, and the arguments of the logarithms of the answer lie off the branch cut,
then the function of `F` has the value of `f` as its derivative at `z`. -/
theorem Answer.hasDerivAt_realize {t : Tower n} {f : Term n} {a : Answer n}
    (eq : Term.value ℂ f = a.deriv ℂ t) {g : ℂ → Fin n → ℂ} {z : ℂ}
    (hg : ∀ i, HasDerivAt (fun w => g w i) ((t.vel i).eval (g z)) z)
    (hv : ∀ i, (t.vel i).Defined (g z)) (hf : f.Defined (g z)) (ha : a.RegularAt (g z)) :
    HasDerivAt (fun w => a.realize (g w)) (f.eval (g z)) z := by
  have left : SpecializesOn {g z} (Term.value ℂ f) fun p => f.eval p :=
    SpecializesOn.value f fun p hp => by rw [Set.mem_singleton_iff.mp hp]; exact hf
  have right : SpecializesOn {g z} (a.deriv ℂ t) (a.derivAt t) :=
    a.specializesOn_deriv fun p hp => by rw [Set.mem_singleton_iff.mp hp]; exact ⟨hv, ha⟩
  rw [left.unique (eq ▸ right) (Set.mem_singleton _)]
  exact a.hasDerivAt_realize_derivAt hg ha

/-- At a regular point the functions of a tower are defined and satisfy its differential
equations. -/
theorem Tower.realize_spec (t : Tower n) (z : ℂ) (hz : t.RegularAt z) :
    (∀ i, (t.vel i).Defined (t.realize z)) ∧
      ∀ i, HasDerivAt (fun w => t.realize w i) ((t.vel i).eval (t.realize z)) z := by
  induction t with
  | const => exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | @prim n t b ih =>
    obtain ⟨ht, hb, shape⟩ := hz
    obtain ⟨dv, hd⟩ := ih ht
    refine ⟨Fin.lastCases ?_ fun i => ?_, Fin.lastCases ?_ fun i => ?_⟩
    · simpa [Tower.vel, Tower.realize] using hb
    · simpa [Tower.vel, Tower.realize] using dv i
    · by_cases hn : n = 0
      · have same (w : ℂ) : t.realize w = t.realize z :=
          funext fun i => absurd i.isLt (by omega)
        have fn : (fun w => (t.prim b).realize w (Fin.last n)) =
            fun w => b.eval (t.realize z) * w := by
          funext w
          simp [Tower.realize, hn, same w]
        rw [fn]
        simpa [Tower.vel, Tower.realize] using (hasDerivAt_id z).const_mul (b.eval (t.realize z))
      · obtain ⟨u, rfl, hu⟩ := shape.resolve_left hn
        have fn : (fun w => (t.prim (.div (t.D u) u)).realize w (Fin.last n)) =
            fun w => Complex.log (u.eval (t.realize w)) := by
          funext w
          simp [Tower.realize, hn]
        rw [fn]
        simpa [Tower.vel, Tower.realize, Term.eval, Tower.D] using
          (Term.hasDerivAt_eval hd u hb.2.1).clog hu
    · simpa [Tower.vel, Tower.realize] using hd i
  | @exp n t u ih =>
    obtain ⟨ht, hu⟩ := hz
    obtain ⟨dv, hd⟩ := ih ht
    refine ⟨Fin.lastCases ?_ fun i => ?_, Fin.lastCases ?_ fun i => ?_⟩
    · simpa [Tower.vel, Tower.realize, Term.Defined] using Term.defined_deriv dv u hu
    · simpa [Tower.vel, Tower.realize] using dv i
    · have fn : (fun w => (t.exp u).realize w (Fin.last n)) =
          fun w => Complex.exp (u.eval (t.realize w)) := by
        funext w
        simp [Tower.realize]
      rw [fn]
      simpa [Tower.vel, Tower.realize, Term.eval] using
        (Term.hasDerivAt_eval hd u hu).cexp
    · simpa [Tower.vel, Tower.realize] using hd i

/-- **Soundness for functions of a complex variable.** Read the generators of the tower as
the functions `Tower.realize`: the variable, exponentials and principal logarithms. An
answer of `integrate`, read the same way, has the integrand as its derivative at every
point where the tower, the integrand and the answer are regular. -/
theorem integrate_hasDerivAt {t : Tower n} {f : Term n} {a : Answer n}
    (ht : admissible t = true) (hf : f.defined = true) (h : integrate t f = .elementary a)
    {z : ℂ} (hz : t.RegularAt z) (hfz : f.Defined (t.realize z))
    (haz : a.RegularAt (t.realize z)) :
    HasDerivAt (fun w => a.realize (t.realize w)) (f.eval (t.realize z)) z :=
  Answer.hasDerivAt_realize (integrate_sound (k := ℂ) ht hf h).2 (t.realize_spec z hz).2
    (t.realize_spec z hz).1 hfz haz

end SympyProofs.Calculus.Risch
