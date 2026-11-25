module

public import SympyProofs.Calculus.Risch.Program.Integrate
public import SympyProofs.Calculus.Risch.Proof.Solve
public import SympyProofs.Calculus.Risch.Proof.Hermite
public import SympyProofs.Calculus.Risch.Proof.PolyPart
public import SympyProofs.Calculus.Risch.Proof.Residue
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Part (a) of Risch's Main Theorem: `integrate` decides elementary integration in the field
of every tower accepted by `admissible`, over an algebraically closed constant field of
characteristic zero.

* `integrate_sound`: an answer returned by `integrate` is defined in the field and has the
  integrand as its derivative.
* `integrate_complete`: when `integrate` returns `nonelementary`, the integrand is not the
  derivative of an element of the field plus a combination, with constant coefficients, of
  logarithmic derivatives of elements of the field.

* `integrate_no_primitive`: by Liouville's theorem, the integrand then has no primitive in
  any elementary extension of the field.

`integrateChecked_sound` and `integrateChecked_complete` state the same for the program that
also tests the input conditions, with no hypothesis on the input. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial

noncomputable local instance intAlgebraIntegrate {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

local notation "ι" => algebraMap (K k n)[X] (RatFunc (K k n))

/-! ### Elementary forms -/

/-- A finite sum of elements with elementary integrals has one. -/
theorem Tower.Elementary.list_sum {t : Tower n} :
    ∀ l : List (K k n), (∀ x ∈ l, t.Elementary k x) → t.Elementary k l.sum
  | [], _ => Tower.Elementary.zero
  | x :: l, h => by
    rw [List.sum_cons]
    exact (h x List.mem_cons_self).add
      (Tower.Elementary.list_sum l fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- A term written as a logarithmic derivative has an elementary integral. -/
theorem Tower.elementary_of_isLog {t : Tower n} {b : Term n} (hb : Term.InDomain k b)
    (h : t.isLog b = true) : t.Elementary k (Term.value k b) := by
  cases b with
  | div d u =>
    have e : d = t.D u := by simpa [Tower.isLog] using h
    have : Term.value k (.div d u) = t.der k (Term.value k u) / Term.value k u := by
      rw [Tower.der_value, ← e]
      rfl
    rw [this]
    exact Tower.Elementary.logDeriv _
  | _ => simp [Tower.isLog] at h

/-! ### The polynomial part at either kind of step -/

namespace PolyPart

variable {t : Tower (n + 1)} {descend : Term n → Result n}

theorem polyPart_sound (ht : t.Admissible k) (hs : SolveSpec k t.parent (solve t.parent))
    (hd : ∀ (g : Term n) (a : Answer n), Term.InDomain k g → descend g = .elementary a →
      a.Regular k ∧ Term.value k g = a.deriv k t.parent)
    {cs : Poly n} (hcs : Poly.Defined k cs) {j : ℕ}
    (hj : ∀ (t' : Tower n) (b : Term n), t = .prim t' b → j = 0) {a : Answer (n + 1)}
    (h : polyPart t descend cs j = .elementary a) :
    a.Regular k ∧ ι (Poly.model k cs) / RatFunc.X ^ j = a.deriv k t := by
  cases t with
  | prim t b =>
    obtain rfl := hj t b rfl
    rw [pow_zero, div_one]
    exact primPart_sound ht hs hd hcs h
  | exp t u => exact expPart_sound ht hs hd hcs h

theorem polyPart_complete (ht : t.Admissible k) (hs : SolveSpec k t.parent (solve t.parent))
    (hd : ∀ (g : Term n) (a : Answer n), Term.InDomain k g → descend g = .elementary a →
      a.Regular k ∧ Term.value k g = a.deriv k t.parent)
    (hc : ∀ g : Term n, Term.InDomain k g → descend g = .nonelementary →
      ¬ t.parent.Elementary k (Term.value k g))
    (hb : ∀ (t' : Tower n) (b : Term n), t = .prim t' b →
      n = 0 ∨ t'.Elementary k (Term.value k b))
    {cs : Poly n} (hcs : Poly.Defined k cs) {j : ℕ}
    (hj : ∀ (t' : Tower n) (b : Term n), t = .prim t' b → j = 0)
    (h : polyPart t descend cs j = .nonelementary) :
    ¬ t.Elementary k (ι (Poly.model k cs) / RatFunc.X ^ j) := by
  cases t with
  | prim t b =>
    obtain rfl := hj t b rfl
    rw [pow_zero, div_one]
    exact primPart_complete ht hs hd hc (hb t b rfl) hcs h
  | exp t u => exact expPart_complete ht hs hc hcs h

end PolyPart

/-! ### One step of the recursion -/

namespace Step

/-- The polynomial quotient of the reduced fraction. -/
def quotient (t : Tower (n + 1)) (f : Term (n + 1)) : Poly n :=
  Poly.quot (Hermite.reduceTerm t f).Ar (Hermite.reduceTerm t f).Dr

/-- The numerator of the proper fraction left for the residue step. -/
def numerator (t : Tower (n + 1)) (f : Term (n + 1)) : Poly n :=
  Poly.trim (Poly.norm (Poly.rem (Hermite.reduceTerm t f).Ar (Hermite.reduceTerm t f).Dr))

/-- The numerator of the polynomial part, over the power of the generator split off. -/
def polynomial (t : Tower (n + 1)) (f : Term (n + 1)) (Q : Term n) : Poly n :=
  Poly.norm (Poly.add (Hermite.reduceTerm t f).L1
    (Poly.mul (Poly.add (quotient t f) [Q]) (Poly.mono (Hermite.reduceTerm t f).k (.const 1))))

theorem integrateStep_eq (t : Tower (n + 1)) (descend : Term n → Result n) (f : Term (n + 1)) :
    integrateStep t descend f =
      match Residue.logPart t (numerator t f) (Hermite.reduceTerm t f).Dr with
      | none => .nonelementary
      | some (pieces, Q) =>
        match PolyPart.polyPart t descend (polynomial t f Q) (Hermite.reduceTerm t f).k with
        | .nonelementary => .nonelementary
        | .elementary a =>
          .elementary ⟨.add (Hermite.reduceTerm t f).g a.field,
            a.sums ++ pieces.map Residue.toRootSum⟩ := rfl

variable {t : Tower (n + 1)} {f : Term (n + 1)}

/-- After the reduction, `f = g′ + P + A / Dr + L1 / θᵏ`, and `A / Dr` meets the input
conditions of the residue step. -/
theorem decomposition (ht : t.Admissible k) (hf : Term.InDomain k f) :
    Residue.Input k t (numerator t f) (Hermite.reduceTerm t f).Dr ∧
      Poly.Defined k (quotient t f) ∧
      Term.value k f = t.der k (Term.value k (Hermite.reduceTerm t f).g) +
        ι (Poly.model k (quotient t f)) +
        ι (Poly.model k (numerator t f)) / ι (Poly.model k (Hermite.reduceTerm t f).Dr) +
        ι (Poly.model k (Hermite.reduceTerm t f).L1) / RatFunc.X ^ (Hermite.reduceTerm t f).k := by
  have sp := Hermite.reduceTerm_spec ht hf
  obtain ⟨idv, dq, dr, lenr⟩ := Poly.rem_spec sp.dA sp.dD sp.nD
  obtain ⟨mA, dA, -, -⟩ := Poly.trim_spec (Poly.defined_norm dr)
  rw [Poly.model_norm dr] at mA
  have D0 : ι (Poly.model k (Hermite.reduceTerm t f).Dr) ≠ 0 :=
    RatFunc.algebraMap_ne_zero sp.nD.model_ne_zero
  refine ⟨⟨ht, dA, sp.dD, sp.nD, sp.squarefree, sp.normal, ?_, ?_⟩, dq, ?_⟩
  · rw [numerator, mA]
    have c := sp.cop
    rw [idv, add_comm] at c
    exact c.of_add_mul_left_left
  · rw [numerator, mA]
    exact Poly.degree_model_lt sp.nD lenr
  · rw [sp.value, numerator, mA, quotient, idv, map_add, map_mul]
    field_simp
    ring

/-- The value of the polynomial handed to the polynomial part. -/
theorem model_polynomial (ht : t.Admissible k) (hf : Term.InDomain k f) {Q : Term n}
    (hQ : Term.InDomain k Q) :
    Poly.Defined k (polynomial t f Q) ∧
      Poly.model k (polynomial t f Q) = Poly.model k (Hermite.reduceTerm t f).L1 +
        (Poly.model k (quotient t f) + C (Term.value k Q)) * X ^ (Hermite.reduceTerm t f).k := by
  have sp := Hermite.reduceTerm_spec ht hf
  have dP := (decomposition ht hf).2.1
  have d : Poly.Defined k (Poly.add (Hermite.reduceTerm t f).L1
      (Poly.mul (Poly.add (quotient t f) [Q])
        (Poly.mono (Hermite.reduceTerm t f).k (.const 1)))) :=
    Poly.defined_add sp.dL (Poly.defined_mul
      (Poly.defined_add dP (Poly.defined_cons.mpr ⟨hQ, Poly.defined_nil⟩))
      (Poly.defined_mono _ trivial))
  refine ⟨Poly.defined_norm d, ?_⟩
  rw [polynomial, Poly.model_norm d, Poly.model_add, Poly.model_mul, Poly.model_add,
    Poly.model_cons, Poly.model_nil, Poly.model_mono, Term.value_const, Rat.cast_one, C_1,
    mul_zero, add_zero, one_mul]

/-- With the logarithms found, `f = g′ + Σ (sums of logarithms)′ + cs / θᵏ`. -/
theorem identity [IsAlgClosed k] (ht : t.Admissible k) (hf : Term.InDomain k f)
    {pieces : List (Poly n × Residue.BPoly n)} {Q : Term n}
    (hl : Residue.logPart t (numerator t f) (Hermite.reduceTerm t f).Dr = some (pieces, Q)) :
    Poly.Defined k (polynomial t f Q) ∧
      (∀ pc ∈ pieces, (Residue.toRootSum pc).Regular k) ∧
      Term.value k f = t.der k (Term.value k (Hermite.reduceTerm t f).g) +
        (pieces.map fun pc => (Residue.toRootSum pc).deriv k t).sum +
        ι (Poly.model k (polynomial t f Q)) / RatFunc.X ^ (Hermite.reduceTerm t f).k := by
  obtain ⟨inp, -, val⟩ := decomposition ht hf
  obtain ⟨dQ, reg, frac⟩ := Residue.logPart_sound inp hl
  obtain ⟨dcs, mcs⟩ := model_polynomial ht hf dQ
  refine ⟨dcs, reg, ?_⟩
  have X0 : (RatFunc.X : RatFunc (K k n)) ^ (Hermite.reduceTerm t f).k ≠ 0 :=
    pow_ne_zero _ RatFunc.X_ne_zero
  rw [val, frac, mcs, map_add, map_mul, map_add, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  field_simp
  ring

variable [IsAlgClosed k] {descend : Term n → Result n}

theorem integrateStep_sound (ht : t.Admissible k)
    (hs : SolveSpec k t.parent (solve t.parent))
    (hd : ∀ (g : Term n) (a : Answer n), Term.InDomain k g → descend g = .elementary a →
      a.Regular k ∧ Term.value k g = a.deriv k t.parent)
    (hf : Term.InDomain k f) {a : Answer (n + 1)}
    (h : integrateStep t descend f = .elementary a) :
    a.Regular k ∧ Term.value k f = a.deriv k t := by
  have sp := Hermite.reduceTerm_spec ht hf
  rw [integrateStep_eq] at h
  cases hl : Residue.logPart t (numerator t f) (Hermite.reduceTerm t f).Dr with
  | none =>
    rw [hl] at h
    cases h
  | some pq =>
    obtain ⟨pieces, Q⟩ := pq
    rw [hl] at h
    dsimp only at h
    obtain ⟨dcs, reg, val⟩ := identity ht hf hl
    cases hp : PolyPart.polyPart t descend (polynomial t f Q) (Hermite.reduceTerm t f).k with
    | nonelementary =>
      rw [hp] at h
      cases h
    | elementary a' =>
      rw [hp] at h
      obtain rfl := Result.elementary.inj h
      obtain ⟨areg, aval⟩ := PolyPart.polyPart_sound ht hs hd dcs
        (fun t' b e => by subst e; rfl) hp
      refine ⟨⟨⟨sp.dg, areg.1⟩, fun s hs' => ?_⟩, ?_⟩
      · rcases List.mem_append.mp hs' with h1 | h1
        · exact areg.2 s h1
        · obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp h1
          exact reg pc hpc
      · rw [val, aval, Answer.deriv, Answer.deriv, List.map_append, List.sum_append,
          List.map_map]
        change _ = t.der k (Term.value k (Hermite.reduceTerm t f).g + Term.value k a'.field) + _
        rw [map_add]
        have : (List.map (RootSum.deriv k t ∘ Residue.toRootSum) pieces) =
            pieces.map fun pc => (Residue.toRootSum pc).deriv k t := rfl
        rw [this]
        ring

theorem integrateStep_complete (ht : t.Admissible k)
    (hs : SolveSpec k t.parent (solve t.parent))
    (hd : ∀ (g : Term n) (a : Answer n), Term.InDomain k g → descend g = .elementary a →
      a.Regular k ∧ Term.value k g = a.deriv k t.parent)
    (hc : ∀ g : Term n, Term.InDomain k g → descend g = .nonelementary →
      ¬ t.parent.Elementary k (Term.value k g))
    (hb : ∀ (t' : Tower n) (b : Term n), t = .prim t' b →
      n = 0 ∨ t'.Elementary k (Term.value k b))
    (hf : Term.InDomain k f) (h : integrateStep t descend f = .nonelementary) :
    ¬ t.Elementary k (Term.value k f) := by
  intro el
  have sp := Hermite.reduceTerm_spec ht hf
  rw [integrateStep_eq] at h
  cases hl : Residue.logPart t (numerator t f) (Hermite.reduceTerm t f).Dr with
  | none =>
    obtain ⟨inp, -, val⟩ := decomposition ht hf
    refine Residue.logPart_complete inp (L := ι (Poly.model k (quotient t f)) +
      ι (Poly.model k (Hermite.reduceTerm t f).L1) / RatFunc.X ^ (Hermite.reduceTerm t f).k)
      (fun p hp hpd => ?_) hl ?_
    · refine SimplePole.Integral.add hp (SimplePole.integral_algebraMap hp _)
        ⟨Poly.model k (Hermite.reduceTerm t f).L1, X ^ (Hermite.reduceTerm t f).k,
          sp.away p hp hpd, ?_⟩
      rw [map_pow, RatFunc.algebraMap_X]
      exact div_mul_cancel₀ _ (pow_ne_zero _ RatFunc.X_ne_zero)
    · have := el.sub (Tower.Elementary.der (Term.value k (Hermite.reduceTerm t f).g))
      rw [val] at this
      convert this using 1
      ring
  | some pq =>
    obtain ⟨pieces, Q⟩ := pq
    rw [hl] at h
    dsimp only at h
    obtain ⟨dcs, reg, val⟩ := identity ht hf hl
    cases hp : PolyPart.polyPart t descend (polynomial t f Q) (Hermite.reduceTerm t f).k with
    | elementary a' =>
      rw [hp] at h
      cases h
    | nonelementary =>
      refine PolyPart.polyPart_complete ht hs hd hc hb dcs (fun t' b e => by subst e; rfl) hp ?_
      have sums : t.Elementary k
          (pieces.map fun pc => (Residue.toRootSum pc).deriv k t).sum :=
        Tower.Elementary.list_sum _ fun x hx => by
          obtain ⟨pc, -, rfl⟩ := List.mem_map.mp hx
          exact RootSum.deriv_elementary t _
      have := (el.sub (Tower.Elementary.der (Term.value k (Hermite.reduceTerm t f).g))).sub sums
      rw [val] at this
      convert this using 1
      ring

end Step

/-! ### The main theorems -/

variable [IsAlgClosed k]

/-- `integrate` is sound and complete in the field of every tower accepted by
`admissible`. -/
theorem integrate_spec : ∀ {n : ℕ} (t : Tower n), admissible t = true →
    (∀ (f : Term n) (a : Answer n), Term.InDomain k f → integrate t f = .elementary a →
      a.Regular k ∧ Term.value k f = a.deriv k t) ∧
    (∀ f : Term n, Term.InDomain k f → integrate t f = .nonelementary →
      ¬ t.Elementary k (Term.value k f))
  | _, .const, _ => by
    refine ⟨fun f a hf h => ?_, fun f hf h => ?_⟩
    · by_cases z : f.isZero = true
      · rw [integrate, ite_eq_left z] at h
        obtain rfl := Result.elementary.inj h
        refine ⟨⟨trivial, by simp⟩, ?_⟩
        rw [(Term.isZero_iff hf).mp z, Answer.deriv, Term.value_const, Rat.cast_zero, map_zero,
          List.map_nil, List.sum_nil, add_zero]
      · rw [integrate, ite_eq_right z] at h
        cases h
    · by_cases z : f.isZero = true
      · rw [integrate, ite_eq_left z] at h
        cases h
      · rw [Tower.elementary_zero_iff]
        exact fun e => z ((Term.isZero_iff hf).mpr e)
  | _, .prim (n := n) t b, h => by
    have top : (t.prim b).Admissible k := admissible_sound h
    simp only [admissible, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨ht, -⟩, -⟩, hlog⟩ := h
    obtain ⟨snd, cmp⟩ : (∀ (f : Term _) (a : Answer _), Term.InDomain k f →
        integrate t f = .elementary a → a.Regular k ∧ Term.value k f = a.deriv k t) ∧
        (∀ f : Term _, Term.InDomain k f → integrate t f = .nonelementary →
          ¬ t.Elementary k (Term.value k f)) := integrate_spec t ht
    have hs : SolveSpec k t (solve t) := solve_spec ht
    have hb : n = 0 ∨ t.Elementary k (Term.value k b) :=
      hlog.imp id fun l => Tower.elementary_of_isLog top.2.1 l
    refine ⟨fun f a hf e => Step.integrateStep_sound top hs snd hf e, fun f hf e => ?_⟩
    exact Step.integrateStep_complete top hs snd cmp
      (fun t' b' eq => by cases eq; exact hb) hf e
  | _, .exp t u, h => by
    have top : (t.exp u).Admissible k := admissible_sound h
    simp only [admissible, Bool.and_eq_true] at h
    obtain ⟨⟨ht, -⟩, -⟩ := h
    obtain ⟨snd, cmp⟩ : (∀ (f : Term _) (a : Answer _), Term.InDomain k f →
        integrate t f = .elementary a → a.Regular k ∧ Term.value k f = a.deriv k t) ∧
        (∀ f : Term _, Term.InDomain k f → integrate t f = .nonelementary →
          ¬ t.Elementary k (Term.value k f)) := integrate_spec t ht
    have hs : SolveSpec k t (solve t) := solve_spec ht
    refine ⟨fun f a hf e => Step.integrateStep_sound top hs snd hf e, fun f hf e => ?_⟩
    exact Step.integrateStep_complete top hs snd cmp (fun t' b' eq => by cases eq) hf e

variable {t : Tower n} {f : Term n}

/-- **Soundness.** In the field of a tower accepted by `admissible`, an answer returned for
a defined integrand is defined, and its derivative is the integrand. -/
theorem integrate_sound (ht : admissible t = true) (hf : f.defined = true) {a : Answer n}
    (h : integrate t f = .elementary a) : a.Regular k ∧ Term.value k f = a.deriv k t :=
  (integrate_spec t ht).1 f a ((Term.defined_iff f).mp hf) h

/-- **Completeness.** In the field of a tower accepted by `admissible`, a defined integrand
for which `integrate` returns `nonelementary` has no elementary integral: it is not of the
form `v′ + Σ cᵢ uᵢ′ / uᵢ` with `v`, `uᵢ` in the field and constants `cᵢ`. -/
theorem integrate_complete (ht : admissible t = true) (hf : f.defined = true)
    (h : integrate t f = .nonelementary) : ¬ t.Elementary k (Term.value k f) :=
  (integrate_spec t ht).2 f ((Term.defined_iff f).mp hf) h

/-- `integrateChecked` answers exactly when both input conditions hold. -/
theorem integrateChecked_eq_some_iff (r : Result n) :
    integrateChecked t f = some r ↔
      admissible t = true ∧ f.defined = true ∧ integrate t f = r := by
  unfold integrateChecked
  by_cases c : (admissible t && f.defined) = true
  · rw [ite_eq_left c, Option.some.injEq]
    rw [Bool.and_eq_true] at c
    exact ⟨fun e => ⟨c.1, c.2, e⟩, fun e => e.2.2⟩
  · rw [ite_eq_right c]
    rw [Bool.and_eq_true] at c
    exact ⟨fun e => (by cases e), fun e => (c ⟨e.1, e.2.1⟩).elim⟩

/-- An answer of `integrateChecked` is defined in the field of an admissible tower, and its
derivative is the integrand. No condition on the input is assumed. -/
theorem integrateChecked_sound {a : Answer n} (h : integrateChecked t f = some (.elementary a)) :
    t.Admissible k ∧ Term.InDomain k f ∧ a.Regular k ∧ Term.value k f = a.deriv k t := by
  obtain ⟨ht, hf, e⟩ := (integrateChecked_eq_some_iff _).mp h
  exact ⟨admissible_sound ht, (Term.defined_iff f).mp hf, integrate_sound ht hf e⟩

/-- When `integrateChecked` answers `nonelementary`, the tower is admissible, the integrand
is defined, and it has no elementary integral. No condition on the input is assumed. -/
theorem integrateChecked_complete (h : integrateChecked t f = some .nonelementary) :
    t.Admissible k ∧ Term.InDomain k f ∧ ¬ t.Elementary k (Term.value k f) := by
  obtain ⟨ht, hf, e⟩ := (integrateChecked_eq_some_iff _).mp h
  exact ⟨admissible_sound ht, (Term.defined_iff f).mp hf, integrate_complete ht hf e⟩

/-! ### Liouville's theorem -/

open Differential in
/-- **No primitive in any elementary extension.** When `integrate` returns `nonelementary`,
the integrand has no primitive in any field obtained from the field of the tower by finitely
many adjunctions of algebraic elements, exponentials and logarithms that add no constants
below the last one. -/
theorem integrate_no_primitive (ht : admissible t = true) (hf : f.defined = true)
    (h : integrate t f = .nonelementary) :
    letI : Differential (K k n) := ⟨t.der k⟩
    ∀ (L : Type) [Field L] [Differential L] [Algebra (K k n) L],
      LiouvilleForm.ElementaryTower (K k n) L →
        ∀ v : L, v′ ≠ algebraMap (K k n) L (Term.value k f) := by
  let : Differential (K k n) := ⟨t.der k⟩
  intro L _ _ _ tower v hv
  exact integrate_complete ht hf h
    ((t.elementary_iff_form (admissible_sound ht) _).mpr (tower.form_of_primitive _ v hv))

end SympyProofs.Calculus.Risch
