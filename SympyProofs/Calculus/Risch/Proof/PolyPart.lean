module

public import SympyProofs.Calculus.Risch.Proof.LiouvilleForm
public import SympyProofs.Calculus.Risch.Program.PolyPart
public import SympyProofs.Calculus.Risch.Proof.SolveStep
public import SympyProofs.Calculus.Risch.Proof.Answer
public import SympyProofs.Calculus.Risch.Proof.Pole
public import SympyProofs.Calculus.Risch.Proof.Constants
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Integration of a polynomial in the newest generator, with negative powers at an
exponential step.

An element of the field of an admissible tower has an elementary integral exactly when it is
in Liouville form. For a Laurent polynomial in an exponential generator this forces one
Risch differential equation in the preceding field for each coefficient other than the
constant one, and an elementary integral of the constant coefficient there. For a
polynomial in a primitive generator it is equivalent to a triangular system for the
coefficients of the integral, each determined up to a constant by the equation one degree
lower, together with an elementary integral in the preceding field of what remains of the
constant coefficient.

`expPart` and `primPart` solve these equations with `rde` and `limited` and integrate the
remainder one level down. An answer they return has the stated derivative, and when they
report that there is no elementary integral there is none. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial

noncomputable local instance intAlgebraPolyPart {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

local notation "ι" => algebraMap (K k n)[X] (RatFunc (K k n))

/-! ### Elementary integrals and Liouville forms -/

/-- Over an admissible tower, an element has an elementary integral exactly when it is in
Liouville form: the constants of the field are those of the ground field. -/
theorem Tower.elementary_iff_form (t : Tower n) (ht : t.Admissible k) (f : K k n) :
    t.Elementary k f ↔
      (letI : Differential (K k n) := ⟨t.der k⟩; LiouvilleForm.InLiouvilleForm (K k n) f) := by
  let : Differential (K k n) := ⟨t.der k⟩
  constructor
  · rintro ⟨κ, inst, c, u, v, rfl⟩
    refine ⟨κ, inst, fun i => constHom k n (c i), fun i => t.der_constHom (c i), u, v, ?_⟩
    rw [add_comm]
    rfl
  · rintro ⟨κ, inst, c, hc, u, v, h⟩
    choose c' hc' using fun i => (t.der_eq_zero_iff ht (c i)).mp (hc i)
    refine ⟨κ, inst, c', u, v, ?_⟩
    rw [h, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc' i]
    rfl

/-- At an admissible exponential step, a Laurent polynomial in the generator has an
elementary integral only if its constant coefficient has one over the field below and every
other coefficient solves a Risch differential equation there. -/
theorem Tower.exp_laurent_necessary {t : Tower n} {u : Term n} (ht : (t.exp u).Admissible k)
    (q : (K k n)[X]) (j : ℕ) (h : (t.exp u).Elementary k (ι q / RatFunc.X ^ j)) :
    t.Elementary k (q.coeff j) ∧ ∀ i : ℕ, i ≠ j → ∃ r : K k n,
      t.der k r + ((i : K k n) - (j : K k n)) * t.der k (Term.value k u) * r = q.coeff i := by
  have form := ((t.exp u).elementary_iff_form ht _).mp h
  let : Differential (K k n) := ⟨t.der k⟩
  let : Differential (RatFunc (K k n)) := ⟨(t.exp u).der k⟩
  let : DifferentialAlgebra (K k n) (RatFunc (K k n)) := ⟨t.der_exp_C u⟩
  have form' := (LiouvilleForm.form_iff_of_constants (K := K k n) (L := RatFunc (K k n)) (by
    intro v hv
    obtain ⟨c, hc⟩ := Tower.exp_constant ht hv
    exact ⟨c, hc.symm⟩) _).mp form
  obtain ⟨lower, eqs⟩ := LiouvilleForm.exponential_laurent_necessary (Term.value k u)
    (t.der_exp_X u) q j form'
  exact ⟨(t.elementary_iff_form ht.1 _).mpr lower, eqs⟩

/-- At an admissible primitive step with `θ′ = b`, a polynomial `q` in the generator has an
elementary integral exactly when there is a polynomial `p` of degree at most one more whose
coefficients above the constant one solve the triangular system `pᵢ₊₁′ + (i+2) b pᵢ₊₂ =
qᵢ₊₁`, and `q₀ - b p₁` has an elementary integral over the field below. -/
theorem Tower.prim_polynomial_iff {t : Tower n} {b : Term n} (ht : (t.prim b).Admissible k)
    (q : (K k n)[X]) :
    (t.prim b).Elementary k (ι q) ↔ ∃ p : (K k n)[X], p.natDegree ≤ q.natDegree + 1 ∧
      t.Elementary k (q.coeff 0 - Term.value k b * p.coeff 1) ∧
      ∀ i : ℕ, i ≤ q.natDegree →
        t.der k (p.coeff (i+1)) + ((i+2 : ℕ) : K k n) * Term.value k b * p.coeff (i+2) =
          q.coeff (i+1) := by
  rw [(t.prim b).elementary_iff_form ht]
  let : Differential (K k n) := ⟨t.der k⟩
  let : Differential (RatFunc (K k n)) := ⟨(t.prim b).der k⟩
  let : DifferentialAlgebra (K k n) (RatFunc (K k n)) := ⟨t.der_prim_C b⟩
  refine (LiouvilleForm.form_iff_of_constants (K := K k n) (L := RatFunc (K k n)) (by
    intro v hv
    obtain ⟨c, hc⟩ := Tower.prim_constant ht hv
    exact ⟨c, hc.symm⟩) _).trans ?_
  refine
    (LiouvilleForm.primitive_polynomial_iff (Term.value k b) ht.2.2 (t.der_prim_X b) q).trans ?_
  refine exists_congr fun p => and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  exact (t.elementary_iff_form ht.1 _).symm

/-- Over the constants only zero has an elementary integral. -/
theorem Tower.elementary_zero_iff (t : Tower 0) (f : K k 0) : t.Elementary k f ↔ f = 0 := by
  cases t
  constructor
  · rintro ⟨κ, _, c, u, v, rfl⟩
    simp [Tower.der]
  · rintro rfl
    exact Tower.Elementary.zero

namespace PolyPart

/-! ### Coefficient lists -/

theorem coeff_model_cons_zero (c : Term n) (cs : Poly n) :
    (Poly.model k (c :: cs)).coeff 0 = Term.value k c := by
  simp [Poly.model]

theorem coeff_model_cons_succ (c : Term n) (cs : Poly n) (m : ℕ) :
    (Poly.model k (c :: cs)).coeff (m + 1) = (Poly.model k cs).coeff m := by
  simp [Poly.model]

theorem coeff_model_succ (cs : Poly n) (m : ℕ) :
    (Poly.model k cs).coeff (m + 1) = (Poly.model k cs.tail).coeff m := by
  cases cs with
  | nil => simp [Poly.model]
  | cons c cs => simp [Poly.model]

/-- The derivation of a tower vanishes on the rational numbers. -/
theorem der_ratCast (t : Tower n) (q : ℚ) : t.der k (q : K k n) = 0 := by
  rw [← constHom_ratCast, Tower.der_constHom]

theorem value_genPow (j : ℕ) :
    Term.value k (Term.genPow n j) = (RatFunc.X : RatFunc (K k n)) ^ j := by
  induction j with
  | zero =>
    change ((1 : ℚ) : RatFunc (K k n)) = _
    simp
  | succ j ih =>
    change Term.value k (Term.genPow n j) * gens k (n + 1) (Fin.last n) = _
    rw [ih, pow_succ]
    simp [gens]

theorem inDomain_genPow (j : ℕ) : Term.InDomain k (Term.genPow n j) := by
  induction j with
  | zero => trivial
  | succ j ih => exact ⟨ih, trivial⟩

/-- A successful run of `solveFrom` applies the step to every coefficient. -/
theorem solveFrom_some {step : ℕ → Term n → Option (Term n)} :
    ∀ {ps : Poly n} {i : ℕ} {qs : Poly n}, solveFrom step i ps = some qs →
      qs.length = ps.length ∧
        ∀ m, m < ps.length → step (i + m) (Poly.coeff ps m) = some (Poly.coeff qs m)
  | [], i, qs, h => by
    obtain rfl : [] = qs := Option.some.inj h
    exact ⟨rfl, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | p :: ps, i, qs, h => by
    cases hp : step i p with
    | none => simp [solveFrom, hp] at h
    | some q =>
      cases hq : solveFrom step (i + 1) ps with
      | none => simp [solveFrom, hp, hq] at h
      | some qs' =>
        obtain rfl : q :: qs' = qs := by simpa [solveFrom, hp, hq] using h
        obtain ⟨len, ih⟩ := solveFrom_some hq
        refine ⟨by simp [len], fun m hm => ?_⟩
        cases m with
        | zero => exact hp
        | succ m =>
          have := ih m (by simpa using hm)
          rw [show i + (m + 1) = i + 1 + m by omega]
          exact this

/-- A failed run of `solveFrom` fails at one of the coefficients. -/
theorem solveFrom_none {step : ℕ → Term n → Option (Term n)} :
    ∀ {ps : Poly n} {i : ℕ}, solveFrom step i ps = none →
      ∃ m, m < ps.length ∧ step (i + m) (Poly.coeff ps m) = none
  | [], i, h => by cases h
  | p :: ps, i, h => by
    cases hp : step i p with
    | none => exact ⟨0, by simp, hp⟩
    | some q =>
      cases hq : solveFrom step (i + 1) ps with
      | none =>
        obtain ⟨m, hm, e⟩ := solveFrom_none hq
        refine ⟨m + 1, by simpa using hm, ?_⟩
        rw [show i + (m + 1) = i + 1 + m by omega]
        exact e
      | some qs => simp [solveFrom, hp, hq] at h

variable {t : Tower n}

/-! ### An exponential step -/

section Exponential

variable {u : Term n}

/-- The coefficients found at an exponential step are defined, the one of the constant term
vanishes, and each of the others solves its differential equation. -/
theorem laurent_sound (ht : (t.exp u).Admissible k) (hs : SolveSpec k t (solve t)) {j : ℕ}
    {cs rs : Poly n} (hcs : Poly.Defined k cs)
    (h : solveFrom (fun i c =>
      if i == j then some (.const 0)
      else rde t (.mul (.const ((i : Rat) - (j : Rat))) (t.D u)) c) 0 cs = some rs) :
    Poly.Defined k rs ∧ (Poly.model k rs).coeff j = 0 ∧
      ∀ i, i ≠ j → t.der k ((Poly.model k rs).coeff i) +
        ((i : K k n) - (j : K k n)) * t.der k (Term.value k u) * (Poly.model k rs).coeff i =
          (Poly.model k cs).coeff i := by
  have hdu : Term.InDomain k (t.D u) := Tower.inDomain_D ht.1 ht.2.1
  obtain ⟨len, hstep⟩ := solveFrom_some h
  have solved (i : ℕ) (hi : i < cs.length) (hij : i ≠ j) :=
    rde_sound hs (a := .mul (.const ((i : Rat) - (j : Rat))) (t.D u)) (h := Poly.coeff cs i)
      (y := Poly.coeff rs i) ⟨trivial, hdu⟩ (Poly.defined_coeff hcs i)
      (by simpa [hij] using hstep i hi)
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    have e : Poly.coeff rs i = rs[i] := by simp [Poly.coeff, hi]
    by_cases hij : i = j
    · have := hstep i (len ▸ hi)
      simp only [hij, Nat.zero_add, beq_self_eq_true, ite_true, Option.some.injEq] at this
      rw [← e, hij, ← this]
      trivial
    · rw [← e]
      exact (solved i (len ▸ hi) hij).1
  · by_cases hj : j < cs.length
    · have := hstep j hj
      simp only [Nat.zero_add, beq_self_eq_true, ite_true, Option.some.injEq] at this
      rw [← Poly.value_coeff, ← this]
      exact Poly.value_zero
    · exact Poly.coeff_model_of_length_le (by omega)
  · intro i hij
    by_cases hi : i < cs.length
    · have := (solved i hi hij).2
      rw [Poly.value_coeff, Poly.value_coeff] at this
      rw [← this, Tower.der_value]
      change _ = _ + (((i : ℚ) - (j : ℚ) : ℚ) : K k n) * Term.value k (t.D u) * _
      push_cast
      rfl
    · rw [Poly.coeff_model_of_length_le (by omega : cs.length ≤ i),
        Poly.coeff_model_of_length_le (by omega : rs.length ≤ i)]
      simp

/-- The derivative of a Laurent polynomial in an exponential generator. -/
theorem der_div_X_pow (t : Tower n) (u : Term n) (R : (K k n)[X]) (j : ℕ) :
    (t.exp u).der k (ι R / RatFunc.X ^ j) =
      ι (Tower.polyDer k (t.exp u) R - C ((j : K k n) * t.der k (Term.value k u)) * R) /
        RatFunc.X ^ j := by
  let : Differential (K k n) := ⟨t.der k⟩
  let : Differential (RatFunc (K k n)) := ⟨(t.exp u).der k⟩
  let : DifferentialAlgebra (K k n) (RatFunc (K k n)) := ⟨t.der_exp_C u⟩
  exact LiouvilleForm.deriv_div_X_pow (a := t.der k (Term.value k u)) (t.der_exp_X u) R j

/-- The Laurent polynomial is the derivative of the one found plus its constant
coefficient. -/
theorem laurent_identity (ht : (t.exp u).Admissible k) (hs : SolveSpec k t (solve t)) {j : ℕ}
    {cs rs : Poly n} (hcs : Poly.Defined k cs)
    (h : solveFrom (fun i c =>
      if i == j then some (.const 0)
      else rde t (.mul (.const ((i : Rat) - (j : Rat))) (t.D u)) c) 0 cs = some rs) :
    Term.InDomain k (.div (Poly.toTerm rs) (Term.genPow n j)) ∧
      ι (Poly.model k cs) / RatFunc.X ^ j =
        (t.exp u).der k (Term.value k (.div (Poly.toTerm rs) (Term.genPow n j))) +
          RatFunc.C (Term.value k (Poly.coeff cs j)) := by
  obtain ⟨hrs, zero, ids⟩ := laurent_sound ht hs hcs h
  have xn : (RatFunc.X : RatFunc (K k n)) ≠ 0 := RatFunc.X_ne_zero
  refine ⟨⟨Poly.inDomain_toTerm hrs, inDomain_genPow j, ?_⟩, ?_⟩
  · change Term.value k (Term.genPow n j) ≠ 0
    rw [value_genPow]
    exact pow_ne_zero j xn
  have val : Term.value k (.div (Poly.toTerm rs) (Term.genPow n j)) =
      ι (Poly.model k rs) / RatFunc.X ^ j := by
    change Term.value k (Poly.toTerm rs) / Term.value k (Term.genPow n j) = _
    rw [Poly.value_toTerm, value_genPow]
  rw [val, der_div_X_pow]
  have poly : Poly.model k cs = Tower.polyDer k (t.exp u) (Poly.model k rs) -
      C ((j : K k n) * t.der k (Term.value k u)) * Poly.model k rs +
        C (Term.value k (Poly.coeff cs j)) * X ^ j := by
    ext i
    rw [coeff_add, coeff_sub, Pole.coeff_polyDer_exp, coeff_C_mul, coeff_C_mul_X_pow]
    by_cases hij : i = j
    · subst hij
      rw [zero, Poly.value_coeff]
      simp
    · rw [ite_eq_right hij, ← ids i hij]
      ring
  conv_lhs => rw [poly]
  rw [map_add, add_div]
  congr 1
  rw [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, mul_div_assoc,
    div_self (pow_ne_zero j xn), mul_one]

/-- An answer returned at an exponential step is defined and has the Laurent polynomial as
its derivative. -/
theorem expPart_sound (ht : (t.exp u).Admissible k) (hs : SolveSpec k t (solve t))
    {descend : Term n → Result n}
    (hd : ∀ (g : Term n) (a : Answer n), Term.InDomain k g → descend g = .elementary a →
      a.Regular k ∧ Term.value k g = a.deriv k t)
    {cs : Poly n} (hcs : Poly.Defined k cs) {j : ℕ} {a : Answer (n + 1)}
    (h : expPart t u descend cs j = .elementary a) :
    a.Regular k ∧ ι (Poly.model k cs) / RatFunc.X ^ j = a.deriv k (t.exp u) := by
  rw [expPart] at h
  split at h
  · cases h
  · rename_i rs hrs
    cases hg : descend (Poly.coeff cs j) with
    | nonelementary =>
      rw [hg] at h
      cases h
    | elementary a₀ =>
      rw [hg] at h
      obtain rfl := Result.elementary.inj h
      obtain ⟨reg, val⟩ := hd _ _ (Poly.defined_coeff hcs j) hg
      obtain ⟨hW, eqn⟩ := laurent_identity ht hs hcs hrs
      have regw := Answer.regular_weaken reg
      refine ⟨⟨⟨hW, regw.1⟩, regw.2⟩, ?_⟩
      rw [Answer.deriv_addField, Answer.deriv_weaken_exp, ← val]
      exact eqn

/-- When no answer is returned at an exponential step, the Laurent polynomial has no
elementary integral. -/
theorem expPart_complete (ht : (t.exp u).Admissible k) (hs : SolveSpec k t (solve t))
    {descend : Term n → Result n}
    (hc : ∀ g : Term n, Term.InDomain k g → descend g = .nonelementary →
      ¬ t.Elementary k (Term.value k g))
    {cs : Poly n} (hcs : Poly.Defined k cs) {j : ℕ}
    (h : expPart t u descend cs j = .nonelementary) :
    ¬ (t.exp u).Elementary k (ι (Poly.model k cs) / RatFunc.X ^ j) := by
  intro form
  obtain ⟨lower, eqs⟩ := Tower.exp_laurent_necessary ht (Poly.model k cs) j form
  have hdu : Term.InDomain k (t.D u) := Tower.inDomain_D ht.1 ht.2.1
  rw [expPart] at h
  split at h
  · rename_i hnone
    obtain ⟨i, hi, hstep⟩ := solveFrom_none hnone
    by_cases hij : i = j
    · simp [hij] at hstep
    · simp only [Nat.zero_add, beq_iff_eq, hij, ite_false] at hstep
      have ok := rde_complete hs (a := .mul (.const ((i : Rat) - (j : Rat))) (t.D u))
        (h := Poly.coeff cs i) ⟨trivial, hdu⟩ (Poly.defined_coeff hcs i) (by
          obtain ⟨r, hr⟩ := eqs i hij
          refine ⟨r, ?_⟩
          rw [Poly.value_coeff, ← hr, Tower.der_value]
          change _ + (((i : ℚ) - (j : ℚ) : ℚ) : K k n) * Term.value k (t.D u) * _ = _
          push_cast
          rfl)
      rw [hstep] at ok
      cases ok
  · cases hg : descend (Poly.coeff cs j) with
    | nonelementary =>
      apply hc _ (Poly.defined_coeff hcs j) hg
      rw [Poly.value_coeff]
      exact lower
    | elementary a₀ =>
      rw [hg] at h
      cases h

end Exponential

/-! ### A primitive step -/

section Primitive

/-- The coefficients found at a primitive step are defined and solve the triangular
system. -/
theorem primSolve_sound (hs : SolveSpec k t (solve t)) {b : Term n} (hb : Term.InDomain k b) :
    ∀ {cs : Poly n} {i : ℕ} {v : Term n} {Ps : Poly n},
      Poly.Defined k cs → primSolve t b i cs = some (v, Ps) →
      Term.InDomain k v ∧ Poly.Defined k Ps ∧
        ∀ m, t.der k ((Poly.model k (v :: Ps)).coeff m) +
          ((i + m + 1 : ℕ) : K k n) * Term.value k b * (Poly.model k (v :: Ps)).coeff (m + 1) =
            (Poly.model k cs).coeff m := by
  intro cs
  induction cs with
  | nil =>
    intro i v Ps _ h
    simp only [primSolve, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨trivial, Poly.defined_nil, fun m => ?_⟩
    cases m <;> simp [Poly.model, Poly.value_zero]
  | cons c cs ih =>
    intro i v Ps hcs h
    rw [primSolve] at h
    split at h
    · cases h
    · rename_i hi Ps' hrec
      split at h
      · cases h
      · rename_i γ v' hlim
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hcs' : Poly.Defined k cs := (Poly.defined_cons.mp hcs).2
        obtain ⟨hhi, hPs, rec⟩ := ih hcs' hrec
        have hg : Term.InDomain k (.sub c (.mul (.mul (.const ((i + 1 : ℕ) : ℚ)) b) hi)) :=
          ⟨(Poly.defined_cons.mp hcs).1, ⟨trivial, hb⟩, hhi⟩
        obtain ⟨hv, dv⟩ := limited_sound hs hg hb hlim
        refine ⟨hv, Poly.defined_cons.mpr ⟨⟨hhi, trivial⟩, hPs⟩, ?_⟩
        have ne : ((i : K k n) + 1) ≠ 0 := Nat.cast_add_one_ne_zero i
        have gval : Term.value k (.sub c (.mul (.mul (.const ((i + 1 : ℕ) : ℚ)) b) hi)) =
            Term.value k c - ((i : K k n) + 1) * Term.value k b * Term.value k hi := by
          change Term.value k c -
            (((i + 1 : ℕ) : ℚ) : K k n) * Term.value k b * Term.value k hi = _
          push_cast
          rfl
        have new : Term.value k (.add hi (.const (γ / ((i + 1 : ℕ) : ℚ)))) =
            Term.value k hi + (γ : K k n) / ((i : K k n) + 1) := by
          change Term.value k hi + ((γ / ((i + 1 : ℕ) : ℚ) : ℚ) : K k n) = _
          push_cast
          rfl
        intro m
        cases m with
        | zero =>
          rw [coeff_model_cons_zero, coeff_model_cons_succ, coeff_model_cons_zero,
            coeff_model_cons_zero, dv, gval, new]
          push_cast
          field_simp
          ring
        | succ m =>
          have r := rec m
          rw [show i + (m + 1) + 1 = i + 1 + m + 1 by omega]
          simp only [coeff_model_cons_succ] at r ⊢
          have dnew : t.der k
              ((Poly.model k (.add hi (.const (γ / ((i + 1 : ℕ) : ℚ))) :: Ps')).coeff m) =
              t.der k ((Poly.model k (hi :: Ps')).coeff m) := by
            cases m with
            | zero =>
              rw [coeff_model_cons_zero, coeff_model_cons_zero]
              change t.der k (Term.value k hi + ((γ / ((i + 1 : ℕ) : ℚ) : ℚ) : K k n)) = _
              rw [map_add, der_ratCast, add_zero]
            | succ m => rw [coeff_model_cons_succ, coeff_model_cons_succ]
          rw [dnew]
          exact r

/-- A derivative that is a constant multiple of an element without a primitive vanishes. -/
theorem multiple_eq_zero {b w : K k n} (nonprim : ¬ ∃ w : K k n, t.der k w = b) {δ : k}
    (h : t.der k w = constHom k n δ * b) : δ = 0 := by
  by_contra hδ
  have hδ' : constHom k n δ ≠ 0 := (_root_.map_ne_zero _).mpr hδ
  apply nonprim
  refine ⟨w / constHom k n δ, ?_⟩
  rw [Derivation.leibniz_div, Tower.der_constHom, h]
  simp only [smul_eq_mul, mul_zero, sub_zero]
  field_simp

/-- If the triangular system has a solution in the field, `primSolve` succeeds, and the
coefficient it leaves undetermined differs from that of the solution by a constant. -/
theorem primSolve_complete (hlow : t.Admissible k) (hs : SolveSpec k t (solve t)) {b : Term n}
    (hb : Term.InDomain k b) (nonprim : ¬ ∃ w : K k n, t.der k w = Term.value k b) :
    ∀ (cs : Poly n) (i : ℕ), 0 < i → Poly.Defined k cs → ∀ p : (K k n)[X],
      (∀ m, t.der k (p.coeff (i + m)) +
        ((i + m + 1 : ℕ) : K k n) * Term.value k b * p.coeff (i + m + 1) =
          (Poly.model k cs).coeff m) →
      ∃ v Ps, primSolve t b i cs = some (v, Ps) ∧
        ∃ κ : k, Term.value k v - p.coeff i = constHom k n κ := by
  intro cs
  induction cs with
  | nil =>
    intro i hi _ p hyp
    refine ⟨.const 0, [], rfl, ?_⟩
    let : Differential (K k n) := ⟨t.der k⟩
    have deg : p.natDegree ≤ (affine 0 (Term.value k b) p).natDegree + 1 :=
      LiouvilleForm.primitive_projection_degree_le (k := 0) nonprim (by simp)
    have small : (affine 0 (Term.value k b) p).natDegree ≤ i - 1 := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro N hN
      obtain ⟨m, rfl⟩ : ∃ m, N = i + m := ⟨N - i, by omega⟩
      rw [coeff_affine]
      have := hyp m
      simp only [Poly.model_nil, coeff_zero] at this
      simp only [mul_zero, zero_mul, add_zero]
      exact this
    have top : p.coeff (i + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have d0 : t.der k (p.coeff i) = 0 := by
      have := hyp 0
      simpa [top, Poly.model_nil] using this
    obtain ⟨q, hq⟩ := (t.der_eq_zero_iff hlow _).mp d0
    exact ⟨-q, by rw [Poly.value_zero, hq, zero_sub, map_neg]⟩
  | cons c cs ih =>
    intro i hi hcs p hyp
    have hcs' : Poly.Defined k cs := (Poly.defined_cons.mp hcs).2
    obtain ⟨hiE, Ps, hrec, κ, hκ⟩ := ih (i + 1) (Nat.succ_pos i) hcs' p (fun m => by
      have := hyp (m + 1)
      rw [coeff_model_cons_succ] at this
      rw [show i + 1 + m = i + (m + 1) by omega]
      exact this)
    obtain ⟨hhi, -, -⟩ := primSolve_sound hs hb hcs' hrec
    have hg : Term.InDomain k (.sub c (.mul (.mul (.const ((i + 1 : ℕ) : ℚ)) b) hiE)) :=
      ⟨(Poly.defined_cons.mp hcs).1, ⟨trivial, hb⟩, hhi⟩
    have gval : Term.value k (.sub c (.mul (.mul (.const ((i + 1 : ℕ) : ℚ)) b) hiE)) =
        Term.value k c - ((i : K k n) + 1) * Term.value k b * Term.value k hiE := by
      change Term.value k c -
        (((i + 1 : ℕ) : ℚ) : K k n) * Term.value k b * Term.value k hiE = _
      push_cast
      rfl
    have h0 := hyp 0
    rw [coeff_model_cons_zero] at h0
    simp only [Nat.add_zero] at h0
    have hp1 : p.coeff (i + 1) = Term.value k hiE - constHom k n κ := by
      rw [← hκ]
      ring
    rw [hp1] at h0
    push_cast at h0
    have ex : ∃ (γ : k) (w : K k n), t.der k w =
        Term.value k (.sub c (.mul (.mul (.const ((i + 1 : ℕ) : ℚ)) b) hiE)) -
          constHom k n γ * Term.value k b := by
      refine ⟨-((i : k) + 1) * κ, p.coeff i, ?_⟩
      rw [gval, map_mul, map_neg, map_add, map_natCast, map_one]
      linear_combination h0
    obtain ⟨⟨γ, v⟩, hlim⟩ := Option.isSome_iff_exists.mp (limited_complete hs hg hb ex)
    obtain ⟨hv, dv⟩ := limited_sound hs hg hb hlim
    refine ⟨v, .add hiE (.const (γ / ((i + 1 : ℕ) : ℚ))) :: Ps, by
      rw [primSolve, hrec]
      dsimp only
      rw [hlim], ?_⟩
    have diff : t.der k (Term.value k v - p.coeff i) =
        constHom k n (-((i : k) + 1) * κ - (γ : k)) * Term.value k b := by
      rw [map_sub, dv, gval, map_sub, map_mul, map_neg, map_add, map_natCast, map_one,
        constHom_ratCast]
      linear_combination -h0
    have zero := multiple_eq_zero nonprim diff
    rw [zero, map_zero, zero_mul] at diff
    exact (t.der_eq_zero_iff hlow _).mp diff

variable {b : Term n}

/-- The polynomial is the derivative of the one found plus an element of the field
below. -/
theorem prim_identity (ht : (t.prim b).Admissible k) (hs : SolveSpec k t (solve t))
    {cs Ps : Poly n} {v : Term n} (hcs : Poly.Defined k cs)
    (h : primSolve t b 1 cs.tail = some (v, Ps)) :
    Poly.Defined k (.const 0 :: v :: Ps) ∧
      Term.InDomain k (.sub (Poly.coeff cs 0) (.mul b v)) ∧
      ι (Poly.model k cs) =
        (t.prim b).der k (ι (Poly.model k (.const 0 :: v :: Ps))) +
          RatFunc.C (Term.value k (.sub (Poly.coeff cs 0) (.mul b v))) := by
  have hb : Term.InDomain k b := ht.2.1
  obtain ⟨hv, hPs, ids⟩ := primSolve_sound hs hb (Poly.defined_tail hcs) h
  refine ⟨Poly.defined_cons.mpr ⟨trivial, Poly.defined_cons.mpr ⟨hv, hPs⟩⟩,
    ⟨Poly.defined_coeff hcs 0, hb, hv⟩, ?_⟩
  rw [Tower.der_algebraMap, ← RatFunc.algebraMap_C, ← map_add]
  congr 1
  ext m
  rw [coeff_add, Pole.coeff_polyDer_prim]
  cases m with
  | zero =>
    rw [coeff_model_cons_zero, coeff_model_cons_succ, coeff_model_cons_zero, coeff_C_zero,
      Poly.value_zero, map_zero (t.der k), ← Poly.value_coeff]
    change _ = 0 + ((0 + 1 : ℕ) : K k n) * Term.value k b * Term.value k v +
      (Term.value k (Poly.coeff cs 0) - Term.value k b * Term.value k v)
    push_cast
    ring
  | succ m =>
    have := ids m
    rw [show 1 + m + 1 = m + 1 + 1 by omega] at this
    rw [coeff_model_succ, ← this, coeff_C_succ, add_zero]
    simp only [coeff_model_cons_succ]

/-- An element without a primitive is not zero. -/
theorem value_ne_zero_of_nonprim (ht : (t.prim b).Admissible k) : Term.value k b ≠ 0 :=
  fun hz => ht.2.2 ⟨0, by rw [map_zero, hz]⟩

/-- An answer returned at a primitive step is defined and has the polynomial as its
derivative. -/
theorem primPart_sound (ht : (t.prim b).Admissible k) (hs : SolveSpec k t (solve t))
    {descend : Term n → Result n}
    (hd : ∀ (g : Term n) (a : Answer n), Term.InDomain k g → descend g = .elementary a →
      a.Regular k ∧ Term.value k g = a.deriv k t)
    {cs : Poly n} (hcs : Poly.Defined k cs) {a : Answer (n + 1)}
    (h : primPart t b descend cs = .elementary a) :
    a.Regular k ∧ ι (Poly.model k cs) = a.deriv k (t.prim b) := by
  have hb : Term.InDomain k b := ht.2.1
  cases hps : primSolve t b 1 cs.tail with
  | none => simp [primPart, hps] at h
  | some vP =>
    obtain ⟨v, Ps⟩ := vP
    obtain ⟨hdef, hg, eqn⟩ := prim_identity ht hs hcs hps
    cases hdg : descend (.sub (Poly.coeff cs 0) (.mul b v)) with
    | elementary a₀ =>
      obtain rfl : a₀.weaken.addField (Poly.toTerm (.const 0 :: v :: Ps)) = a := by
        simpa [primPart, hps, hdg] using h
      obtain ⟨reg, val⟩ := hd _ _ hg hdg
      have regw := Answer.regular_weaken reg
      refine ⟨⟨⟨Poly.inDomain_toTerm hdef, regw.1⟩, regw.2⟩, ?_⟩
      rw [Answer.deriv_addField, Answer.deriv_weaken_prim, ← val, Poly.value_toTerm]
      exact eqn
    | nonelementary =>
      cases hdb : descend b with
      | elementary a₁ => simp [primPart, hps, hdg, hdb] at h
      | nonelementary =>
        cases hsc : Term.scalar? (.div (.sub (Poly.coeff cs 0) (.mul b v)) b) with
        | none => simp [primPart, hps, hdg, hdb, hsc] at h
        | some c =>
          obtain rfl : (⟨Poly.toTerm (.const 0 :: .add v (.const c) :: Ps), []⟩ :
              Answer (n + 1)) = a := by
            simpa [primPart, hps, hdg, hdb, hsc] using h
          have bne := value_ne_zero_of_nonprim ht
          have gb : Term.value k (.sub (Poly.coeff cs 0) (.mul b v)) =
              (c : K k n) * Term.value k b := by
            have := (Term.scalar?_eq_some_iff (k := k)
              (e := .div (.sub (Poly.coeff cs 0) (.mul b v)) b) ⟨hg, hb, bne⟩ c).mp hsc
            exact (div_eq_iff bne).mp this
          have hdef' : Poly.Defined k (.const 0 :: .add v (.const c) :: Ps) :=
            Poly.defined_cons.mpr ⟨trivial, Poly.defined_cons.mpr
              ⟨⟨(Poly.defined_cons.mp (Poly.defined_cons.mp hdef).2).1, trivial⟩,
                (Poly.defined_cons.mp (Poly.defined_cons.mp hdef).2).2⟩⟩
          refine ⟨⟨Poly.inDomain_toTerm hdef', fun s hs => by cases hs⟩, ?_⟩
          have model' : Poly.model k (.const 0 :: .add v (.const c) :: Ps) =
              Poly.model k (.const 0 :: v :: Ps) + C (c : K k n) * X := by
            rw [Poly.model_cons, Poly.model_cons, Poly.model_cons, Poly.model_cons]
            change _ + X * (C (Term.value k v + (c : K k n)) + _) = _
            rw [C_add]
            ring
          have dcx : (t.prim b).der k (ι (C (c : K k n) * X)) =
              RatFunc.C ((c : K k n) * Term.value k b) := by
            rw [map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X, Derivation.leibniz,
              Tower.der_prim_X, Tower.der_prim_C, der_ratCast, map_zero, smul_zero, add_zero,
              smul_eq_mul, map_mul]
          rw [Answer.deriv]
          change _ = (t.prim b).der k (Term.value k (Poly.toTerm _)) + 0
          rw [add_zero, Poly.value_toTerm, model', map_add, map_add, dcx, ← gb]
          exact eqn

/-- When no answer is returned at a primitive step, the polynomial has no elementary
integral, provided the generator is adjoined over the constants or its derivative has an
elementary integral over the field below. -/
theorem primPart_complete (ht : (t.prim b).Admissible k) (hs : SolveSpec k t (solve t))
    {descend : Term n → Result n}
    (hd : ∀ (g : Term n) (a : Answer n), Term.InDomain k g → descend g = .elementary a →
      a.Regular k ∧ Term.value k g = a.deriv k t)
    (hc : ∀ g : Term n, Term.InDomain k g → descend g = .nonelementary →
      ¬ t.Elementary k (Term.value k g))
    (hb : n = 0 ∨ t.Elementary k (Term.value k b))
    {cs : Poly n} (hcs : Poly.Defined k cs)
    (h : primPart t b descend cs = .nonelementary) :
    ¬ (t.prim b).Elementary k (ι (Poly.model k cs)) := by
  intro form
  have hbd : Term.InDomain k b := ht.2.1
  have bne := value_ne_zero_of_nonprim ht
  obtain ⟨p, deg, lower, eqs⟩ := (Tower.prim_polynomial_iff ht (Poly.model k cs)).mp form
  obtain ⟨v, Ps, hps, κ, hκ⟩ := primSolve_complete ht.1 hs hbd ht.2.2 cs.tail 1 Nat.one_pos
    (Poly.defined_tail hcs) p (fun m => by
      rw [← coeff_model_succ, show 1 + m + 1 = m + 2 by omega, Nat.add_comm 1 m]
      by_cases le : m ≤ (Poly.model k cs).natDegree
      · exact eqs m le
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < m + 1),
          coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < m + 2),
          coeff_eq_zero_of_natDegree_lt (by omega : (Poly.model k cs).natDegree < m + 1)]
        simp)
  obtain ⟨-, hg, -⟩ := prim_identity ht hs hcs hps
  cases hdg : descend (.sub (Poly.coeff cs 0) (.mul b v)) with
  | elementary a₀ => simp [primPart, hps, hdg] at h
  | nonelementary =>
    have nog := hc _ hg hdg
    cases hdb : descend b with
    | elementary a₁ =>
      apply nog
      have eb : t.Elementary k (Term.value k b) := by
        rw [(hd _ _ hbd hdb).2]
        exact Answer.deriv_elementary t a₁
      have e : Term.value k (.sub (Poly.coeff cs 0) (.mul b v)) =
          ((Poly.model k cs).coeff 0 - Term.value k b * p.coeff 1) -
            constHom k n κ * Term.value k b := by
        change Term.value k (Poly.coeff cs 0) - Term.value k b * Term.value k v = _
        rw [Poly.value_coeff]
        linear_combination -Term.value k b * hκ
      rw [e]
      exact lower.sub (eb.const_mul κ)
    | nonelementary =>
      rcases hb with rfl | eb
      · have val := Term.value_evalRat (k := k)
          (.div (.sub (Poly.coeff cs 0) (.mul b v)) b)
        have found := (Term.scalar?_eq_some_iff (k := k)
          (e := .div (.sub (Poly.coeff cs 0) (.mul b v)) b) ⟨hg, hbd, bne⟩ _).mpr val.symm
        simp [primPart, hps, hdg, hdb, found] at h
      · exact hc _ hbd hdb eb

end Primitive

end PolyPart

end SympyProofs.Calculus.Risch
