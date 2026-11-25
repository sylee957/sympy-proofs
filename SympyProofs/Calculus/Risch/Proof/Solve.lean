module

public import SympyProofs.Calculus.Risch.Program.Admissible
public import SympyProofs.Calculus.Risch.Proof.SolveBounds
public import SympyProofs.Calculus.Risch.Proof.SolveStep

/-! Part (b) of Risch's Main Theorem for every tower accepted by `admissible`: such a tower
is admissible over every constant field of characteristic zero, and `solve` describes all
solutions of the parametric equation in its field. Both are proved together by induction on
the tower, since the test for a primitive uses the solver of the field below. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

/-- A tower accepted by the test is admissible, and `solve` meets its specification. -/
theorem admissible_spec : ∀ {n : ℕ} (t : Tower n), admissible t = true →
    t.Admissible k ∧ SolveSpec k t (solve t)
  | _, .const, _ => ⟨trivial, Solve.constSolve_spec⟩
  | _, .prim t b, h => by
    simp only [admissible, Bool.and_eq_true] at h
    obtain ⟨⟨⟨ht, hb⟩, hr⟩, -⟩ := h
    obtain ⟨adm, st⟩ : t.Admissible k ∧ SolveSpec k t (solve t) := admissible_spec t ht
    have db : Term.InDomain k b := (Term.defined_iff b).mp hb
    have nonprim : ¬ ∃ v : K k _, t.der k v = Term.value k b := by
      rintro ⟨v, hv⟩
      have some := rde_complete st (a := .const 0) (h := b) trivial db ⟨v, by
        rw [Term.value_const, Rat.cast_zero, zero_mul, add_zero]
        exact hv⟩
      rw [Option.isNone_iff_eq_none.mp hr] at some
      cases some
    have top : (t.prim b).Admissible k := ⟨adm, db, nonprim⟩
    refine ⟨top, fun f gs hf hg => ?_⟩
    exact Solve.stepSolve_spec (t := t.prim b) st (Solve.pieces_spec top hf hg)
      (fun y c _ eqn => Solve.prim_denominator top hf hg y c eqn)
      (fun p Y eq => Solve.prim_bound top (Solve.pieces_spec top hf hg).good st eq)
  | _, .exp t u, h => by
    simp only [admissible, Bool.and_eq_true] at h
    obtain ⟨⟨ht, hu⟩, ok⟩ := h
    obtain ⟨adm, st⟩ : t.Admissible k ∧ SolveSpec k t (solve t) := admissible_spec t ht
    have du : Term.InDomain k u := (Term.defined_iff u).mp hu
    have top : (t.exp u).Admissible k := Rel.exp_admissible adm du ok
    refine ⟨top, fun f gs hf hg => ?_⟩
    exact Solve.stepSolve_spec (t := t.exp u) st (Solve.pieces_spec top hf hg)
      (fun y c _ eqn => Solve.exp_denominator top ok hf hg y c eqn)
      (fun p Y eq => Solve.exp_bound top ok (Solve.pieces_spec top hf hg).good (solve t) eq)

/-- A tower accepted by the test is admissible over every constant field. -/
theorem admissible_sound {t : Tower n} (h : admissible t = true) : t.Admissible k :=
  (admissible_spec t h).1

/-- `solve` describes all solutions of `y′ + f y = Σ cᵢ gᵢ` in the field of an accepted
tower. -/
theorem solve_spec {t : Tower n} (h : admissible t = true) : SolveSpec k t (solve t) :=
  (admissible_spec t h).2

end SympyProofs.Calculus.Risch
