module

public import SympyProofs.Calculus.Risch.Proof.SolvePieces
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Part (b) of the Main Theorem at a tower step, given a solver for the preceding field
(Risch 1969, pp. 184–187), and over the constants. The two kinds of step differ only in the
denominator of the solutions and in the degree bound, which enter here as hypotheses.

A solution `y` of `y′ + f y = Σ cᵢ gᵢ` is written `Y / P` with the common denominator `P`,
and the equation becomes `R Y′ + S Y = Σ cᵢ Gᵢ` for the polynomial `Y`, which `solvePoly`
solves below the degree bound.

Two solvers are read off part (b): one Risch differential equation `y′ + a y = h` is the
parametric equation with its constant fixed to one, and integration up to a constant
multiple of a second element is the equation `y′ = c₁ g + c₂ b` with `c₁ = 1`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial Linear

noncomputable local instance intAlgebraSolveStep {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

local notation "ι" => algebraMap (K k n)[X] (RatFunc (K k n))

namespace Solve

/-! ### The cleared equation -/

/-- The equation for `Y / P`, cleared of denominators. -/
theorem cleared_iff (t : Tower (n + 1)) {N B T P H Y : (K k n)[X]} (hB : B ≠ 0) (hT : T ≠ 0)
    (hP : P ≠ 0) :
    L t (P * (B * T)) (T * (N * P - B * Tower.polyDer k t P)) Y = H * (P * P * B) ↔
      t.der k (ι Y / ι P) + (ι N / ι B) * (ι Y / ι P) = ι H / ι T := by
  have hB' := RatFunc.algebraMap_ne_zero hB
  have hT' := RatFunc.algebraMap_ne_zero hT
  have hP' := RatFunc.algebraMap_ne_zero hP
  rw [Derivation.leibniz_div, Tower.der_algebraMap, Tower.der_algebraMap, L]
  simp only [smul_eq_mul]
  constructor
  · intro he
    have he' := congrArg ι he
    simp only [map_mul, map_add, map_sub] at he'
    field_simp [hB', hT', hP']
    linear_combination he'
  · intro he
    apply RatFunc.algebraMap_injective (K k n)
    simp only [map_mul, map_add, map_sub]
    field_simp [hB', hT', hP'] at he
    linear_combination he

/-- The common denominator of the solutions is not zero. -/
theorem PiecesSpec.P_ne_zero {t : Tower (n + 1)} {f : Term (n + 1)} {gs : List (Term (n + 1))}
    {e : ℕ} {pc : Pieces n} (ps : PiecesSpec k t f gs e pc) : Poly.model k pc.P ≠ 0 := by
  rw [ps.Pval]
  exact mul_ne_zero (pow_ne_zero _ X_ne_zero)
    (mul_ne_zero ps.nT (pow_ne_zero _ ps.nB.model_ne_zero))

/-- A combination of fractions with one denominator is the combination of the numerators
over that denominator. -/
theorem linComb_fractions (P : Poly n) : ∀ (Ys : List (Poly n)) (d : List k),
    linComb d (Ys.map fun Y => Term.div (Poly.toTerm Y) (Poly.toTerm P)) =
      ι (pcomb d Ys) / ι (Poly.model k P)
  | [], d => by simp [pcomb_nil_right, linComb_nil_right]
  | Y :: Ys, [] => by simp [pcomb_nil_left, linComb_nil_left]
  | Y :: Ys, c :: d => by
    rw [List.map_cons, linComb_cons, linComb_fractions P Ys d, pcomb_cons, map_add, map_mul,
      RatFunc.algebraMap_C, add_div, mul_div_assoc, constHom_succ]
    change _ * (Term.value k (Poly.toTerm Y) / Term.value k (Poly.toTerm P)) + _ = _
    rw [Poly.value_toTerm, Poly.value_toTerm]

omit [CharZero k] in
/-- Negating a row negates its value on a vector. -/
theorem dotK_neg : ∀ (row : List ℚ) (v : List k),
    dotK (row.map fun q => -q) v = -dotK row v
  | [], v => by simp [dotK]
  | r :: row, [] => by simp [dotK]
  | r :: row, c :: v => by
    change ((-r : ℚ) : k) * c + dotK (row.map fun q => -q) v = -((r : k) * c + dotK row v)
    rw [dotK_neg row v]
    push_cast
    ring

/-! ### A tower step -/

/-- Before compression, the solutions at a tower step are the combinations over the common
denominator of the polynomials returned by `solvePoly`, for the parameters that solve the
returned system together with the rows identifying the first new parameters with the old
ones. -/
theorem fractions_spec {t : Tower (n + 1)}
    {lower : Term n → List (Term n) → List (Term n) × List (List ℚ)}
    (hl : SolveSpec k t.parent lower) {f : Term (n + 1)} {gs : List (Term (n + 1))} {e : ℕ}
    {pc : Pieces n} (ps : PiecesSpec k t f gs e pc)
    (hden : ∀ (y : K k (n + 1)) (c : List k), c.length = gs.length →
      t.der k y + Term.value k f * y = linComb c gs → y.denom ∣ Poly.model k pc.P)
    {j : ℕ}
    (hbound : ∀ (p : List k) (Y : (K k n)[X]),
      L t (Poly.model k pc.R) (Poly.model k pc.S) Y = pcomb p pc.Gs →
        ∀ i, j ≤ i → Y.coeff i = 0)
    {out : List (Poly n) × List (List ℚ)}
    (hout : out = solvePoly t lower pc.R pc.S pc.lam j pc.Gs)
    (y : K k (n + 1)) (c : List k) (hc : c.length = gs.length) :
    t.der k y + Term.value k f * y = linComb c gs ↔
      ∃ d : List k, d.length = out.1.length ∧
        y = linComb d (out.1.map fun Y => Term.div (Poly.toTerm Y) (Poly.toTerm pc.P)) ∧
        ∀ row ∈ (List.range gs.length).map
              (fun i => unit gs.length i ++ (unit gs.length i).map fun q => -q) ++
            out.2.map (fun r => List.replicate gs.length 0 ++ r),
          dotK row (c ++ d) = 0 := by
  have sp := solvePoly_spec ps.good hl j ps.dG
  rw [← hout] at sp
  obtain ⟨-, lenY, iff⟩ := sp
  have Bn : Poly.model k pc.B ≠ 0 := ps.nB.model_ne_zero
  have Pn : Poly.model k pc.P ≠ 0 := ps.P_ne_zero
  have hcG : c.length = pc.Gs.length := by rw [ps.lenG, hc]
  have opEq (Y : (K k n)[X]) :
      L t (Poly.model k pc.R) (Poly.model k pc.S) Y = pcomb c pc.Gs ↔
        t.der k (ι Y / ι (Poly.model k pc.P)) +
          Term.value k f * (ι Y / ι (Poly.model k pc.P)) = linComb c gs := by
    rw [ps.Rval, ps.Sval, ps.Gval, ps.fval, ps.comb]
    exact cleared_iff t Bn ps.nT Pn
  constructor
  · intro eqn
    obtain ⟨q, hq⟩ := hden y c hc eqn
    have qn : q ≠ 0 := fun hz => Pn (by rw [hq, hz, mul_zero])
    obtain ⟨Y, hY⟩ : ∃ Y : (K k n)[X], Y = y.num * q := ⟨_, rfl⟩
    have yv : y = ι Y / ι (Poly.model k pc.P) := by
      rw [hY, hq, map_mul, map_mul, mul_div_mul_right _ _ (RatFunc.algebraMap_ne_zero qn),
        RatFunc.num_div_denom]
    have poly := (opEq Y).mpr (by rw [← yv]; exact eqn)
    obtain ⟨w, wl, wy, wr⟩ := (iff c Y hcG).mp ⟨hbound c Y poly, poly⟩
    refine ⟨c ++ w, wl, ?_, ?_⟩
    · rw [linComb_fractions, ← wy]
      exact yv
    · intro row hrow
      rcases List.mem_append.mp hrow with h | h
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
        have il : i < gs.length := List.mem_range.mp hi
        rw [dotK_append (by rw [length_unit, hc]), dotK_unit _ _ _ il, dotK_neg,
          dotK_unit _ _ _ il, List.getD_append _ _ _ _ (by omega)]
        ring
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
        rw [dotK_append (by rw [List.length_replicate, hc]),
          dotK_zero_row _ _ fun e he => List.eq_of_mem_replicate he, zero_add]
        exact wr r hr
  · rintro ⟨d, dl, rfl, rows⟩
    have mle : gs.length ≤ d.length := by
      rw [dl, ← ps.lenG]
      exact lenY
    have agree : ∀ i, i < gs.length → c.getD i 0 = d.getD i 0 := by
      intro i hi
      have := rows _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
      rw [dotK_append (by rw [length_unit, hc]), dotK_unit _ _ _ hi, dotK_neg,
        dotK_unit _ _ _ hi] at this
      linear_combination this
    obtain ⟨w, rfl⟩ : ∃ w, d = c ++ w := by
      refine ⟨d.drop gs.length, ?_⟩
      apply List.ext_getElem
      · simp [hc]
        omega
      · intro i h1 h2
        by_cases hi : i < gs.length
        · have := agree i hi
          rw [List.getElem_append_left (by omega)]
          simpa [List.getD, h1, show i < c.length by omega] using this.symm
        · rw [List.getElem_append_right (by omega)]
          simp [hc]
          congr 1
          omega
    have sub := (iff c (pcomb (c ++ w) out.1) hcG).mpr ⟨w, dl, rfl, fun r hr => by
      have := rows _ (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
      rwa [dotK_append (by rw [List.length_replicate, hc]),
        dotK_zero_row _ _ fun e he => List.eq_of_mem_replicate he, zero_add] at this⟩
    rw [linComb_fractions]
    exact (opEq _).mp sub.2

/-- `stepSolve` describes exactly the solutions at a tower step: given that `P` is a
denominator for every solution and that the degree bound holds for the cleared equation, the
solutions `(y, c)` of `y′ + f y = Σ cᵢ gᵢ` are the `y = Σ dⱼ hⱼ` for which `(c, d)` solves
the returned system. -/
theorem stepSolve_spec {t : Tower (n + 1)}
    {lower : Term n → List (Term n) → List (Term n) × List (List ℚ)}
    (hl : SolveSpec k t.parent lower) {f : Term (n + 1)} {gs : List (Term (n + 1))} {e : ℕ}
    (ps : PiecesSpec k t f gs e (pieces t f gs))
    (hden : ∀ (y : K k (n + 1)) (c : List k), c.length = gs.length →
      t.der k y + Term.value k f * y = linComb c gs →
        y.denom ∣ Poly.model k (pieces t f gs).P)
    (hbound : ∀ (p : List k) (Y : (K k n)[X]),
      L t (Poly.model k (pieces t f gs).R) (Poly.model k (pieces t f gs).S) Y =
        pcomb p (pieces t f gs).Gs →
      ∀ i, degBound t lower (pieces t f gs).R (pieces t f gs).S (pieces t f gs).lam
        (pieces t f gs).Gs ≤ i → Y.coeff i = 0) :
    (∀ h ∈ (stepSolve t lower f gs).1, Term.InDomain k h) ∧
    ∀ (y : K k (n + 1)) (c : List k), c.length = gs.length →
      (t.der k y + Term.value k f * y = linComb c gs ↔
        ∃ d : List k, d.length = (stepSolve t lower f gs).1.length ∧
          y = linComb d (stepSolve t lower f gs).1 ∧
          ∀ row ∈ (stepSolve t lower f gs).2, dotK row (c ++ d) = 0) := by
  obtain ⟨pc, hpc⟩ : ∃ pc, pc = pieces t f gs := ⟨_, rfl⟩
  rw [← hpc] at ps hden hbound
  obtain ⟨out, hout⟩ : ∃ out, out = solvePoly t lower pc.R pc.S pc.lam
    (degBound t lower pc.R pc.S pc.lam pc.Gs) pc.Gs := ⟨_, rfl⟩
  have dY : ∀ Y ∈ out.1, Poly.Defined k Y := by
    rw [hout]
    exact (solvePoly_spec ps.good hl _ ps.dG).1
  have Pn' : ι (Poly.model k pc.P) ≠ 0 := RatFunc.algebraMap_ne_zero ps.P_ne_zero
  have cs := compress_spec (k := k) (m := gs.length)
    (hs := out.1.map fun Y => Term.div (Poly.toTerm Y) (Poly.toTerm pc.P))
    (rows := (List.range gs.length).map
        (fun i => unit gs.length i ++ (unit gs.length i).map fun q => -q) ++
      out.2.map fun r => List.replicate gs.length 0 ++ r)
    (mix := fun v => Term.norm (.div (Poly.toTerm (lcomb v out.1)) (Poly.toTerm pc.P)))
    fun v _ => by
      have dom : Term.InDomain k
          (Term.div (Poly.toTerm (lcomb v out.1)) (Poly.toTerm pc.P)) := by
        refine ⟨Poly.inDomain_toTerm (defined_lcomb v dY), Poly.inDomain_toTerm ps.dP, ?_⟩
        change Term.value k (Poly.toTerm pc.P) ≠ 0
        rw [Poly.value_toTerm]
        exact Pn'
      obtain ⟨nd, nv⟩ := Term.norm_sound (k := k) (n + 1) _ dom
      refine ⟨nd, ?_⟩
      rw [nv, linComb_fractions, ← model_lcomb]
      change Term.value k (Poly.toTerm _) / Term.value k (Poly.toTerm _) = _
      rw [Poly.value_toTerm, Poly.value_toTerm]
  rw [List.length_map] at cs
  have run : stepSolve t lower f gs = compress gs.length out.1.length
      ((List.range gs.length).map
          (fun i => unit gs.length i ++ (unit gs.length i).map fun q => -q) ++
        out.2.map fun r => List.replicate gs.length 0 ++ r)
      (fun v => Term.norm (.div (Poly.toTerm (lcomb v out.1)) (Poly.toTerm pc.P))) := by
    subst hout hpc
    rfl
  rw [run]
  exact ⟨cs.1, fun y c hc =>
    (fractions_spec hl ps hden hbound hout y c hc).trans (cs.2 y c hc)⟩

/-! ### The constants -/

/-- The row of the negated right-hand sides, applied to the parameters. -/
theorem dotK_evalRat : ∀ (gs : List (Term 0)) (c : List k),
    dotK (gs.map fun g => -g.evalRat) c = -linComb c gs
  | [], c => by simp [dotK, linComb_nil_right]
  | g :: gs, [] => by simp [dotK, linComb_nil_left]
  | g :: gs, a :: c => by
    change ((-g.evalRat : ℚ) : k) * a + dotK (gs.map fun g => -g.evalRat) c = _
    rw [dotK_evalRat gs c, linComb_cons, Rat.cast_neg, Term.value_evalRat]
    change _ = -(a * Term.value k g + linComb c gs)
    ring

/-- Over the constants the equation is `f y = Σ cᵢ gᵢ`, and `constSolve` describes exactly
its solutions. -/
theorem constSolve_spec : SolveSpec k Tower.const constSolve := by
  intro f gs _ _
  refine ⟨fun h hh => by rw [List.mem_singleton.mp hh]; trivial, fun y c hc => ?_⟩
  have row (d : k) : dotK (gs.map (fun g => -g.evalRat) ++ [f.evalRat]) (c ++ [d]) =
      Term.value k f * d - linComb c gs := by
    rw [dotK_append (by rw [List.length_map, hc]), dotK_evalRat]
    change _ + (((f.evalRat : ℚ) : k) * d + 0) = _
    rw [Term.value_evalRat]
    ring
  have one (d : k) : linComb [d] [(.const 1 : Term 0)] = d := by
    simp [linComb, Term.value_const, constHom]
  change (0 : K k 0) + Term.value k f * y = linComb c gs ↔
    ∃ d : List k, d.length = 1 ∧ y = linComb d [(.const 1 : Term 0)] ∧
      ∀ r ∈ [gs.map (fun g => -g.evalRat) ++ [f.evalRat]], dotK r (c ++ d) = 0
  rw [zero_add]
  constructor
  · intro eqn
    refine ⟨[y], rfl, (one y).symm, fun r hr => ?_⟩
    rw [List.mem_singleton.mp hr, row, eqn, sub_self]
  · rintro ⟨d, dl, rfl, rows⟩
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp dl
    have := rows _ (List.mem_singleton.mpr rfl)
    rw [row] at this
    rw [one]
    exact sub_eq_zero.mp this

/-! ### Combinations of terms -/

/-- A combination of terms with rational coefficients denotes the combination of their
values. -/
theorem value_lincomb : ∀ (hs : List (Term n)) (cs : List ℚ),
    Term.value k (lincomb cs hs) = linComb (cs.map fun (q : ℚ) => (q : k)) hs
  | [], cs => by cases cs <;> simp [lincomb, linComb_nil_right, Term.value_const]
  | h :: hs, [] => by simp [lincomb, linComb_nil_left, Term.value_const]
  | h :: hs, c :: cs => by
    rw [lincomb, List.map_cons, linComb_cons, ← value_lincomb hs cs, constHom_ratCast]
    rfl

/-- A combination of defined terms is defined. -/
theorem inDomain_lincomb : ∀ {hs : List (Term n)} (cs : List ℚ),
    (∀ h ∈ hs, Term.InDomain k h) → Term.InDomain k (lincomb cs hs)
  | [], cs, _ => by cases cs <;> trivial
  | h :: hs, [], _ => trivial
  | h :: hs, c :: cs, hd =>
    ⟨⟨trivial, hd h List.mem_cons_self⟩,
      inDomain_lincomb cs fun e he => hd e (List.mem_cons_of_mem _ he)⟩

end Solve

/-! ### One equation, and integration up to a multiple of a second element -/

variable {t : Tower n}

/-- A term returned by `rde` is defined and solves `y′ + a y = h`. -/
theorem rde_sound (hs : SolveSpec k t (solve t)) {a h y : Term n} (ha : Term.InDomain k a)
    (hh : Term.InDomain k h) (ok : rde t a h = some y) :
    Term.InDomain k y ∧
      t.der k (Term.value k y) + Term.value k a * Term.value k y = Term.value k h := by
  have hg : ∀ g ∈ [h], Term.InDomain k g := fun g hg => by rwa [List.mem_singleton.mp hg]
  obtain ⟨dom, spec⟩ := hs a [h] ha hg
  rw [rde] at ok
  split at ok
  · rename_i x0 d hx
    obtain rfl := Option.some.inj ok
    obtain ⟨xl, x0e, xrows⟩ := normalized_sound hx
    obtain rfl : x0 = 1 := x0e
    have dl : d.length = (solve t a [h]).1.length := by
      rw [List.length_cons] at xl
      omega
    refine ⟨Solve.inDomain_lincomb _ dom, ?_⟩
    rw [Solve.value_lincomb]
    have := (spec (linComb (d.map fun (q : ℚ) => (q : k)) (solve t a [h]).1) [1] rfl).mpr
      ⟨d.map fun (q : ℚ) => (q : k), by rw [List.length_map, dl], rfl, fun row hrow => by
        have cast := dotK_cast (k := k) row (1 :: d)
        rw [xrows row hrow] at cast
        simpa using cast⟩
    simpa [linComb] using this
  · cases ok

/-- If `y′ + a y = h` has a solution in the field of the tower, `rde` returns one. -/
theorem rde_complete (hs : SolveSpec k t (solve t)) {a h : Term n} (ha : Term.InDomain k a)
    (hh : Term.InDomain k h)
    (ex : ∃ y : K k n, t.der k y + Term.value k a * y = Term.value k h) :
    (rde t a h).isSome := by
  have hg : ∀ g ∈ [h], Term.InDomain k g := fun g hg => by rwa [List.mem_singleton.mp hg]
  obtain ⟨y, hy⟩ := ex
  obtain ⟨d, dl, -, drows⟩ := ((hs a [h] ha hg).2 y [1] rfl).mp (by simpa [linComb] using hy)
  have found := normalized_complete (k := k) (rows := (solve t a [h]).2)
    (M := 1 + (solve t a [h]).1.length) ⟨1 :: d, by simp [dl, add_comm], rfl, drows⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp found
  obtain ⟨xl, -, -⟩ := normalized_sound hx
  obtain ⟨x0, d', rfl⟩ : ∃ x0 d', x = x0 :: d' := by
    cases x with
    | nil =>
      rw [List.length_nil] at xl
      omega
    | cons x0 d' => exact ⟨x0, d', rfl⟩
  rw [rde, hx]
  rfl

private theorem pair_domain {g b : Term n} (hg : Term.InDomain k g) (hb : Term.InDomain k b) :
    ∀ e ∈ [g, b], Term.InDomain k e := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact hg
  · rwa [List.mem_singleton.mp he]

private theorem pair_comb (c : k) (g b : Term n) :
    linComb [1, c] [g, b] = Term.value k g + constHom k n c * Term.value k b := by
  simp [linComb]

/-- A pair returned by `limited` consists of a rational `c` and a defined term `v` with
`v′ = g - c b`. -/
theorem limited_sound (hs : SolveSpec k t (solve t)) {g b v : Term n} {c : ℚ}
    (hg : Term.InDomain k g) (hb : Term.InDomain k b) (ok : limited t g b = some (c, v)) :
    Term.InDomain k v ∧
      t.der k (Term.value k v) = Term.value k g - (c : K k n) * Term.value k b := by
  have hz : Term.InDomain k (.const 0 : Term n) := trivial
  obtain ⟨dom, spec⟩ := hs (.const 0) [g, b] hz (pair_domain hg hb)
  rw [limited] at ok
  split at ok
  · rename_i x0 c' d hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ok)
    obtain ⟨xl, x0e, xrows⟩ := normalized_sound hx
    obtain rfl : x0 = 1 := x0e
    have dl : d.length = (solve t (.const 0) [g, b]).1.length := by
      rw [List.length_cons, List.length_cons] at xl
      omega
    refine ⟨Solve.inDomain_lincomb _ dom, ?_⟩
    have := (spec (linComb (d.map fun (q : ℚ) => (q : k)) (solve t (.const 0) [g, b]).1)
      [1, (c' : k)] rfl).mpr
      ⟨d.map fun (q : ℚ) => (q : k), by rw [List.length_map, dl], rfl, fun row hrow => by
        have cast := dotK_cast (k := k) row (1 :: c' :: d)
        rw [xrows row hrow] at cast
        simpa using cast⟩
    rw [pair_comb, Poly.value_zero, zero_mul, add_zero, constHom_ratCast] at this
    rw [Solve.value_lincomb, this]
    push_cast
    ring
  · cases ok

/-- If `v′ = g - c b` for a constant `c` and an element `v` of the field of the tower,
`limited` returns a pair. -/
theorem limited_complete (hs : SolveSpec k t (solve t)) {g b : Term n}
    (hg : Term.InDomain k g) (hb : Term.InDomain k b)
    (ex : ∃ (c : k) (v : K k n),
      t.der k v = Term.value k g - constHom k n c * Term.value k b) :
    (limited t g b).isSome := by
  have hz : Term.InDomain k (.const 0 : Term n) := trivial
  obtain ⟨c, v, hv⟩ := ex
  have first : t.der k v + Term.value k (.const 0 : Term n) * v = linComb [1, -c] [g, b] := by
    rw [pair_comb, Poly.value_zero, hv, map_neg]
    ring
  obtain ⟨d, dl, -, drows⟩ :=
    ((hs (.const 0) [g, b] hz (pair_domain hg hb)).2 v [1, -c] rfl).mp first
  have found := normalized_complete (k := k) (rows := (solve t (.const 0) [g, b]).2)
    (M := 2 + (solve t (.const 0) [g, b]).1.length)
    ⟨1 :: -c :: d, by rw [List.length_cons, List.length_cons, dl]; omega, rfl, drows⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp found
  obtain ⟨xl, -, -⟩ := normalized_sound hx
  obtain ⟨x0, c', d', rfl⟩ : ∃ x0 c' d', x = x0 :: c' :: d' := by
    match x, xl with
    | [], xl =>
      rw [List.length_nil] at xl
      omega
    | [_], xl =>
      rw [List.length_singleton] at xl
      omega
    | x0 :: c' :: d', _ => exact ⟨x0, c', d', rfl⟩
  rw [limited, hx]
  rfl

end SympyProofs.Calculus.Risch
