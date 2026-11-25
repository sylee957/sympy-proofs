module

public import SympyProofs.Calculus.Risch.Program.Solve
public import SympyProofs.Calculus.Risch.Spec.Solve
public import SympyProofs.Calculus.Risch.Proof.Deriv
public import SympyProofs.Calculus.Risch.Proof.Constraints
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The polynomial form of part (b) at a tower step: all polynomials `Y` of bounded degree
in the newest generator and all constants `p` with `R Y′ + S Y = Σ pᵢ Gᵢ`. Following Risch
(1969, pp. 185–186), the coefficient of highest degree of `Y` satisfies an instance of part
(b) in the preceding field. Substituting its general solution lowers the degree bound by
one and adds the new constants to the parameters.

The systems of equations and the generators of their solution spaces are rational, and the
parameters range over the constant field `k`.

The last section specifies `compress`: a basis and a linear system are replaced by one basis
element for each generator of the solution space of the system. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial Linear

noncomputable local instance intAlgebraSolvePoly {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

namespace Solve

/-! ### Combinations of polynomials with constant coefficients -/

/-- A combination of polynomials in the newest generator with constant coefficients. -/
noncomputable def pcomb (p : List k) (Gs : List (Poly n)) : (K k n)[X] :=
  (List.zipWith (fun (c : k) (G : Poly n) => C (constHom k n c) * Poly.model k G) p Gs).sum

theorem pcomb_nil_left (Gs : List (Poly n)) : pcomb ([] : List k) Gs = 0 := by simp [pcomb]

theorem pcomb_nil_right (p : List k) : pcomb p ([] : List (Poly n)) = 0 := by simp [pcomb]

theorem pcomb_cons (c : k) (p : List k) (G : Poly n) (Gs : List (Poly n)) :
    pcomb (c :: p) (G :: Gs) = C (constHom k n c) * Poly.model k G + pcomb p Gs := by
  simp [pcomb]

theorem pcomb_append {p q : List k} {Gs Hs : List (Poly n)} (h : p.length = Gs.length) :
    pcomb (p ++ q) (Gs ++ Hs) = pcomb p Gs + pcomb q Hs := by
  simp [pcomb, List.zipWith_append h]

/-- The coefficient of degree `j` of a combination is the combination of the coefficients
of degree `j`. -/
theorem coeff_pcomb (j : ℕ) : ∀ (Gs : List (Poly n)) (p : List k),
    (pcomb p Gs).coeff j = linComb p (coeffs Gs j)
  | [], p => by simp [pcomb_nil_right, coeffs, linComb_nil_right]
  | G :: Gs, [] => by simp [pcomb_nil_left, linComb_nil_left]
  | G :: Gs, c :: p => by
    change _ = linComb (c :: p) (Poly.coeff G j :: coeffs Gs j)
    rw [pcomb_cons, coeff_add, coeff_C_mul, coeff_pcomb j Gs p, linComb_cons, Poly.value_coeff]

theorem defined_coeffs {Gs : List (Poly n)} (hG : ∀ G ∈ Gs, Poly.Defined k G) (j : ℕ) :
    ∀ c ∈ coeffs Gs j, Term.InDomain k c := by
  intro c hc
  obtain ⟨G, hGm, rfl⟩ := List.mem_map.mp hc
  exact Poly.defined_coeff (hG G hGm) j

/-- A combination has no coefficient of degree at least the greatest length. -/
theorem coeff_pcomb_of_maxLen_le {j : ℕ} : ∀ (Gs : List (Poly n)) (p : List k),
    maxLen Gs ≤ j → (pcomb p Gs).coeff j = 0
  | [], p, _ => by simp [pcomb_nil_right]
  | G :: Gs, [], _ => by simp [pcomb_nil_left]
  | G :: Gs, c :: p, h => by
    simp only [maxLen, List.foldr_cons] at h
    rw [pcomb_cons, coeff_add, coeff_C_mul, Poly.coeff_model_of_length_le (by omega),
      coeff_pcomb_of_maxLen_le Gs p (by simpa [maxLen] using (le_max_right _ _).trans h)]
    simp

theorem pcomb_map_nil : ∀ (Gs : List (Poly n)) (p : List k),
    pcomb p (Gs.map fun _ => ([] : Poly n)) = 0
  | [], p => by simp [pcomb_nil_right]
  | G :: Gs, [] => by simp [pcomb_nil_left]
  | G :: Gs, c :: p => by
    rw [List.map_cons, pcomb_cons, pcomb_map_nil Gs p, Poly.model_nil]
    simp

theorem pcomb_map_mono (j : ℕ) : ∀ (hs : List (Term n)) (d : List k),
    pcomb d (hs.map (Poly.mono j)) = C (linComb d hs) * X ^ j
  | [], d => by simp [pcomb_nil_right, linComb_nil_right]
  | h :: hs, [] => by simp [pcomb_nil_left, linComb_nil_left]
  | h :: hs, c :: d => by
    rw [List.map_cons, pcomb_cons, pcomb_map_mono j hs d, Poly.model_mono, linComb_cons,
      C_add, C_mul]
    ring

theorem pcomb_map_congr {α : Type*} (F G : α → Poly n) : ∀ (l : List α) (p : List k),
    (∀ a ∈ l, Poly.model k (F a) = Poly.model k (G a)) → pcomb p (l.map F) = pcomb p (l.map G)
  | [], p, _ => rfl
  | a :: l, [], _ => by simp [pcomb_nil_left]
  | a :: l, c :: p, h => by
    rw [List.map_cons, List.map_cons, pcomb_cons, pcomb_cons, h a List.mem_cons_self,
      pcomb_map_congr F G l p fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem linComb_map_congr {α : Type*} (F G : α → Term n) : ∀ (l : List α) (p : List k),
    (∀ a ∈ l, Term.value k (F a) = Term.value k (G a)) →
      linComb p (l.map F) = linComb p (l.map G)
  | [], p, _ => rfl
  | a :: l, [], _ => by simp [linComb_nil_left]
  | a :: l, c :: p, h => by
    rw [List.map_cons, List.map_cons, linComb_cons, linComb_cons, h a List.mem_cons_self,
      linComb_map_congr F G l p fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem linComb_map_div (s : Term n) : ∀ (as : List (Term n)) (p : List k),
    linComb p (as.map fun g => Term.div g s) = linComb p as / Term.value k s
  | [], p => by simp [linComb_nil_right]
  | a :: as, [] => by simp [linComb_nil_left]
  | a :: as, c :: p => by
    rw [List.map_cons, linComb_cons, linComb_cons, linComb_map_div s as p, add_div,
      mul_div_assoc]
    rfl

theorem pcomb_eq_sum : ∀ (Gs : List (Poly n)) (p : List k), p.length = Gs.length →
    pcomb p Gs = ∑ i ∈ Finset.range Gs.length,
      C (constHom k n (p.getD i 0)) * Poly.model k (Gs.getD i [])
  | [], p, _ => by simp [pcomb_nil_right]
  | G :: Gs, [], h => by simp at h
  | G :: Gs, c :: p, h => by
    rw [pcomb_cons, pcomb_eq_sum Gs p (by simpa using h), List.length_cons,
      Finset.sum_range_succ']
    simp [add_comm]

theorem linComb_eq_sum : ∀ (hs : List (Term n)) (d : List k), d.length = hs.length →
    linComb d hs = ∑ i ∈ Finset.range hs.length,
      constHom k n (d.getD i 0) * Term.value k (hs.getD i (.const 0))
  | [], d, _ => by simp [linComb_nil_right]
  | h :: hs, [], hd => by simp at hd
  | h :: hs, c :: d, hd => by
    rw [linComb_cons, linComb_eq_sum hs d (by simpa using hd), List.length_cons,
      Finset.sum_range_succ']
    simp [add_comm]

/-! ### Rows and combinations of rational vectors -/

omit [CharZero k] in
theorem dotK_take : ∀ (v : List k) (row : List ℚ) (w : List k),
    dotK (row.take v.length) (v ++ w) = dotK row v
  | [], row, w => by simp [dotK]
  | c :: v, [], w => by simp [dotK]
  | c :: v, r :: row, w => by
    have ih := dotK_take v row w
    simp only [dotK] at ih
    simp [dotK, ih]

omit [CharZero k] in
theorem dotK_append_of_length {row : List ℚ} {v : List k} (h : row.length = v.length)
    (w : List k) : dotK row (v ++ w) = dotK row v := by
  have := dotK_take v row w
  rwa [← h, List.take_length] at this

omit [CharZero k] in
theorem lsum_cons (e : k) (es : List k) (g : List ℚ) (G : List (List ℚ)) (i : ℕ) :
    lsum (e :: es) (g :: G) i = e * ((g.getD i 0 : ℚ) : k) + lsum es G i := by
  simp [Linear.lsum]

omit [CharZero k] in
theorem lsum_eq_zero_of_length {M i : ℕ} (hi : M ≤ i) (es : List k) (G : List (List ℚ))
    (h : ∀ g ∈ G, g.length = M) : lsum es G i = 0 :=
  lsum_eq_zero es G fun g hg => List.getD_eq_default _ _ (by rw [h g hg]; exact hi)

omit [CharZero k] in
theorem dotK_map_neg (i : ℕ) : ∀ (G : List (List ℚ)) (es : List k),
    dotK (G.map fun v => -(v.getD i 0)) es = -lsum es G i
  | [], es => by simp [dotK, Linear.lsum]
  | g :: G, [] => by simp [dotK, Linear.lsum]
  | g :: G, e :: es => by
    have ih := dotK_map_neg i G es
    simp only [dotK] at ih
    rw [lsum_cons]
    simp only [dotK, List.map_cons, List.zipWith_cons_cons, List.sum_cons, ih]
    push_cast
    ring

omit [CharZero k] in
theorem getD_map_range (N : ℕ) (f : ℕ → k) (i : ℕ) :
    ((List.range N).map f).getD i 0 = if i < N then f i else 0 := by
  by_cases hi : i < N
  · simp [List.getD, hi]
  · simp [List.getD, hi]

/-! ### The operator -/

/-- The derivation of the field of a tower vanishes on the constants. -/
theorem der_constHom : ∀ {n : ℕ} (t : Tower n) (c : k), t.der k (constHom k n c) = 0
  | _, .const, c => by simp [Tower.der]
  | _, .prim t b, c => by
    rw [constHom_succ, Tower.der_prim_C, der_constHom t c, map_zero]
  | _, .exp t u, c => by
    rw [constHom_succ, Tower.der_exp_C, der_constHom t c, map_zero]

/-- The operator `Y ↦ R Y′ + S Y`. -/
noncomputable def L (t : Tower (n + 1)) (R S Y : (K k n)[X]) : (K k n)[X] :=
  R * Tower.polyDer k t Y + S * Y

/-- The operator on coefficient lists denotes the operator on polynomials. -/
theorem model_applyL (t : Tower (n + 1)) (R S Y : Poly n) :
    Poly.model k (applyL t R S Y) =
      L t (Poly.model k R) (Poly.model k S) (Poly.model k Y) := by
  rw [applyL, Poly.model_add, Poly.model_mul, Poly.model_mul, Poly.model_der, L]

theorem defined_applyL {t : Tower (n + 1)} (ht : t.Admissible k) {R S Y : Poly n}
    (hR : Poly.Defined k R) (hS : Poly.Defined k S) (hY : Poly.Defined k Y) :
    Poly.Defined k (applyL t R S Y) :=
  Poly.defined_add (Poly.defined_mul hR (Poly.defined_der ht hY)) (Poly.defined_mul hS hY)

/-- The derivative of a constant polynomial is the derivative of the constant. -/
theorem polyDer_C (t : Tower (n + 1)) (a : K k n) :
    Tower.polyDer k t (C a) = C (t.parent.der k a) := by
  ext i
  rw [Tower.coeff_polyDer]
  cases i <;> simp [coeff_C]

theorem L_add (t : Tower (n + 1)) (R S Y Z : (K k n)[X]) :
    L t R S (Y + Z) = L t R S Y + L t R S Z := by
  simp only [L, map_add]
  ring

theorem L_smul (t : Tower (n + 1)) (R S Y : (K k n)[X]) (c : k) :
    L t R S (C (constHom k n c) * Y) = C (constHom k n c) * L t R S Y := by
  simp only [L, Derivation.leibniz, smul_eq_mul, polyDer_C, der_constHom, map_zero, mul_zero,
    add_zero]
  ring

theorem L_zero (t : Tower (n + 1)) (R S : (K k n)[X]) : L t R S 0 = 0 := by simp [L]

/-- Differentiation does not raise the degree in the newest generator. -/
theorem natDegree_polyDer_le (t : Tower (n + 1)) (P : (K k n)[X]) :
    (Tower.polyDer k t P).natDegree ≤ P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [Tower.coeff_polyDer, coeff_eq_zero_of_natDegree_lt hi,
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_lt hi)]
  simp

theorem coeff_polyDer_top (t : Tower (n + 1)) {P : (K k n)[X]} {j : ℕ}
    (hP : P.natDegree ≤ j) :
    (Tower.polyDer k t P).coeff j =
      t.parent.der k (P.coeff j) + (j : K k n) * Term.value k t.twist * P.coeff j := by
  rw [Tower.coeff_polyDer, coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hP), mul_zero,
    add_zero]

/-- The coefficient of highest possible degree of `R Y′ + S Y`. -/
theorem coeff_L_top (t : Tower (n + 1)) {R S Y : (K k n)[X]} {lam j : ℕ}
    (hR : R.natDegree ≤ lam) (hS : S.natDegree ≤ lam) (hY : Y.natDegree ≤ j) :
    (L t R S Y).coeff (lam + j) = R.coeff lam * t.parent.der k (Y.coeff j) +
      (S.coeff lam + (j : K k n) * Term.value k t.twist * R.coeff lam) * Y.coeff j := by
  rw [L, coeff_add, coeff_mul_add_eq_of_natDegree_le hR ((natDegree_polyDer_le t Y).trans hY),
    coeff_mul_add_eq_of_natDegree_le hS hY, coeff_polyDer_top t hY]
  ring

/-- `R Y′ + S Y` has no coefficient above the sum of the degree bounds. -/
theorem coeff_L_high (t : Tower (n + 1)) {R S Y : (K k n)[X]} {lam j i : ℕ}
    (hR : R.natDegree ≤ lam) (hS : S.natDegree ≤ lam) (hY : Y.natDegree ≤ j)
    (hi : lam + j < i) : (L t R S Y).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have d1 : (R * Tower.polyDer k t Y).natDegree ≤ lam + j :=
    natDegree_mul_le.trans (Nat.add_le_add hR ((natDegree_polyDer_le t Y).trans hY))
  have d2 : (S * Y).natDegree ≤ lam + j := natDegree_mul_le.trans (Nat.add_le_add hS hY)
  exact ((natDegree_add_le _ _).trans (max_le d1 d2)).trans_lt hi

theorem pcomb_map_neg (t : Tower (n + 1)) (R S : Poly n) (j : ℕ) :
    ∀ (hs : List (Term n)) (d : List k),
      pcomb d (hs.map fun h => Poly.neg (applyL t R S (Poly.mono j h))) =
        -L t (Poly.model k R) (Poly.model k S) (C (linComb d hs) * X ^ j)
  | [], d => by simp [pcomb_nil_right, linComb_nil_right, L_zero]
  | h :: hs, [] => by simp [pcomb_nil_left, linComb_nil_left, L_zero]
  | h :: hs, c :: d => by
    rw [List.map_cons, pcomb_cons, pcomb_map_neg t R S j hs d, Poly.model_neg, model_applyL,
      Poly.model_mono, linComb_cons, C_add, C_mul, add_mul, L_add, mul_assoc, L_smul]
    ring

theorem pcomb_map_sub (t : Tower (n + 1)) (R S : Poly n) (j : ℕ) (η : Poly n → Term n) :
    ∀ (Gs : List (Poly n)) (p : List k),
      pcomb p (Gs.map fun G => Poly.sub G (applyL t R S (Poly.mono j (η G)))) =
        pcomb p Gs - L t (Poly.model k R) (Poly.model k S) (C (linComb p (Gs.map η)) * X ^ j)
  | [], p => by simp [pcomb_nil_right, linComb_nil_right, L_zero]
  | G :: Gs, [] => by simp [pcomb_nil_left, linComb_nil_left, L_zero]
  | G :: Gs, c :: p => by
    rw [List.map_cons, pcomb_cons, pcomb_map_sub t R S j η Gs p, Poly.model_sub, model_applyL,
      Poly.model_mono, List.map_cons, linComb_cons, pcomb_cons, C_add, C_mul, add_mul, L_add,
      mul_assoc, L_smul]
    ring

/-! ### The programs on lists of polynomials -/

/-- The parameters satisfy the equations of `vanish` exactly when the combination has no
coefficient of degree at least `lo`. -/
theorem vanish_spec {Gs : List (Poly n)} (hG : ∀ G ∈ Gs, Poly.Defined k G) (lo : ℕ)
    {p : List k} (w : List k) (hp : p.length = Gs.length) :
    (∀ row ∈ vanish Gs lo (maxLen Gs), dotK row (p ++ w) = 0) ↔
      ∀ j, lo ≤ j → (pcomb p Gs).coeff j = 0 := by
  constructor
  · intro rows j hj
    by_cases hlt : j < maxLen Gs
    · rw [coeff_pcomb]
      apply (rowsOf_spec (defined_coeffs hG j) p).mp
      intro r hr
      have := rows (r.take Gs.length) (List.mem_flatMap.mpr ⟨j - lo,
        List.mem_range.mpr (by omega),
        List.mem_map.mpr ⟨r, by rwa [Nat.add_sub_cancel' hj], rfl⟩⟩)
      rwa [← hp, dotK_take] at this
    · exact coeff_pcomb_of_maxLen_le Gs p (Nat.le_of_not_lt hlt)
  · intro all row hrow
    obtain ⟨i, -, hmem⟩ := List.mem_flatMap.mp hrow
    obtain ⟨r, hr2, rfl⟩ := List.mem_map.mp hmem
    rw [← hp, dotK_take]
    apply (rowsOf_spec (defined_coeffs hG (lo + i)) p).mpr _ r hr2
    rw [← coeff_pcomb]
    exact all _ (Nat.le_add_right _ _)

theorem length_addFront : ∀ (ms Ys : List (Poly n)), (addFront ms Ys).length = Ys.length
  | [], Ys => rfl
  | _ :: _, [] => rfl
  | m :: ms, Y :: Ys => by simp [addFront, length_addFront ms Ys]

theorem pcomb_addFront : ∀ (ms Ys : List (Poly n)) (v : List k), ms.length ≤ Ys.length →
    pcomb v (addFront ms Ys) = pcomb v Ys + pcomb v ms
  | [], Ys, v, _ => by simp [addFront, pcomb_nil_right]
  | m :: ms, [], v, h => by simp at h
  | m :: ms, Y :: Ys, [], _ => by simp [pcomb_nil_left]
  | m :: ms, Y :: Ys, c :: v, h => by
    rw [addFront, pcomb_cons, pcomb_cons, pcomb_cons, Poly.model_add,
      pcomb_addFront ms Ys v (by simpa using h)]
    ring

theorem defined_addFront : ∀ {ms Ys : List (Poly n)}, (∀ m ∈ ms, Poly.Defined k m) →
    (∀ Y ∈ Ys, Poly.Defined k Y) → ∀ Z ∈ addFront ms Ys, Poly.Defined k Z
  | [], Ys, _, hY => hY
  | _ :: _, [], _, _ => fun _ h => by simp [addFront] at h
  | m :: ms, Y :: Ys, hm, hY => by
    intro Z hZ
    rcases List.mem_cons.mp hZ with rfl | hZ
    · exact Poly.defined_add (hY Y List.mem_cons_self) (hm m List.mem_cons_self)
    · exact defined_addFront (fun a ha => hm a (List.mem_cons_of_mem _ ha))
        (fun a ha => hY a (List.mem_cons_of_mem _ ha)) Z hZ

/-- A combination of coefficient lists with rational coefficients denotes the combination
of the polynomials. -/
theorem model_lcomb : ∀ (Ys : List (Poly n)) (v : List ℚ),
    Poly.model k (lcomb v Ys) = pcomb (v.map fun (q : ℚ) => (q : k)) Ys
  | [], v => by cases v <;> simp [lcomb, pcomb_nil_right, Poly.model_nil]
  | Y :: Ys, [] => by simp [lcomb, pcomb_nil_left, Poly.model_nil]
  | Y :: Ys, c :: v => by
    rw [lcomb, Poly.model_add, Poly.model_scale, model_lcomb Ys v, List.map_cons, pcomb_cons,
      Term.value_const, constHom_ratCast]

theorem defined_lcomb : ∀ {Ys : List (Poly n)} (v : List ℚ),
    (∀ Y ∈ Ys, Poly.Defined k Y) → Poly.Defined k (lcomb v Ys)
  | [], v, _ => by cases v <;> exact fun _ h => by simp [lcomb] at h
  | Y :: Ys, [], _ => fun _ h => by simp [lcomb] at h
  | Y :: Ys, c :: v, h =>
    Poly.defined_add (Poly.defined_scale trivial (h Y List.mem_cons_self))
      (defined_lcomb v fun Z hZ => h Z (List.mem_cons_of_mem _ hZ))

/-- A combination, with coefficients `es`, of polynomials that are rational combinations
`v ∈ G` of the `H i` is the combination of the `H i` with the coordinates of the combination
of `G`. -/
theorem pcomb_kernel {M : ℕ} (H : ℕ → (K k n)[X]) (F : List ℚ → Poly n) :
    ∀ (G : List (List ℚ)) (es : List k),
      (∀ v ∈ G, Poly.model k (F v) =
        ∑ i ∈ Finset.range M, C (constHom k n ((v.getD i 0 : ℚ) : k)) * H i) →
      pcomb es (G.map F) = ∑ i ∈ Finset.range M, C (constHom k n (lsum es G i)) * H i
  | [], es, _ => by simp [pcomb_nil_right, Linear.lsum]
  | g :: G, [], _ => by simp [pcomb_nil_left, Linear.lsum]
  | g :: G, e :: es, h => by
    rw [List.map_cons, pcomb_cons, h g List.mem_cons_self,
      pcomb_kernel H F G es fun v hv => h v (List.mem_cons_of_mem _ hv), Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lsum_cons, map_add, map_mul, C_add, C_mul]
    ring

/-! ### The specification -/

/-- Hypotheses on the operator: both coefficients have degree at most `lam`, and one of them
has degree exactly `lam`. -/
structure Good (k : Type) [Field k] [CharZero k] (t : Tower (n + 1)) (R S : Poly n) (lam : ℕ) :
    Prop where
  admissible : t.Admissible k
  hR : Poly.Defined k R
  hS : Poly.Defined k S
  degR : (Poly.model k R).natDegree ≤ lam
  degS : (Poly.model k S).natDegree ≤ lam
  lead : (Poly.model k R).coeff lam ≠ 0 ∨ (Poly.model k S).coeff lam ≠ 0

/-- A polynomial with fewer than `j` coefficients solving the equation with parameters `p`. -/
def Sol (t : Tower (n + 1)) (R S : Poly n) (j : ℕ) (Gs : List (Poly n)) (p : List k)
    (Y : (K k n)[X]) : Prop :=
  (∀ i, j ≤ i → Y.coeff i = 0) ∧ L t (Poly.model k R) (Poly.model k S) Y = pcomb p Gs

/-- The output describes exactly the solutions. -/
def Spec (k : Type) [Field k] [CharZero k] (t : Tower (n + 1)) (R S : Poly n) (j : ℕ)
    (Gs : List (Poly n)) (out : List (Poly n) × List (List ℚ)) : Prop :=
  (∀ Y ∈ out.1, Poly.Defined k Y) ∧ Gs.length ≤ out.1.length ∧
    ∀ (p : List k) (Y : (K k n)[X]), p.length = Gs.length →
      (Sol t R S j Gs p Y ↔ ∃ w : List k, (p ++ w).length = out.1.length ∧
        Y = pcomb (p ++ w) out.1 ∧ ∀ row ∈ out.2, dotK row (p ++ w) = 0)

/-- The output describes exactly the solutions whose parameters satisfy the constraints. -/
def SpecC (k : Type) [Field k] [CharZero k] (t : Tower (n + 1)) (R S : Poly n) (j : ℕ)
    (Gs : List (Poly n)) (Cs : List (List ℚ)) (out : List (Poly n) × List (List ℚ)) : Prop :=
  (∀ Y ∈ out.1, Poly.Defined k Y) ∧ Gs.length ≤ out.1.length ∧
    ∀ (p : List k) (Y : (K k n)[X]), p.length = Gs.length →
      ((Sol t R S j Gs p Y ∧ ∀ row ∈ Cs, dotK row p = 0) ↔ ∃ w : List k,
        (p ++ w).length = out.1.length ∧ Y = pcomb (p ++ w) out.1 ∧
          ∀ row ∈ out.2, dotK row (p ++ w) = 0)

/-- With no coefficient allowed, the only solution is zero, and the parameters are those for
which the right-hand side vanishes. -/
theorem spec_zero (t : Tower (n + 1)) (R S : Poly n) {Gs : List (Poly n)}
    (hG : ∀ G ∈ Gs, Poly.Defined k G) :
    Spec k t R S 0 Gs (Gs.map fun _ => [], vanish Gs 0 (maxLen Gs)) := by
  refine ⟨?_, by simp, fun p Y hp => ?_⟩
  · intro Y hY
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hY
    exact Poly.defined_nil
  constructor
  · rintro ⟨below, eq⟩
    have Y0 : Y = 0 := by
      ext i
      simpa using below i (Nat.zero_le i)
    refine ⟨[], by simpa using hp, by rw [pcomb_map_nil]; exact Y0, ?_⟩
    apply (vanish_spec hG 0 [] hp).mpr
    intro j _
    rw [← eq, Y0, L_zero, coeff_zero]
  · rintro ⟨w, len, rfl, rows⟩
    rw [pcomb_map_nil]
    refine ⟨fun i _ => coeff_zero i, ?_⟩
    rw [L_zero]
    ext j
    rw [coeff_zero, (vanish_spec hG 0 w hp).mp rows j (Nat.zero_le j)]

/-- If `rec` describes the solutions for the right-hand sides combined along the generators
of the solution space of `Cs`, then `restrict` describes the solutions whose parameters
satisfy `Cs`. -/
theorem restrict_spec {t : Tower (n + 1)} {R S : Poly n} {j : ℕ} {Cs : List (List ℚ)}
    {Gs : List (Poly n)} (hG : ∀ G ∈ Gs, Poly.Defined k G)
    {rec : List (Poly n) → List (Poly n) × List (List ℚ)}
    (ih : Spec k t R S j ((kernel Cs Gs.length).map fun v => Poly.norm (lcomb v Gs))
      (rec ((kernel Cs Gs.length).map fun v => Poly.norm (lcomb v Gs)))) :
    SpecC k t R S j Gs Cs (restrict Cs Gs rec) := by
  obtain ⟨klen, kiff⟩ := kernel_spec (k := k) Cs Gs.length
  obtain ⟨G, hGk⟩ : ∃ G, G = kernel Cs Gs.length := ⟨_, rfl⟩
  rw [← hGk] at klen kiff ih
  obtain ⟨out, hout⟩ : ∃ out, out = rec (G.map fun v => Poly.norm (lcomb v Gs)) :=
    ⟨_, rfl⟩
  rw [← hout] at ih
  have run : restrict Cs Gs rec = (Gs.map (fun _ => ([] : Poly n)) ++ out.1,
      (List.range Gs.length).map
          (fun i => unit Gs.length i ++ G.map fun v => -(v.getD i 0)) ++
        out.2.map fun r => List.replicate Gs.length 0 ++ r) := by
    subst hGk hout
    rfl
  rw [run]
  obtain ⟨dY, len, iff⟩ := ih
  rw [List.length_map] at len
  have comb (e p : List k) (hp : p.length = Gs.length) (h : ∀ i, p.getD i 0 = lsum e G i) :
      pcomb e (G.map fun v => Poly.norm (lcomb v Gs)) = pcomb p Gs := by
    rw [pcomb_kernel (M := Gs.length) (fun i => Poly.model k (Gs.getD i [])) _ G e (fun v hv => by
      rw [Poly.model_norm (defined_lcomb v hG), model_lcomb,
        pcomb_eq_sum Gs _ (by rw [List.length_map]; exact klen v hv)]
      exact Finset.sum_congr rfl fun i _ => by rw [getD_map_cast]),
      pcomb_eq_sum Gs p hp]
    exact Finset.sum_congr rfl fun i _ => by rw [h i]
  have ident (p e w : List k) (hp : p.length = Gs.length) (he : e.length = G.length) :
      (∀ row ∈ (List.range Gs.length).map
          (fun i => unit Gs.length i ++ G.map fun v => -(v.getD i 0)),
        dotK row (p ++ (e ++ w)) = 0) ↔ ∀ i, p.getD i 0 = lsum e G i := by
    have each (i : ℕ) (hi : i < Gs.length) :
        dotK (unit Gs.length i ++ G.map fun v => -(v.getD i 0)) (p ++ (e ++ w)) =
          p.getD i 0 - lsum e G i := by
      rw [dotK_append (by rw [length_unit, hp]), dotK_unit _ _ _ hi,
        dotK_append_of_length (by rw [List.length_map, he]), dotK_map_neg]
      ring
    constructor
    · intro h i
      by_cases hi : i < Gs.length
      · have := h _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
        rw [each i hi] at this
        exact sub_eq_zero.mp this
      · rw [List.getD_eq_default _ _ (by omega),
          lsum_eq_zero_of_length (Nat.le_of_not_lt hi) e G klen]
    · intro h row hrow
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
      rw [each i (List.mem_range.mp hi), h i, sub_self]
  have shifted (p v : List k) (hp : p.length = Gs.length) :
      (∀ row ∈ out.2.map fun r => List.replicate Gs.length 0 ++ r, dotK row (p ++ v) = 0) ↔
        ∀ row ∈ out.2, dotK row v = 0 := by
    have each (r : List ℚ) : dotK (List.replicate Gs.length 0 ++ r) (p ++ v) = dotK r v := by
      rw [dotK_append (by rw [List.length_replicate, hp]),
        dotK_zero_row _ _ fun e he => List.eq_of_mem_replicate he, zero_add]
    constructor
    · intro h r hr
      rw [← each r]
      exact h _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
    · intro h row hrow
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
      rw [each r]
      exact h r hr
  have front (p v : List k) (hp : p.length = Gs.length) :
      pcomb (p ++ v) (Gs.map (fun _ => ([] : Poly n)) ++ out.1) = pcomb v out.1 := by
    rw [pcomb_append (by simpa using hp), pcomb_map_nil, zero_add]
  refine ⟨?_, by simp, fun p Y hp => ?_⟩
  · intro Y hY
    rcases List.mem_append.mp hY with h | h
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
      exact Poly.defined_nil
    · exact dY Y h
  dsimp only
  constructor
  · rintro ⟨sol, rows⟩
    obtain ⟨es, el, eh⟩ := (kiff p hp).mp rows
    have sub : Sol t R S j (G.map fun v => Poly.norm (lcomb v Gs)) es Y :=
      ⟨sol.1, sol.2.trans (comb es p hp eh).symm⟩
    obtain ⟨w, wl, wy, wr⟩ := (iff es Y (by simpa using el)).mp sub
    refine ⟨es ++ w, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map] at wl ⊢
      omega
    · rw [front p _ hp]
      exact wy
    · intro row hrow
      rcases List.mem_append.mp hrow with h | h
      · exact (ident p es w hp el).mpr eh row h
      · exact (shifted p (es ++ w) hp).mpr wr row h
  · rintro ⟨w, wl, hY, rows⟩
    have wlen : G.length ≤ w.length := by
      simp only [List.length_append, List.length_map] at wl
      omega
    obtain ⟨es, w', rfl, el⟩ : ∃ es w' : List k, w = es ++ w' ∧ es.length = G.length :=
      ⟨w.take G.length, w.drop G.length, (List.take_append_drop _ _).symm, by simp [wlen]⟩
    have eh := (ident p es w' hp el).mp fun row h => rows row (List.mem_append_left _ h)
    have wr := (shifted p (es ++ w') hp).mp fun row h => rows row (List.mem_append_right _ h)
    rw [front p _ hp] at hY
    have sub := (iff es Y (by simpa using el)).mpr ⟨w', by
      simp only [List.length_append, List.length_map] at wl ⊢
      omega, hY, wr⟩
    exact ⟨⟨sub.1, sub.2.trans (comb es p hp eh)⟩, (kiff p hp).mpr ⟨es, el, eh⟩⟩

theorem below_split {Y : (K k n)[X]} {j : ℕ} (h : ∀ i, j + 1 ≤ i → Y.coeff i = 0) :
    Y.natDegree ≤ j ∧ ∀ i, j ≤ i → (Y - C (Y.coeff j) * X ^ j).coeff i = 0 := by
  refine ⟨natDegree_le_iff_coeff_eq_zero.mpr fun i hi => h i hi, fun i hi => ?_⟩
  rw [coeff_sub, coeff_C_mul, coeff_X_pow]
  rcases hi.eq_or_lt with rfl | lt
  · simp
  · rw [h i lt, ite_eq_right (by omega)]
    simp

theorem below_join {Y : (K k n)[X]} {j : ℕ} (y : K k n) (h : ∀ i, j ≤ i → Y.coeff i = 0) :
    ∀ i, j + 1 ≤ i → (Y + C y * X ^ j).coeff i = 0 := by
  intro i hi
  rw [coeff_add, h i (by omega), coeff_C_mul, coeff_X_pow, ite_eq_right (by omega)]
  simp

theorem value_twisted (t : Tower (n + 1)) (R S : Poly n) (lam j : ℕ) :
    Term.value k (Term.add (Poly.coeff S lam)
      (.mul (.mul (.const (j : ℚ)) t.twist) (Poly.coeff R lam))) =
      (Poly.model k S).coeff lam +
        (j : K k n) * Term.value k t.twist * (Poly.model k R).coeff lam := by
  change Term.value k (Poly.coeff S lam) +
    Term.value k (.const (j : ℚ)) * Term.value k t.twist * Term.value k (Poly.coeff R lam) = _
  rw [Poly.value_coeff, Poly.value_coeff, Term.value_const, Rat.cast_natCast]

/-- The step in which the leading coefficient of the operator has no derivative term: the
top coefficient of `Y` is determined algebraically as a combination `etas` of the
parameters. -/
theorem spec_algebraic {t : Tower (n + 1)} {R S : Poly n} {lam : ℕ} (g : Good k t R S lam)
    (j : ℕ) {Gs : List (Poly n)} (hG : ∀ G ∈ Gs, Poly.Defined k G)
    (hr : (Poly.model k R).coeff lam = 0)
    {etas : List (Term n)} (hηd : ∀ e ∈ etas, Term.InDomain k e)
    (hηl : etas.length = Gs.length)
    (hηv : ∀ p : List k,
      linComb p etas * (Poly.model k S).coeff lam = (pcomb p Gs).coeff (lam + j))
    {Gs' : List (Poly n)} (hGl : Gs'.length = Gs.length)
    (hGv : ∀ p : List k, pcomb p Gs' =
      pcomb p Gs - L t (Poly.model k R) (Poly.model k S) (C (linComb p etas) * X ^ j))
    {out : List (Poly n) × List (List ℚ)}
    (ih : SpecC k t R S j Gs' (vanish Gs (lam + j + 1) (maxLen Gs)) out) :
    Spec k t R S (j + 1) Gs (addFront (etas.map (Poly.mono j)) out.1, out.2) := by
  have sne : (Poly.model k S).coeff lam ≠ 0 := g.lead.resolve_left (not_not.mpr hr)
  obtain ⟨dY, len, iff⟩ := ih
  rw [hGl] at len
  have front : (etas.map (Poly.mono j)).length ≤ out.1.length := by simpa [hηl] using len
  refine ⟨?_, by rw [length_addFront]; exact len, fun p Y hp => ?_⟩
  · apply defined_addFront _ dY
    intro m hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    exact Poly.defined_mono j (hηd e he)
  have hp' : p.length = Gs'.length := hp.trans hGl.symm
  have frontComb (w : List k) : pcomb (p ++ w) (etas.map (Poly.mono j)) =
      C (linComb p etas) * X ^ j := by
    have := pcomb_append (p := p) (q := w) (Gs := etas.map (Poly.mono j)) (Hs := [])
      (by simp [hp, hηl])
    rw [List.append_nil, pcomb_nil_right, add_zero] at this
    rw [this, pcomb_map_mono]
  constructor
  · rintro ⟨below, eq⟩
    obtain ⟨degY, belowY⟩ := below_split below
    have top := coeff_L_top t g.degR g.degS degY
    rw [hr, zero_mul, zero_add, mul_zero, add_zero, eq] at top
    have yk : Y.coeff j = linComb p etas := by
      apply mul_right_cancel₀ sne
      rw [hηv, top]
      ring
    have sub : Sol t R S j Gs' p (Y - C (Y.coeff j) * X ^ j) := by
      refine ⟨belowY, ?_⟩
      rw [hGv, ← eq, ← yk]
      simp only [L, map_sub]
      ring
    have highRows : ∀ row ∈ vanish Gs (lam + j + 1) (maxLen Gs), dotK row p = 0 := by
      intro row h
      have := (vanish_spec hG (lam + j + 1) [] hp).mpr (fun i hi => by
        rw [← eq]
        exact coeff_L_high t g.degR g.degS degY hi) row h
      rwa [List.append_nil] at this
    obtain ⟨w, wl, wy, wr⟩ := (iff p _ hp').mp ⟨sub, highRows⟩
    refine ⟨w, by rw [length_addFront]; exact wl, ?_, wr⟩
    rw [pcomb_addFront _ _ _ front, ← wy, frontComb, ← yk]
    ring
  · rintro ⟨w, wl, rfl, rows⟩
    rw [length_addFront] at wl
    have sub := ((iff p (pcomb (p ++ w) out.1) hp').mpr ⟨w, wl, rfl, rows⟩).1
    rw [pcomb_addFront _ _ _ front, frontComb]
    refine ⟨below_join _ sub.1, ?_⟩
    rw [L_add, sub.2, hGv]
    ring

/-- The step solved by part (b) in the preceding field, for an instance `f`, `gs` with the
values of the leading coefficient equation. -/
theorem spec_solve {t : Tower (n + 1)} {R S : Poly n} {lam : ℕ} (g : Good k t R S lam)
    {lower : Term n → List (Term n) → List (Term n) × List (List ℚ)}
    (hl : SolveSpec k t.parent lower) (j : ℕ) {Gs : List (Poly n)}
    (hG : ∀ G ∈ Gs, Poly.Defined k G) (hr : (Poly.model k R).coeff lam ≠ 0)
    {f : Term n} {gs : List (Term n)}
    (hf : Term.InDomain k f) (hgd : ∀ e ∈ gs, Term.InDomain k e) (hgl : gs.length = Gs.length)
    (hfv : Term.value k f * (Poly.model k R).coeff lam = (Poly.model k S).coeff lam +
      (j : K k n) * Term.value k t.twist * (Poly.model k R).coeff lam)
    (hgv : ∀ p : List k,
      linComb p gs * (Poly.model k R).coeff lam = (pcomb p Gs).coeff (lam + j))
    {News : List (Poly n)} (hNl : News.length = (lower f gs).1.length)
    (hNv : ∀ d : List k, pcomb d News =
      -L t (Poly.model k R) (Poly.model k S) (C (linComb d (lower f gs).1) * X ^ j))
    {out : List (Poly n) × List (List ℚ)}
    (ih : SpecC k t R S j (Gs ++ News) (vanish Gs (lam + j + 1) (maxLen Gs) ++
      (lower f gs).2.map fun row => row.take (Gs.length + (lower f gs).1.length)) out) :
    Spec k t R S (j + 1) Gs
      (addFront (Gs.map (fun _ => ([] : Poly n)) ++ (lower f gs).1.map (Poly.mono j)) out.1,
        out.2) := by
  obtain ⟨sdef, sspec⟩ := hl f gs hf hgd
  obtain ⟨sol, hsol⟩ : ∃ sol, sol = lower f gs := ⟨_, rfl⟩
  rw [← hsol] at hNl hNv sdef sspec ih ⊢
  obtain ⟨dY, len, iff⟩ := ih
  rw [List.length_append, hNl] at len
  have front : (Gs.map (fun _ => ([] : Poly n)) ++ sol.1.map (Poly.mono j)).length ≤
      out.1.length := by
    simpa using len
  have frontComb {p d : List k} (hp : p.length = Gs.length) (hd : d.length = sol.1.length)
      (w : List k) :
      pcomb ((p ++ d) ++ w) (Gs.map (fun _ => ([] : Poly n)) ++ sol.1.map (Poly.mono j)) =
        C (linComb d sol.1) * X ^ j := by
    have h1 := pcomb_append (p := p ++ d) (q := w)
      (Gs := Gs.map (fun _ => ([] : Poly n)) ++ sol.1.map (Poly.mono j)) (Hs := [])
      (by simp [hp, hd])
    rw [List.append_nil, pcomb_nil_right, add_zero] at h1
    rw [h1, pcomb_append (by simpa using hp), pcomb_map_nil, pcomb_map_mono, zero_add]
  have newComb {p d : List k} (hp : p.length = Gs.length) :
      pcomb (p ++ d) (Gs ++ News) =
        pcomb p Gs - L t (Poly.model k R) (Poly.model k S) (C (linComb d sol.1) * X ^ j) := by
    rw [pcomb_append hp, hNv]
    ring
  refine ⟨?_, by rw [length_addFront]; omega, fun p Y hp => ?_⟩
  · apply defined_addFront _ dY
    intro m hm
    rcases List.mem_append.mp hm with h | h
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
      exact Poly.defined_nil
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      exact Poly.defined_mono j (sdef e he)
  constructor
  · rintro ⟨below, eq⟩
    obtain ⟨degY, belowY⟩ := below_split below
    have top := coeff_L_top t g.degR g.degS degY
    rw [eq] at top
    have low : t.parent.der k (Y.coeff j) + Term.value k f * Y.coeff j = linComb p gs := by
      apply mul_right_cancel₀ hr
      rw [hgv, top]
      linear_combination (Y.coeff j) * hfv
    obtain ⟨d, dl, dy, drows⟩ := (sspec (Y.coeff j) p (by rw [hgl, hp])).mp low
    have sub : Sol t R S j (Gs ++ News) (p ++ d) (Y - C (Y.coeff j) * X ^ j) := by
      refine ⟨belowY, ?_⟩
      rw [newComb hp, ← eq, ← dy]
      simp only [L, map_sub]
      ring
    have cRows : ∀ row ∈ vanish Gs (lam + j + 1) (maxLen Gs) ++
        sol.2.map (fun row => row.take (Gs.length + sol.1.length)), dotK row (p ++ d) = 0 := by
      intro row hrow
      rcases List.mem_append.mp hrow with h | h
      · refine (vanish_spec hG (lam + j + 1) d hp).mpr (fun i hi => ?_) row h
        rw [← eq]
        exact coeff_L_high t g.degR g.degS degY hi
      · obtain ⟨row', hr', rfl⟩ := List.mem_map.mp h
        have := dotK_take (p ++ d) row' []
        rw [List.length_append, hp, dl, List.append_nil] at this
        rw [this]
        exact drows row' hr'
    obtain ⟨w, wl, wy, wr⟩ := (iff (p ++ d) _ (by simp [hp, dl, hNl])).mp ⟨sub, cRows⟩
    refine ⟨d ++ w, ?_, ?_, ?_⟩
    · rw [length_addFront, ← List.append_assoc]
      exact wl
    · rw [← List.append_assoc, pcomb_addFront _ _ _ front, ← wy, frontComb hp dl, ← dy]
      ring
    · rw [← List.append_assoc]
      exact wr
  · rintro ⟨w, wl, rfl, rows⟩
    rw [length_addFront] at wl
    have wlen : sol.1.length ≤ w.length := by
      rw [List.length_append, hp] at wl
      omega
    obtain ⟨d, w', rfl, dl⟩ : ∃ d w' : List k, w = d ++ w' ∧ d.length = sol.1.length :=
      ⟨w.take sol.1.length, w.drop sol.1.length, (List.take_append_drop _ _).symm,
        by simp [wlen]⟩
    rw [← List.append_assoc] at wl rows ⊢
    have sub := ((iff (p ++ d) (pcomb ((p ++ d) ++ w') out.1) (by simp [hp, dl, hNl])).mpr
      ⟨w', wl, rfl, rows⟩).1
    rw [pcomb_addFront _ _ _ front, frontComb hp dl]
    refine ⟨below_join _ sub.1, ?_⟩
    rw [L_add, sub.2, newComb hp]
    ring

/-- `solvePoly` describes exactly the solutions: the polynomials `Y` with fewer than `j`
coefficients and the parameters `p` with `R Y′ + S Y = Σ pᵢ Gᵢ` are the combinations
`Y = Σ (p, w)ᵢ Yᵢ` of the returned polynomials for which `(p, w)` solves the returned
system. -/
theorem solvePoly_spec {t : Tower (n + 1)} {R S : Poly n} {lam : ℕ} (g : Good k t R S lam)
    {lower : Term n → List (Term n) → List (Term n) × List (List ℚ)}
    (hl : SolveSpec k t.parent lower) : ∀ (j : ℕ) {Gs : List (Poly n)},
      (∀ G ∈ Gs, Poly.Defined k G) → Spec k t R S j Gs (solvePoly t lower R S lam j Gs)
  | 0, Gs, hG => spec_zero t R S hG
  | j + 1, Gs, hG => by
    have rdom : Term.InDomain k (Poly.coeff R lam) := Poly.defined_coeff g.hR lam
    obtain ⟨s, hs⟩ : ∃ s : Term n, s = Term.add (Poly.coeff S lam)
      (.mul (.mul (.const (j : ℚ)) t.twist) (Poly.coeff R lam)) := ⟨_, rfl⟩
    have sdom : Term.InDomain k s := by
      rw [hs]
      exact ⟨Poly.defined_coeff g.hS lam, ⟨trivial, Tower.inDomain_twist g.admissible⟩,
        rdom⟩
    have sval : Term.value k s = (Poly.model k S).coeff lam +
        (j : K k n) * Term.value k t.twist * (Poly.model k R).coeff lam := by
      rw [hs, value_twisted]
    rw [solvePoly]
    dsimp only
    rw [← hs]
    split
    · rename_i hz
      have hr : (Poly.model k R).coeff lam = 0 := by
        rw [← Poly.value_coeff]
        exact (Term.isZero_iff rdom).mp hz
      have sv : Term.value k s = (Poly.model k S).coeff lam := by
        rw [sval, hr, mul_zero, add_zero]
      have sne' : (Poly.model k S).coeff lam ≠ 0 := g.lead.resolve_left (not_not.mpr hr)
      have sne : Term.value k s ≠ 0 := by rw [sv]; exact sne'
      have ηdom (G : Poly n) (hGm : G ∈ Gs) :
          Term.InDomain k (Term.div (Poly.coeff G (lam + j)) s) :=
        ⟨Poly.defined_coeff (hG G hGm) _, sdom, sne⟩
      have inner (G : Poly n) (hGm : G ∈ Gs) : Poly.Defined k (Poly.sub G (applyL t R S
          (Poly.mono j (Term.norm (Term.div (Poly.coeff G (lam + j)) s))))) :=
        Poly.defined_sub (hG G hGm) (defined_applyL g.admissible g.hR g.hS
          (Poly.defined_mono j (Term.norm_sound n _ (ηdom G hGm)).1))
      apply spec_algebraic g j hG hr (etas := Gs.map fun G =>
        Term.norm (Term.div (Poly.coeff G (lam + j)) s))
        (Gs' := Gs.map fun G => Poly.norm (Poly.sub G (applyL t R S (Poly.mono j
          (Term.norm (Term.div (Poly.coeff G (lam + j)) s))))))
      · intro e he
        obtain ⟨G, hGm, rfl⟩ := List.mem_map.mp he
        exact (Term.norm_sound n _ (ηdom G hGm)).1
      · rw [List.length_map]
      · intro p
        rw [linComb_map_congr _ (fun G => Term.div (Poly.coeff G (lam + j)) s) Gs p
          (fun G hGm => (Term.norm_sound n _ (ηdom G hGm)).2), coeff_pcomb,
          show (Gs.map fun G => Term.div (Poly.coeff G (lam + j)) s) =
            (coeffs Gs (lam + j)).map (fun c => Term.div c s) by
            rw [coeffs, List.map_map]; rfl,
          linComb_map_div, sv, div_mul_cancel₀ _ sne']
      · rw [List.length_map]
      · intro p
        rw [pcomb_map_congr _ (fun G => Poly.sub G (applyL t R S (Poly.mono j
          (Term.norm (Term.div (Poly.coeff G (lam + j)) s))))) Gs p
          (fun G hGm => Poly.model_norm (inner G hGm)),
          pcomb_map_sub t R S j (fun G => Term.norm (Term.div (Poly.coeff G (lam + j)) s))]
      · have dG' : ∀ G' ∈ Gs.map fun G => Poly.norm (Poly.sub G (applyL t R S (Poly.mono j
            (Term.norm (Term.div (Poly.coeff G (lam + j)) s))))), Poly.Defined k G' := by
          intro G' hG'
          obtain ⟨G, hGm, rfl⟩ := List.mem_map.mp hG'
          exact Poly.defined_norm (inner G hGm)
        apply restrict_spec dG'
        apply solvePoly_spec g hl j
        intro G' hG'
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp hG'
        exact Poly.defined_norm (defined_lcomb v dG')
    · rename_i hz
      have hr : (Poly.model k R).coeff lam ≠ 0 := by
        rw [← Poly.value_coeff]
        exact fun z => hz ((Term.isZero_iff rdom).mpr z)
      have rne : Term.value k (Poly.coeff R lam) ≠ 0 := by
        rw [Poly.value_coeff]
        exact hr
      have fdom : Term.InDomain k (Term.div s (Poly.coeff R lam)) := ⟨sdom, rdom, rne⟩
      have cdom (c : Term n) (hc : c ∈ coeffs Gs (lam + j)) :
          Term.InDomain k (Term.div c (Poly.coeff R lam)) :=
        ⟨defined_coeffs hG _ c hc, rdom, rne⟩
      have gdom : ∀ e ∈ (coeffs Gs (lam + j)).map fun c =>
          Term.norm (Term.div c (Poly.coeff R lam)), Term.InDomain k e := by
        intro e he
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
        exact (Term.norm_sound n _ (cdom c hc)).1
      have fdom' := (Term.norm_sound n _ fdom).1
      have inner (h : Term n) (hh : h ∈ (lower (Term.norm (Term.div s (Poly.coeff R lam)))
          ((coeffs Gs (lam + j)).map fun c => Term.norm (Term.div c (Poly.coeff R lam)))).1) :
          Poly.Defined k (Poly.neg (applyL t R S (Poly.mono j h))) :=
        Poly.defined_neg (defined_applyL g.admissible g.hR g.hS
          (Poly.defined_mono j ((hl _ _ fdom' gdom).1 h hh)))
      apply spec_solve g hl j hG hr fdom' gdom
        (News := (lower (Term.norm (Term.div s (Poly.coeff R lam)))
          ((coeffs Gs (lam + j)).map fun c =>
            Term.norm (Term.div c (Poly.coeff R lam)))).1.map
            fun h => Poly.norm (Poly.neg (applyL t R S (Poly.mono j h))))
      · simp [coeffs]
      · rw [(Term.norm_sound n _ fdom).2]
        change Term.value k s / Term.value k (Poly.coeff R lam) * _ = _
        rw [Poly.value_coeff, div_mul_cancel₀ _ hr, sval]
      · intro p
        rw [linComb_map_congr _ (fun c => Term.div c (Poly.coeff R lam)) _ p
          (fun c hc => (Term.norm_sound n _ (cdom c hc)).2), linComb_map_div,
          Poly.value_coeff, div_mul_cancel₀ _ hr, coeff_pcomb]
      · rw [List.length_map]
      · intro d
        rw [pcomb_map_congr _ (fun h => Poly.neg (applyL t R S (Poly.mono j h))) _ d
          (fun h hh => Poly.model_norm (inner h hh)), pcomb_map_neg]
      · have dG' : ∀ G' ∈ Gs ++ (lower (Term.norm (Term.div s (Poly.coeff R lam)))
            ((coeffs Gs (lam + j)).map fun c =>
              Term.norm (Term.div c (Poly.coeff R lam)))).1.map
              fun h => Poly.norm (Poly.neg (applyL t R S (Poly.mono j h))),
            Poly.Defined k G' := by
          intro G' hG'
          rcases List.mem_append.mp hG' with h | h
          · exact hG G' h
          · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
            exact Poly.defined_norm (inner e he)
        apply restrict_spec dG'
        apply solvePoly_spec g hl j
        intro G' hG'
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp hG'
        exact Poly.defined_norm (defined_lcomb v dG')

/-! ### Compression -/

/-- A combination, with coefficients `es`, of terms that are rational combinations of the
`H i`, with the coordinates from `m` on of the vectors `v ∈ G` as coefficients, is the
combination of the `H i` with the coordinates from `m` on of the combination of `G`. -/
theorem mixSum {m r : ℕ} (H : ℕ → K k n) (F : List ℚ → Term n) :
    ∀ (G : List (List ℚ)) (es : List k),
      (∀ v ∈ G, Term.value k (F v) =
        ∑ i ∈ Finset.range r, constHom k n ((v.getD (m + i) 0 : ℚ) : k) * H i) →
      linComb es (G.map F) = ∑ i ∈ Finset.range r, constHom k n (lsum es G (m + i)) * H i
  | [], es, _ => by simp [linComb_nil_right, Linear.lsum]
  | g :: G, [], _ => by simp [linComb_nil_left, Linear.lsum]
  | g :: G, e :: es, h => by
    rw [List.map_cons, linComb_cons, h g List.mem_cons_self,
      mixSum H F G es fun v hv => h v (List.mem_cons_of_mem _ hv), Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lsum_cons, map_add, map_mul]
    ring

/-- `compress` describes the same solutions with one basis element for each generator of
the solution space of the system: the combinations `y = Σ dᵢ hᵢ` for which `(c, d)` solves
`rows` are the combinations of the new basis for which `(c, e)` solves the new system. -/
theorem compress_spec {m : ℕ} {hs : List (Term n)} {rows : List (List ℚ)}
    {mix : List ℚ → Term n}
    (hmix : ∀ v : List ℚ, v.length = hs.length →
      Term.InDomain k (mix v) ∧
        Term.value k (mix v) = linComb (v.map fun (q : ℚ) => (q : k)) hs) :
    (∀ h ∈ (compress m hs.length rows mix).1, Term.InDomain k h) ∧
    ∀ (y : K k n) (c : List k), c.length = m →
      ((∃ d : List k, d.length = hs.length ∧ y = linComb d hs ∧
          ∀ row ∈ rows, dotK row (c ++ d) = 0) ↔
        ∃ e : List k, e.length = (compress m hs.length rows mix).1.length ∧
          y = linComb e (compress m hs.length rows mix).1 ∧
          ∀ row ∈ (compress m hs.length rows mix).2, dotK row (c ++ e) = 0) := by
  obtain ⟨klen, kiff⟩ := kernel_spec (k := k) rows (m + hs.length)
  obtain ⟨G, hG⟩ : ∃ G, G = kernel rows (m + hs.length) := ⟨_, rfl⟩
  rw [← hG] at klen kiff
  have run : compress m hs.length rows mix = (G.map fun v => mix (v.drop m),
      (List.range m).map fun i => unit m i ++ G.map fun v => -(v.getD i 0)) := by
    subst hG
    rfl
  rw [run]
  have dropLen (v : List ℚ) (hv : v ∈ G) : (v.drop m).length = hs.length := by
    rw [List.length_drop, klen v hv]
    omega
  have mixVal : ∀ v ∈ G, Term.value k (mix (v.drop m)) = ∑ i ∈ Finset.range hs.length,
      constHom k n ((v.getD (m + i) 0 : ℚ) : k) * Term.value k (hs.getD i (.const 0)) := by
    intro v hv
    rw [(hmix _ (dropLen v hv)).2,
      linComb_eq_sum hs _ (by rw [List.length_map]; exact dropLen v hv)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [getD_map_cast]
    simp [List.getD, List.getElem?_drop]
  have rowsVal (c e : List k) (hc : c.length = m) :
      (∀ row ∈ (List.range m).map fun i => unit m i ++ G.map fun v => -(v.getD i 0),
        dotK row (c ++ e) = 0) ↔ ∀ i, i < m → c.getD i 0 = lsum e G i := by
    constructor
    · intro h i hi
      have := h _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
      rw [dotK_append (by rw [length_unit, hc]), dotK_unit _ _ _ hi, dotK_map_neg] at this
      linear_combination this
    · intro h row hrow
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
      rw [dotK_append (by rw [length_unit, hc]), dotK_unit _ _ _ (List.mem_range.mp hi),
        dotK_map_neg, h i (List.mem_range.mp hi)]
      ring
  refine ⟨?_, fun y c hc => ?_⟩
  · intro h hh
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hh
    exact (hmix _ (dropLen v hv)).1
  rw [List.length_map]
  constructor
  · rintro ⟨d, dl, rfl, rows0⟩
    obtain ⟨es, el, eh⟩ := (kiff (c ++ d) (by rw [List.length_append, hc, dl])).mp rows0
    refine ⟨es, el, ?_, (rowsVal c es hc).mpr fun i hi => ?_⟩
    · rw [mixSum (m := m) (fun i => Term.value k (hs.getD i (.const 0))) _ G es mixVal,
        linComb_eq_sum hs d dl]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← eh (m + i), List.getD_append_right _ _ _ _ (by omega)]
      simp [hc]
    · rw [← eh i, List.getD_append _ _ _ _ (by omega)]
  · rintro ⟨e, el, rfl, rows'⟩
    have agree := (rowsVal c e hc).mp rows'
    obtain ⟨x, hx⟩ : ∃ x : List k, x = (List.range (m + hs.length)).map (lsum e G) :=
      ⟨_, rfl⟩
    have xl : x.length = m + hs.length := by simp [hx]
    have xi (i : ℕ) : x.getD i 0 = lsum e G i := by
      rw [hx, getD_map_range]
      split
      · rfl
      · rename_i h
        exact (lsum_eq_zero_of_length (Nat.le_of_not_lt h) e G klen).symm
    have sol := (kiff x xl).mpr ⟨e, el, xi⟩
    have split : x = c ++ x.drop m := by
      conv_lhs => rw [← List.take_append_drop m x]
      congr 1
      apply List.ext_getElem
      · simp [xl, hc]
      · intro i h1 h2
        have hi : i < m := by rw [← hc]; exact h2
        have a := agree i hi
        rw [← xi i] at a
        rw [List.getElem_take]
        simpa [List.getD, h2, show i < x.length by omega] using a.symm
    refine ⟨x.drop m, by rw [List.length_drop, xl]; omega, ?_, by rw [← split]; exact sol⟩
    rw [mixSum (m := m) (fun i => Term.value k (hs.getD i (.const 0))) _ G e mixVal,
      linComb_eq_sum hs _ (by rw [List.length_drop, xl]; omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← xi (m + i)]
    simp [List.getD, List.getElem?_drop]

end Solve

end SympyProofs.Calculus.Risch
