module

public import SympyProofs.Calculus.Risch.Program.Rel
public import SympyProofs.Calculus.Risch.Spec.Admissible
public import SympyProofs.Calculus.Risch.Algebra.SimplePole
public import SympyProofs.Calculus.Risch.Proof.Deriv
public import SympyProofs.Calculus.Risch.Proof.Linear
public import SympyProofs.Calculus.Risch.Proof.Constraints
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A space of elements of the field of a tower that contains every logarithmic derivative
and is cut out by linear conditions: at most simple poles, no pole at an exponential
generator, and a constant term of the same kind one level down, up to a constant multiple of
the derivative of the exponent. At depth zero the space is zero.

`relRows` computes a linear system over the rationals for the constants `αᵢ` such that
`Σ αᵢ wᵢ` lies in the space. At each step the elements are put over one denominator `T`. At
most simple poles means that the greatest common divisor of `T` and its derivative divides
the numerator, the polynomial part must be a constant, and that constant is examined one
level down. Every condition is a linear equation over the field in constant unknowns, hence
a linear system over the rationals by the Lemma of `Proof/Constraints` (Risch 1969,
pp. 186–187). -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial SimplePole

noncomputable local instance intAlgebraRel {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

section Generic

variable {F : Type*} [Field F] {D : Derivation ℤ F F}

/-- The logarithmic derivative of a product is the sum of the logarithmic derivatives. -/
theorem logDeriv_mul {A B : F} (hA : A ≠ 0) (hB : B ≠ 0) :
    D (A * B) / (A * B) = D A / A + D B / B := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- The logarithmic derivative of a power is a multiple of the logarithmic derivative. -/
theorem logDeriv_pow {A : F} (hA : A ≠ 0) : ∀ m : ℕ, D (A ^ m) / A ^ m = (m : F) * (D A / A)
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ, logDeriv_mul (pow_ne_zero m hA) hA, logDeriv_pow hA m]
    push_cast
    ring

/-- The logarithmic derivative of an inverse is the negative of the logarithmic derivative. -/
theorem logDeriv_inv {A : F} (hA : A ≠ 0) : D A⁻¹ / A⁻¹ = -(D A / A) := by
  rw [Derivation.leibniz_inv]
  simp only [smul_eq_mul]
  field_simp

/-- The logarithmic derivative of a quotient is the difference of the logarithmic
derivatives. -/
theorem logDeriv_div {A B : F} (hA : A ≠ 0) (hB : B ≠ 0) :
    D (A / B) / (A / B) = D A / A - D B / B := by
  have e : A / B = A * B⁻¹ := div_eq_mul_inv _ _
  rw [e, logDeriv_mul hA (inv_ne_zero hB), logDeriv_inv hB]
  ring

end Generic

/-- The space containing the logarithmic derivatives of the field of a tower. -/
def Tower.Rel (k : Type) [Field k] [CharZero k] : {n : ℕ} → Tower n → K k n → Prop
  | _, .const, y => y = 0
  | _, .prim (n := n) t _, y =>
    Simple (F := K k n) y ∧ ∃ y₀ : K k n, Tower.Rel k t y₀ ∧ Proper (y - RatFunc.C y₀)
  | _, .exp (n := n) t u, y =>
    Simple (F := K k n) y ∧ Integral (X : (K k n)[X]) y ∧
      ∃ (y₀ : K k n) (c : k), Tower.Rel k t y₀ ∧
        Proper (y - RatFunc.C (y₀ + constHom k n c * t.der k (Term.value k u)))

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

/-- At depth zero the space is zero. -/
theorem Tower.rel_const {y : K k 0} : Tower.Rel k .const y ↔ y = 0 := Iff.rfl

/-- At a primitive step: at most simple poles, and a constant term in the space of the
preceding field. -/
theorem Tower.rel_prim {t : Tower n} {b : Term n} {y : K k (n + 1)} :
    Tower.Rel k (t.prim b) y ↔
      Simple (F := K k n) y ∧
        ∃ y₀ : K k n, Tower.Rel k t y₀ ∧ Proper (y - RatFunc.C y₀) :=
  Iff.rfl

/-- At an exponential step: at most simple poles, no pole at the generator, and a constant
term in the space of the preceding field up to a constant multiple of the derivative of the
exponent. -/
theorem Tower.rel_exp {t : Tower n} {u : Term n} {y : K k (n + 1)} :
    Tower.Rel k (t.exp u) y ↔
      Simple (F := K k n) y ∧ Integral (X : (K k n)[X]) y ∧
        ∃ (y₀ : K k n) (c : k), Tower.Rel k t y₀ ∧
          Proper (y - RatFunc.C (y₀ + constHom k n c * t.der k (Term.value k u))) :=
  Iff.rfl

namespace Tower.Rel

/-- Zero lies in the space. -/
theorem zero (t : Tower n) : Tower.Rel k t 0 := by
  induction t with
  | const => exact Tower.rel_const.mpr rfl
  | @prim n t b ih =>
    refine Tower.rel_prim.mpr ⟨simple_zero, 0, ih, ?_⟩
    simpa using proper_zero (F := K k n)
  | @exp n t u ih =>
    refine Tower.rel_exp.mpr ⟨simple_zero, ?_, 0, 0, ih, ?_⟩
    · simpa using integral_algebraMap prime_X (0 : (K k n)[X])
    · simpa using proper_zero (F := K k n)

/-- The space is closed under addition. -/
theorem add {t : Tower n} {y z : K k n} (hy : Tower.Rel k t y) (hz : Tower.Rel k t z) :
    Tower.Rel k t (y + z) := by
  induction t with
  | const =>
    rw [Tower.rel_const] at hy hz ⊢
    rw [hy, hz, add_zero]
  | @prim n t b ih =>
    obtain ⟨sy, y₀, ry, py⟩ := Tower.rel_prim.mp hy
    obtain ⟨sz, z₀, rz, pz⟩ := Tower.rel_prim.mp hz
    refine Tower.rel_prim.mpr ⟨sy.add sz, y₀ + z₀, ih ry rz, ?_⟩
    have := py.add pz
    rw [show y + z - RatFunc.C (y₀ + z₀) = y - RatFunc.C y₀ + (z - RatFunc.C z₀) by
      rw [map_add]; ring]
    exact this
  | @exp n t u ih =>
    obtain ⟨sy, iy, y₀, c, ry, py⟩ := Tower.rel_exp.mp hy
    obtain ⟨sz, iz, z₀, d, rz, pz⟩ := Tower.rel_exp.mp hz
    refine Tower.rel_exp.mpr ⟨sy.add sz, iy.add prime_X iz, y₀ + z₀, c + d, ih ry rz, ?_⟩
    have := py.add pz
    rw [show y + z - RatFunc.C (y₀ + z₀ + constHom k n (c + d) * t.der k (Term.value k u)) =
      y - RatFunc.C (y₀ + constHom k n c * t.der k (Term.value k u)) +
        (z - RatFunc.C (z₀ + constHom k n d * t.der k (Term.value k u))) by
      simp only [map_add, map_mul]
      ring]
    exact this

/-- The space is closed under multiplication by a constant. -/
theorem const_mul {t : Tower n} (c : k) {y : K k n} (hy : Tower.Rel k t y) :
    Tower.Rel k t (constHom k n c * y) := by
  induction t with
  | const =>
    rw [Tower.rel_const] at hy ⊢
    rw [hy, mul_zero]
  | @prim n t b ih =>
    obtain ⟨sy, y₀, ry, py⟩ := Tower.rel_prim.mp hy
    refine Tower.rel_prim.mpr ⟨?_, constHom k n c * y₀, ih ry, ?_⟩
    · rw [constHom_succ]
      exact sy.C_mul _
    · rw [constHom_succ, map_mul, ← mul_sub]
      exact py.C_mul _
  | @exp n t u ih =>
    obtain ⟨sy, iy, y₀, d, ry, py⟩ := Tower.rel_exp.mp hy
    refine Tower.rel_exp.mpr ⟨?_, ?_, constHom k n c * y₀, c * d, ih ry, ?_⟩
    · rw [constHom_succ]
      exact sy.C_mul _
    · rw [constHom_succ, ← RatFunc.algebraMap_C]
      exact (integral_algebraMap prime_X _).mul prime_X iy
    · rw [constHom_succ, show RatFunc.C (constHom k n c * y₀ +
          constHom k n (c * d) * t.der k (Term.value k u)) = RatFunc.C (constHom k n c) *
            RatFunc.C (y₀ + constHom k n d * t.der k (Term.value k u)) by
        rw [← map_mul, map_mul (constHom k n)]
        congr 1
        ring, ← mul_sub]
      exact py.C_mul _

/-- The space is closed under negation. -/
theorem neg {t : Tower n} {y : K k n} (hy : Tower.Rel k t y) : Tower.Rel k t (-y) := by
  have := const_mul (-1) hy
  simpa using this

/-- The space is closed under subtraction. -/
theorem sub {t : Tower n} {y z : K k n} (hy : Tower.Rel k t y) (hz : Tower.Rel k t z) :
    Tower.Rel k t (y - z) := by
  rw [sub_eq_add_neg]
  exact add hy hz.neg

end Tower.Rel

local notation "ι" => algebraMap (K k n)[X] (RatFunc (K k n))

/-- The logarithmic derivative of a polynomial differs by a proper fraction from the
logarithmic derivative of its leading coefficient, plus its degree times the derivative of
the exponent at an exponential step. -/
theorem proper_logDeriv_poly (t : Tower (n + 1)) {P : (K k n)[X]} (hP : P ≠ 0) :
    Proper (ι (Tower.polyDer k t P) / ι P -
      RatFunc.C (t.parent.der k P.leadingCoeff / P.leadingCoeff +
        (P.natDegree : K k n) * Term.value k t.twist)) := by
  obtain ⟨c, hc⟩ : ∃ c, c = t.parent.der k P.leadingCoeff / P.leadingCoeff +
    (P.natDegree : K k n) * Term.value k t.twist := ⟨_, rfl⟩
  rw [← hc]
  have hP' := RatFunc.algebraMap_ne_zero hP
  have lc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  refine ⟨Tower.polyDer k t P - C c * P, P, ?_, ?_⟩
  · rw [degree_eq_natDegree hP]
    apply (degree_lt_iff_coeff_zero _ _).mpr
    intro m hm
    rw [coeff_sub, coeff_C_mul, Tower.coeff_polyDer,
      coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hm), mul_zero, add_zero]
    rcases Nat.lt_or_eq_of_le hm with lt | rfl
    · rw [coeff_eq_zero_of_natDegree_lt lt]
      simp
    · have e : P.coeff P.natDegree = P.leadingCoeff := rfl
      rw [e, hc]
      field_simp
      ring
  · rw [map_sub, map_mul, RatFunc.algebraMap_C]
    field_simp

/-- Every logarithmic derivative lies in the space. -/
theorem Tower.rel_logDeriv (t : Tower n) {A : K k n} (hA : A ≠ 0) :
    Tower.Rel k t (t.der k A / A) := by
  induction t with
  | const =>
    rw [Tower.rel_const]
    change (0 : Derivation ℤ (K k 0) (K k 0)) A / A = 0
    simp
  | @prim n t b ih =>
    have tw : Term.value k (t.prim b).twist = 0 := Tower.value_twist (t.prim b)
    have poly (P : (K k n)[X]) (hP : P ≠ 0) : Tower.Rel k (t.prim b)
        ((t.prim b).der k (algebraMap (K k n)[X] (RatFunc (K k n)) P) /
          algebraMap (K k n)[X] (RatFunc (K k n)) P) := by
      rw [Tower.der_algebraMap]
      refine Tower.rel_prim.mpr ⟨simple_logDeriv _ hP, t.der k P.leadingCoeff / P.leadingCoeff,
        ih (leadingCoeff_ne_zero.mpr hP), ?_⟩
      have := proper_logDeriv_poly (t.prim b) hP
      rw [tw, mul_zero, add_zero] at this
      exact this
    obtain ⟨u, d, hu, hd, rfl⟩ : ∃ u d : (K k n)[X], u ≠ 0 ∧ d ≠ 0 ∧
        A = algebraMap (K k n)[X] (RatFunc (K k n)) u /
          algebraMap (K k n)[X] (RatFunc (K k n)) d :=
      ⟨_, _, RatFunc.num_ne_zero hA, RatFunc.denom_ne_zero A, (RatFunc.num_div_denom A).symm⟩
    rw [logDeriv_div (RatFunc.algebraMap_ne_zero hu) (RatFunc.algebraMap_ne_zero hd)]
    exact (poly u hu).sub (poly d hd)
  | @exp n t w ih =>
    have tw : Term.value k (t.exp w).twist = t.der k (Term.value k w) :=
      Tower.value_twist (t.exp w)
    have hX : Tower.polyDer k (t.exp w) X = C (t.der k (Term.value k w)) * X := by
      apply RatFunc.algebraMap_injective (K k n)
      rw [← Tower.der_algebraMap, RatFunc.algebraMap_X, Tower.der_exp_X, map_mul,
        RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    have poly (P : (K k n)[X]) (hP : P ≠ 0) : Tower.Rel k (t.exp w)
        ((t.exp w).der k (algebraMap (K k n)[X] (RatFunc (K k n)) P) /
          algebraMap (K k n)[X] (RatFunc (K k n)) P) := by
      rw [Tower.der_algebraMap]
      refine Tower.rel_exp.mpr ⟨simple_logDeriv _ hP, integral_X_logDeriv _ hX hP,
        t.der k P.leadingCoeff / P.leadingCoeff, (P.natDegree : k),
        ih (leadingCoeff_ne_zero.mpr hP), ?_⟩
      have := proper_logDeriv_poly (t.exp w) hP
      rw [tw] at this
      rw [map_natCast]
      exact this
    obtain ⟨u, d, hu, hd, rfl⟩ : ∃ u d : (K k n)[X], u ≠ 0 ∧ d ≠ 0 ∧
        A = algebraMap (K k n)[X] (RatFunc (K k n)) u /
          algebraMap (K k n)[X] (RatFunc (K k n)) d :=
      ⟨_, _, RatFunc.num_ne_zero hA, RatFunc.denom_ne_zero A, (RatFunc.num_div_denom A).symm⟩
    rw [logDeriv_div (RatFunc.algebraMap_ne_zero hu) (RatFunc.algebraMap_ne_zero hd)]
    exact (poly u hu).sub (poly d hd)

/-! ### Combinations of coefficient lists -/

/-- A combination of the polynomials of coefficient lists with constant coefficients. -/
noncomputable def pcombK (p : List k) (Gs : List (Poly n)) : (K k n)[X] :=
  (List.zipWith (fun (c : k) (G : Poly n) => C (constHom k n c) * Poly.model k G) p Gs).sum

theorem pcombK_cons (c : k) (p : List k) (G : Poly n) (Gs : List (Poly n)) :
    pcombK (c :: p) (G :: Gs) = C (constHom k n c) * Poly.model k G + pcombK p Gs := by
  simp [pcombK]

theorem pcombK_nil_left (Gs : List (Poly n)) : pcombK ([] : List k) Gs = 0 := by
  simp [pcombK]

theorem pcombK_nil_right (p : List k) : pcombK p ([] : List (Poly n)) = 0 := by
  simp [pcombK]

/-- Multiplying every coefficient list by `q` multiplies the combination by `q`. -/
theorem pcombK_map_mul (q : Poly n) : ∀ (Ws : List (Poly n)) (c : List k),
    pcombK c (Ws.map fun W => Poly.mul W q) = pcombK c Ws * Poly.model k q
  | [], c => by simp [pcombK_nil_right]
  | W :: Ws, [] => by simp [pcombK_nil_left]
  | W :: Ws, x :: c => by
    rw [List.map_cons, pcombK_cons, pcombK_cons, pcombK_map_mul q Ws c, Poly.model_mul]
    ring

/-- A decomposition of every coefficient list by the same divisor decomposes the
combination. -/
theorem pcombK_decomp (D : (K k n)[X]) (q r : Poly n → Poly n) :
    ∀ (Ws : List (Poly n)) (p : List k),
      (∀ W ∈ Ws, Poly.model k W = D * Poly.model k (q W) + Poly.model k (r W)) →
      pcombK p Ws = D * pcombK p (Ws.map q) + pcombK p (Ws.map r)
  | [], p, _ => by simp [pcombK_nil_right]
  | W :: Ws, [], _ => by simp [pcombK_nil_left]
  | W :: Ws, c :: p, h => by
    rw [List.map_cons, List.map_cons, pcombK_cons, pcombK_cons, pcombK_cons,
      pcombK_decomp D q r Ws p (fun W hW => h W (List.mem_cons_of_mem _ hW)),
      h W List.mem_cons_self]
    ring

/-- A combination of polynomials of degree below `d` has degree below `d`. -/
theorem degree_pcombK_lt {d : WithBot ℕ} (hd : ⊥ < d) (r : Poly n → Poly n) :
    ∀ (Ws : List (Poly n)) (p : List k), (∀ W ∈ Ws, (Poly.model k (r W)).degree < d) →
      (pcombK p (Ws.map r)).degree < d
  | [], p, _ => by simpa [pcombK_nil_right] using hd
  | W :: Ws, [], _ => by simpa [pcombK_nil_left] using hd
  | W :: Ws, c :: p, h => by
    rw [List.map_cons, pcombK_cons]
    exact (degree_add_le _ _).trans_lt (max_lt
      (((degree_mul_le _ _).trans (add_le_of_nonpos_left degree_C_le)).trans_lt
        (h W List.mem_cons_self))
      (degree_pcombK_lt hd r Ws p fun W hW => h W (List.mem_cons_of_mem _ hW)))

/-- A combination of the terms of coefficient lists is the combination of their
polynomials. -/
theorem linComb_toTerm : ∀ (Ps : List (Poly n)) (p : List k),
    linComb p (Ps.map Poly.toTerm) = ι (pcombK p Ps)
  | [], p => by simp [pcombK_nil_right, linComb_nil_right]
  | P :: Ps, [] => by simp [pcombK_nil_left, linComb_nil_left]
  | P :: Ps, c :: p => by
    rw [List.map_cons, linComb_cons, constHom_succ, linComb_toTerm Ps p, pcombK_cons, map_add,
      map_mul, RatFunc.algebraMap_C, Poly.value_toTerm]

/-- A polynomial is its constant coefficient plus the generator times the rest. -/
theorem Poly.model_head_tail (A : Poly n) :
    Poly.model k A = C (Term.value k (Poly.coeff A 0)) + X * Poly.model k A.tail := by
  cases A with
  | nil => simp [Poly.model_nil, Poly.coeff, Term.value_const]
  | cons a as => simp [Poly.model_cons, Poly.coeff]

/-- A combination is the combination of the constant coefficients plus the generator times
the combination of the rests. -/
theorem pcombK_head_tail : ∀ (As : List (Poly n)) (p : List k),
    pcombK p As =
      C (linComb p (As.map fun A => Poly.coeff A 0)) + X * pcombK p (As.map List.tail)
  | [], p => by simp [pcombK_nil_right, linComb_nil_right]
  | A :: As, [] => by simp [pcombK_nil_left, linComb_nil_left]
  | A :: As, c :: p => by
    rw [List.map_cons, List.map_cons, pcombK_cons, pcombK_cons, linComb_cons,
      pcombK_head_tail As p, Poly.model_head_tail A]
    simp only [map_add, map_mul]
    ring

/-- A combination is a constant exactly when the tails combine to zero; the constant is then
the combination of the heads. -/
theorem pcombK_eq_C_iff (As : List (Poly n)) (p : List k) (c : K k n) :
    pcombK p As = C c ↔
      pcombK p (As.map List.tail) = 0 ∧ linComb p (As.map fun A => Poly.coeff A 0) = c := by
  rw [pcombK_head_tail]
  constructor
  · intro h
    have h0 := congrArg (fun Q : (K k n)[X] => Q.coeff 0) h
    simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero] at h0
    refine ⟨?_, h0⟩
    rw [h0] at h
    have := add_left_cancel (a := C c) (b := X * pcombK p (As.map List.tail)) (c := 0)
      (by rw [add_zero]; exact h)
    exact (mul_eq_zero.mp this).resolve_left X_ne_zero
  · rintro ⟨h1, h2⟩
    rw [h1, h2, mul_zero, add_zero]

/-! ### The common denominator -/

namespace Poly

private theorem model_one : model k ([.const 1] : Poly n) = 1 := by
  simp [model_cons, model_nil, Term.value_const]

private theorem defined_one : Defined k ([.const 1] : Poly n) := fun e he => by
  rw [List.mem_singleton.mp he]
  trivial

/-- The common denominator does not vanish, and every combination of the terms is the
combination of the numerators over it. -/
theorem commonDen_spec : ∀ {gs : List (Term (n + 1))}, (∀ g ∈ gs, Term.InDomain k g) →
    Defined k (commonDen gs).2 ∧ model k (commonDen gs).2 ≠ 0 ∧
      (∀ W ∈ (commonDen gs).1, Defined k W) ∧ (commonDen gs).1.length = gs.length ∧
      ∀ c : List k, linComb c gs = ι (pcombK c (commonDen gs).1) / ι (model k (commonDen gs).2)
  | [], _ => by
    refine ⟨defined_one, by rw [commonDen, model_one]; exact one_ne_zero,
      fun _ h => by simp [commonDen] at h, rfl, fun c => ?_⟩
    simp [commonDen, pcombK_nil_right, linComb_nil_right]
  | g :: gs, h => by
    obtain ⟨dT, nT, dW, len, eq⟩ :=
      commonDen_spec (gs := gs) fun e he => h e (List.mem_cons_of_mem _ he)
    obtain ⟨fe, fn⟩ := ofTerm_spec g (h g List.mem_cons_self)
    obtain ⟨dp, dq⟩ := ofTerm_defined (k := k) g
    have qn : model k (ofTerm g).2 ≠ 0 := fun z => fn (by rw [z, map_zero])
    refine ⟨defined_mul dq dT, ?_, ?_, by simp [commonDen, len], fun c => ?_⟩
    · rw [commonDen, model_mul]
      exact mul_ne_zero qn nT
    · intro W hW
      rcases List.mem_cons.mp hW with rfl | hW
      · exact defined_mul dp dT
      · obtain ⟨W', hW', rfl⟩ := List.mem_map.mp hW
        exact defined_mul (dW W' hW') dq
    · cases c with
      | nil => simp [pcombK_nil_left, linComb_nil_left]
      | cons x c =>
        have nT' := RatFunc.algebraMap_ne_zero nT
        rw [linComb_cons, eq c, constHom_succ]
        simp only [commonDen, pcombK_cons, pcombK_map_mul, model_mul, map_add, map_mul]
        rw [fe, RatFunc.algebraMap_C]
        field_simp

end Poly

/-! ### One step -/

namespace Rel

/-- With the pole condition expressed as a divisibility: membership of a fraction, written by
two divisions with remainder, is the vanishing of the first remainder together with a
condition on the second quotient. -/
theorem rel_iff {F : Type*} [Field F] {P : Prop} {T G Ts W Q R A N : F[X]} (hT : T ≠ 0)
    (hG : T = G * Ts) (simple : P ↔ G ∣ W) (hW : W = G * Q + R) (hR : R.degree < G.degree)
    (hQ : Q = Ts * A + N) (hN : N.degree < Ts.degree) (S : F → Prop) :
    (P ∧ ∃ c, S c ∧ Proper (algebraMap F[X] (RatFunc F) W / algebraMap F[X] (RatFunc F) T -
        RatFunc.C c)) ↔ (R = 0 ∧ ∃ c, S c ∧ A = C c) := by
  have Gn : G ≠ 0 := fun z => hT (by rw [hG, z, zero_mul])
  have key : G ∣ W ↔ R = 0 := by
    rw [hW, dvd_add_right (dvd_mul_right _ _)]
    exact ⟨fun h => eq_zero_of_dvd_of_degree_lt h hR, fun h => h ▸ dvd_zero _⟩
  have frac (r0 : R = 0) : algebraMap F[X] (RatFunc F) W / algebraMap F[X] (RatFunc F) T =
      algebraMap F[X] (RatFunc F) Q / algebraMap F[X] (RatFunc F) Ts := by
    rw [hW, r0, add_zero, hG, map_mul, map_mul,
      mul_div_mul_left _ _ (RatFunc.algebraMap_ne_zero Gn)]
  constructor
  · rintro ⟨hp, c, sc, pc⟩
    have r0 := key.mp (simple.mp hp)
    rw [frac r0] at pc
    exact ⟨r0, c, sc, (proper_sub_C_iff (by rw [hQ]; ring) hN c).mp pc⟩
  · rintro ⟨r0, c, sc, ac⟩
    refine ⟨simple.mpr (key.mpr r0), c, sc, ?_⟩
    rw [frac r0]
    exact (proper_sub_C_iff (by rw [hQ]; ring) hN c).mpr ac

/-- A combination of the terms has at most simple poles, no pole at the generator when
`atX` is set, and a constant term in `S`, exactly when the remainders combine to zero and
the polynomial parts combine to a constant in `S`. -/
theorem parts_spec (atX : Bool) {ws : List (Term (n + 1))}
    (hw : ∀ w ∈ ws, Term.InDomain k w) :
    (∀ R ∈ (parts atX ws).1, Poly.Defined k R) ∧
      (∀ A ∈ (parts atX ws).2, Poly.Defined k A) ∧ (parts atX ws).2.length = ws.length ∧
      ∀ (α : List k) (S : K k n → Prop),
        ((Simple (linComb α ws) ∧ (atX = true → Integral X (linComb α ws))) ∧
          ∃ c, S c ∧ Proper (linComb α ws - RatFunc.C c)) ↔
        (pcombK α (parts atX ws).1 = 0 ∧ ∃ c, S c ∧ pcombK α (parts atX ws).2 = C c) := by
  obtain ⟨dT0, nT0, dW0, len0, comb0⟩ := Poly.commonDen_spec hw
  obtain ⟨mT, dT, nrmT, -⟩ := Poly.trim_spec (Poly.defined_norm dT0)
  obtain ⟨T, hT⟩ : ∃ T, T = Poly.trim (Poly.norm (Poly.commonDen ws).2) := ⟨_, rfl⟩
  rw [← hT] at mT dT nrmT
  rw [Poly.model_norm dT0] at mT
  have Tn : Poly.model k T ≠ 0 := mT ▸ nT0
  have nT : Poly.Normal k T := nrmT.resolve_left fun h => Tn (by rw [h, Poly.model_nil])
  obtain ⟨dT', hdT'⟩ : ∃ dT', dT' = if atX then (.const 0 : Term n) :: Poly.formalD T
    else Poly.formalD T := ⟨_, rfl⟩
  have ddT : Poly.Defined k dT' := by
    rw [hdT']
    split
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · trivial
      · exact Poly.defined_formalD dT c hc
    · exact Poly.defined_formalD dT
  have mdT : Poly.model k dT' = (if atX then X else 1) * derivative (Poly.model k T) := by
    rw [hdT']
    split
    · rw [Poly.model_cons, Poly.model_formalD, Term.value_const]
      simp
    · rw [Poly.model_formalD, one_mul]
  obtain ⟨dg, -, -, bez, gT, gD⟩ := Poly.gcd_spec dT ddT
  obtain ⟨mG, dG, nrmG, -⟩ := Poly.trim_spec (Poly.defined_norm dg)
  obtain ⟨G, hG⟩ : ∃ G, G = Poly.trim (Poly.norm (Poly.gcd T dT').1) := ⟨_, rfl⟩
  rw [← hG] at mG dG nrmG
  rw [Poly.model_norm dg] at mG
  rw [← mG] at bez gT gD
  have Gn : Poly.model k G ≠ 0 := fun z => Tn (by
    obtain ⟨q, hq⟩ := gT
    rw [hq, z, zero_mul])
  have nG : Poly.Normal k G := nrmG.resolve_left fun h => Gn (by rw [h, Poly.model_nil])
  have dq := (Poly.rem_spec dT dG nG).2.1
  have eT := Poly.quot_of_dvd dT dG nG gT
  obtain ⟨mTs, dTs, nrmTs, -⟩ := Poly.trim_spec (Poly.defined_norm dq)
  obtain ⟨Ts, hTs⟩ : ∃ Ts, Ts = Poly.trim (Poly.norm (Poly.quot T G)) := ⟨_, rfl⟩
  rw [← hTs] at mTs dTs nrmTs
  rw [Poly.model_norm dq] at mTs
  rw [← mTs] at eT
  have Tsn : Poly.model k Ts ≠ 0 := fun z => Tn (by rw [eT, z, mul_zero])
  have nTs : Poly.Normal k Ts := nrmTs.resolve_left fun h => Tsn (by rw [h, Poly.model_nil])
  have run : parts atX ws = ((Poly.commonDen ws).1.map fun W => Poly.rem W G,
      (Poly.commonDen ws).1.map fun W => Poly.quot (Poly.quot W G) Ts) := by
    rw [hTs, hG, hdT', hT]
    rfl
  rw [run]
  have first (W : Poly n) (hW : W ∈ (Poly.commonDen ws).1) := Poly.rem_spec (dW0 W hW) dG nG
  have second (W : Poly n) (hW : W ∈ (Poly.commonDen ws).1) :=
    Poly.rem_spec (first W hW).2.1 dTs nTs
  refine ⟨?_, ?_, by simp [len0], fun α S => ?_⟩
  · intro R hR
    obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hR
    exact (first W hW).2.2.1
  · intro A hA
    obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hA
    exact (second W hW).2.1
  have eW := pcombK_decomp (Poly.model k G) (fun W => Poly.quot W G) (fun W => Poly.rem W G)
    (Poly.commonDen ws).1 α fun W hW => (first W hW).1
  have dR := degree_pcombK_lt (d := (Poly.model k G).degree)
    (bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr Gn)) (fun W => Poly.rem W G) (Poly.commonDen ws).1 α
    fun W hW => Poly.degree_model_lt nG (first W hW).2.2.2
  have eQ := pcombK_decomp (Poly.model k Ts) (fun Q => Poly.quot Q Ts) (fun Q => Poly.rem Q Ts)
    ((Poly.commonDen ws).1.map fun W => Poly.quot W G) α (by
      intro Q hQ
      obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hQ
      exact (second W hW).1)
  have dN := degree_pcombK_lt (d := (Poly.model k Ts).degree)
    (bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr Tsn)) (fun Q => Poly.rem Q Ts)
    ((Poly.commonDen ws).1.map fun W => Poly.quot W G) α (by
      intro Q hQ
      obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hQ
      exact Poly.degree_model_lt nTs (second W hW).2.2.2)
  rw [List.map_map] at eQ
  rw [comb0 α, ← mT]
  refine rel_iff Tn eT ?_ eW dR eQ dN S
  rw [mdT] at bez gD
  cases atX with
  | false =>
    simp only [Bool.false_eq_true, ite_false, one_mul, false_imp_iff, and_true] at bez gD ⊢
    exact simple_div_iff Tn eT bez gD _
  | true =>
    simp only [ite_true, true_imp_iff] at bez gD ⊢
    exact simple_integral_div_iff Tn eT bez gD _

/-- The rows of one step hold for `α`, and the combination of the constant terms lies in
`S`, exactly when the combination of the terms has at most simple poles, no pole at the
generator when `atX` is set, and a constant term in `S`. -/
theorem stepRows_spec (atX : Bool) {ws : List (Term (n + 1))}
    (hw : ∀ w ∈ ws, Term.InDomain k w) :
    (∀ h ∈ (stepRows atX ws).2, Term.InDomain k h) ∧
      (stepRows atX ws).2.length = ws.length ∧
      ∀ (α : List k) (S : K k n → Prop),
        ((Simple (linComb α ws) ∧ (atX = true → Integral X (linComb α ws))) ∧
          ∃ c, S c ∧ Proper (linComb α ws - RatFunc.C c)) ↔
        ((∀ row ∈ (stepRows atX ws).1, Linear.dotK row α = 0) ∧
          S (linComb α (stepRows atX ws).2)) := by
  obtain ⟨dR, dA, len, iff⟩ := parts_spec atX hw
  obtain ⟨pr, hpr⟩ : ∃ pr, pr = parts atX ws := ⟨_, rfl⟩
  rw [← hpr] at dR dA len iff
  have run : stepRows atX ws = (rowsOf (pr.1.map Poly.toTerm) ++
      rowsOf (pr.2.map fun A => Poly.toTerm A.tail), pr.2.map fun A => Poly.coeff A 0) := by
    rw [hpr]
    rfl
  rw [run]
  have d1 : ∀ e ∈ pr.1.map Poly.toTerm, Term.InDomain k e := by
    intro e he
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp he
    exact Poly.inDomain_toTerm (dR R hR)
  have d2 : ∀ e ∈ pr.2.map fun A => Poly.toTerm A.tail, Term.InDomain k e := by
    intro e he
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp he
    exact Poly.inDomain_toTerm (Poly.defined_tail (dA A hA))
  refine ⟨?_, by simp [len], fun α S => ?_⟩
  · intro h hh
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hh
    exact Poly.defined_coeff (dA A hA) 0
  rw [iff α S]
  have r1 : (∀ row ∈ rowsOf (pr.1.map Poly.toTerm), Linear.dotK row α = 0) ↔
      pcombK α pr.1 = 0 := by
    rw [rowsOf_spec d1 α, linComb_toTerm,
      map_eq_zero_iff _ (RatFunc.algebraMap_injective (K k n))]
  have r2 : (∀ row ∈ rowsOf (pr.2.map fun A => Poly.toTerm A.tail), Linear.dotK row α = 0) ↔
      pcombK α (pr.2.map List.tail) = 0 := by
    have e : (pr.2.map fun A => Poly.toTerm A.tail) = (pr.2.map List.tail).map Poly.toTerm := by
      rw [List.map_map]
      rfl
    rw [rowsOf_spec d2 α, e, linComb_toTerm,
      map_eq_zero_iff _ (RatFunc.algebraMap_injective (K k n))]
  simp only [List.forall_mem_append, r1, r2, pcombK_eq_C_iff]
  constructor
  · rintro ⟨h1, c, sc, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3 ▸ sc⟩
  · rintro ⟨⟨h1, h2⟩, sc⟩
    exact ⟨h1, _, sc, h2, rfl⟩

end Rel

/-! ### The linear system -/

/-- A combination with constant coefficients lies in the space exactly when the coefficients
solve the linear system over the rationals. -/
theorem relRows_spec : ∀ {n : ℕ} (t : Tower n), t.Admissible k → ∀ {ws : List (Term n)},
    (∀ w ∈ ws, Term.InDomain k w) → ∀ α : List k, α.length = ws.length →
    (Tower.Rel k t (linComb α ws) ↔ ∀ row ∈ relRows t ws, Linear.dotK row α = 0) := by
  intro n t
  induction t with
  | const =>
    intro _ ws hw α _
    rw [Tower.rel_const]
    exact (rowsOf_spec hw α).symm
  | @prim n t b ih =>
    intro ht ws hw α hα
    obtain ⟨dh, len, iff⟩ := Rel.stepRows_spec false hw
    have step := iff α (Tower.Rel k t)
    simp only [Bool.false_eq_true, false_imp_iff, and_true] at step
    rw [Tower.rel_prim, step, ih ht.1 dh α (by rw [len, hα])]
    change _ ↔ ∀ row ∈ (Rel.stepRows false ws).1 ++ relRows t (Rel.stepRows false ws).2, _
    simp only [List.forall_mem_append]
  | @exp n t u ih =>
    intro ht ws hw α hα
    obtain ⟨dh, len, iff⟩ := Rel.stepRows_spec true hw
    have step := iff α fun c' => ∃ (y₀ : K k n) (c : k),
      Tower.Rel k t y₀ ∧ c' = y₀ + constHom k n c * t.der k (Term.value k u)
    have reshuffle : (Simple (linComb α ws) ∧ Integral X (linComb α ws) ∧
        ∃ (y₀ : K k n) (c : k), Tower.Rel k t y₀ ∧
          Proper (linComb α ws - RatFunc.C (y₀ + constHom k n c * t.der k (Term.value k u)))) ↔
        ((Simple (linComb α ws) ∧ (true = true → Integral X (linComb α ws))) ∧
          ∃ c' : K k n, (∃ (y₀ : K k n) (c : k),
            Tower.Rel k t y₀ ∧ c' = y₀ + constHom k n c * t.der k (Term.value k u)) ∧
            Proper (linComb α ws - RatFunc.C c')) := by
      constructor
      · rintro ⟨s, i, y₀, c, r, p⟩
        exact ⟨⟨s, fun _ => i⟩, _, ⟨y₀, c, r, rfl⟩, p⟩
      · rintro ⟨⟨s, i⟩, c', ⟨y₀, c, r, rfl⟩, p⟩
        exact ⟨s, i rfl, y₀, c, r, p⟩
    have de : Term.InDomain k (t.D u) := Tower.inDomain_D ht.1 ht.2.1
    have dh' : ∀ h ∈ (Rel.stepRows true ws).2 ++ [t.D u], Term.InDomain k h := by
      intro h hh
      rcases List.mem_append.mp hh with h1 | h1
      · exact dh h h1
      · rw [List.mem_singleton.mp h1]
        exact de
    have single (c : k) : linComb [c] [t.D u] = constHom k n c * t.der k (Term.value k u) := by
      rw [linComb_cons, linComb_nil_left, add_zero, Tower.der_value]
    have low_iff (c : k) := ih ht.1 dh' (α ++ [c]) (by simp [len, hα])
    have S_iff : (∃ (y₀ : K k n) (c : k), Tower.Rel k t y₀ ∧
        linComb α (Rel.stepRows true ws).2 =
          y₀ + constHom k n c * t.der k (Term.value k u)) ↔
        ∀ row ∈ Linear.eliminate ws.length
          (relRows t ((Rel.stepRows true ws).2 ++ [t.D u])), Linear.dotK row α = 0 := by
      rw [Linear.eliminate_spec _ hα]
      constructor
      · rintro ⟨y₀, c, r, e⟩
        refine ⟨-c, (low_iff (-c)).mp ?_⟩
        rw [linComb_append (by rw [len, hα]), single, e, map_neg,
          show y₀ + constHom k n c * t.der k (Term.value k u) +
            -constHom k n c * t.der k (Term.value k u) = y₀ by ring]
        exact r
      · rintro ⟨c, H⟩
        have r := (low_iff c).mpr H
        rw [linComb_append (by rw [len, hα]), single] at r
        exact ⟨_, -c, r, by rw [map_neg]; ring⟩
    rw [Tower.rel_exp, reshuffle, step, S_iff]
    change _ ↔ ∀ row ∈ (Rel.stepRows true ws).1 ++ Linear.eliminate ws.length
      (relRows t ((Rel.stepRows true ws).2 ++ [t.D u])), _
    simp only [List.forall_mem_append]

end SympyProofs.Calculus.Risch
