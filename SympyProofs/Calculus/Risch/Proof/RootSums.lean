module

public import SympyProofs.Calculus.Risch.Proof.ResidueDefs
public import SympyProofs.Calculus.Risch.Proof.Answer
public import SympyProofs.Calculus.Risch.Proof.ConstRoots
public import SympyProofs.Calculus.Risch.Proof.Deriv
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The pieces of the residue step as sums of logarithms. A polynomial in the root variable,
written as a term one level up, takes at each element of the field the value of the
polynomial there. A piece `(m, g)` of the Euclidean algorithm becomes the sum over the
constant roots `c` of `m` of `c log g(c)`, and its derivative is the sum of `c g(c)′ / g(c)`.
Over an algebraically closed constant field, a divisor of a squarefree polynomial with
constant coefficients has as many constant roots as its degree, and their sum is read off
its two highest coefficients. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial

noncomputable local instance intAlgebraRootSums {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

/-! ### The arithmetic on terms, at arbitrary values of the generators -/

namespace Coeff

variable {n : ℕ} {F : Type*} [Field F]

/-- A negation evaluates to the negative. -/
theorem eval_neg (g : Fin n → F) (a : Term n) : (neg a).eval g = -a.eval g := by
  fun_cases neg a <;> simp [Term.eval]

/-- A sum evaluates to the sum. -/
theorem eval_add [CharZero F] (g : Fin n → F) (a b : Term n) :
    (add a b).eval g = a.eval g + b.eval g := by
  fun_cases add a b <;> simp_all [Term.eval]

/-- A product evaluates to the product. -/
theorem eval_mul [CharZero F] (g : Fin n → F) (a b : Term n) :
    (mul a b).eval g = a.eval g * b.eval g := by
  fun_cases mul a b <;> simp_all [Term.eval]

/-- The negation of a defined term is defined. -/
theorem defined_neg {g : Fin n → F} {a : Term n} (ha : a.Defined g) : (neg a).Defined g := by
  fun_cases neg a <;> first | exact trivial | exact ha

/-- The sum of defined terms is defined. -/
theorem defined_add {g : Fin n → F} {a b : Term n} (ha : a.Defined g) (hb : b.Defined g) :
    (add a b).Defined g := by
  fun_cases add a b <;> first | exact trivial | exact ha | exact hb | exact ⟨ha, hb⟩

/-- The product of defined terms is defined. -/
theorem defined_mul {g : Fin n → F} {a b : Term n} (ha : a.Defined g) (hb : b.Defined g) :
    (mul a b).Defined g := by
  fun_cases mul a b <;> first | exact trivial | exact ha | exact hb | exact ⟨ha, hb⟩

end Coeff

namespace Residue

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

/-! ### A polynomial in the root as a term -/

/-- The term of a coefficient list, with the element `x` for the newest generator, has the
value of the polynomial at `x`. -/
theorem eval_toTerm (x : K k n) (p : Poly n) :
    (Poly.toTerm p).eval (Fin.lastCases x (gens k n)) = (Poly.model k p).eval x := by
  induction p with
  | nil => simp [Poly.toTerm, Term.eval, Poly.model_nil]
  | cons a as ih =>
    rw [Poly.toTerm, Coeff.eval_add, Coeff.eval_mul, Term.eval_weaken, ih, Poly.model_cons]
    simp [Term.eval, Term.value]

/-- The term of a defined coefficient list is defined, whatever element stands for the
newest generator. -/
theorem defined_toTerm (x : K k n) {p : Poly n} (hp : Poly.Defined k p) :
    (Poly.toTerm p).Defined (Fin.lastCases x (gens k n)) := by
  induction p with
  | nil => trivial
  | cons a as ih =>
    exact Coeff.defined_add
      ((Term.defined_weaken (gens k n) x a).mpr (Poly.defined_cons.mp hp).1)
      (Coeff.defined_mul trivial (ih (Poly.defined_cons.mp hp).2))

/-! ### The inputs of the Euclidean algorithm -/

/-- A constant polynomial in the root has the value of its coefficient. -/
theorem zeval_singleton (c : k) (a : Term n) : zeval k c [a] = Term.value k a := by
  simp [zeval, Poly.model_cons, Poly.model_nil]

/-- The polynomial `a + e z` in the root has the value `a + c e` at `c`. -/
theorem zeval_pair (c : k) (a e : Term n) :
    zeval k c [a, e] = Term.value k a + constHom k n c * Term.value k e := by
  simp only [zeval, Poly.model_cons, Poly.model_nil, mul_zero, add_zero, eval_add, eval_mul,
    eval_C, eval_X]

/-- A polynomial in the generator, with coefficients that do not depend on the root, denotes
itself at every constant. -/
theorem bmodel_const (D : Poly n) (c : k) :
    bmodel k c (D.map fun d => [d]) = Poly.model k D := by
  induction D with
  | nil => rfl
  | cons d D ih => rw [List.map_cons, bmodel_cons, ih, zeval_singleton, Poly.model_cons]

/-- A defined polynomial in the generator is defined as a polynomial with coefficients in the
root. -/
theorem bdefined_const {D : Poly n} (hD : Poly.Defined k D) :
    BDefined k (D.map fun d => [d]) := by
  intro q hq
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  exact Poly.defined_cons.mpr ⟨hD d hd, Poly.defined_nil⟩

/-- `shifted A E` denotes `A - c E` at the constant `c`. -/
theorem bmodel_shifted (A E : Poly n) (c : k) :
    bmodel k c (shifted A E) = Poly.model k A - C (constHom k n c) * Poly.model k E := by
  fun_induction shifted A E with
  | case1 E =>
    induction E with
    | nil => simp [bmodel_nil, Poly.model_nil]
    | cons e E ih =>
      rw [List.map_cons, bmodel_cons, ih, zeval_pair, Coeff.value_neg, Poly.model_cons,
        Poly.value_zero, Poly.model_nil]
      simp only [map_add, map_mul, map_neg, map_zero]
      ring
  | case2 A _ =>
    rw [bmodel_const, Poly.model_nil, mul_zero, sub_zero]
  | case3 a A e E ih =>
    rw [bmodel_cons, ih, zeval_pair, Coeff.value_neg, Poly.model_cons, Poly.model_cons]
    simp only [map_add, map_mul, map_neg]
    ring

/-- `shifted A E` is defined when `A` and `E` are. -/
theorem bdefined_shifted {A E : Poly n} (hA : Poly.Defined k A) (hE : Poly.Defined k E) :
    BDefined k (shifted A E) := by
  fun_induction shifted A E with
  | case1 E =>
    intro q hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
    exact Poly.defined_cons.mpr
      ⟨trivial, Poly.defined_cons.mpr ⟨Coeff.inDomain_neg (hE e he), Poly.defined_nil⟩⟩
  | case2 A _ => exact bdefined_const hA
  | case3 a A e E ih =>
    exact bdefined_cons.mpr
      ⟨Poly.defined_cons.mpr ⟨(Poly.defined_cons.mp hA).1, Poly.defined_cons.mpr
          ⟨Coeff.inDomain_neg (Poly.defined_cons.mp hE).1, Poly.defined_nil⟩⟩,
        ih (Poly.defined_cons.mp hA).2 (Poly.defined_cons.mp hE).2⟩

/-! ### A piece as a sum of logarithms -/

/-- The renumbered generators of the field below take, at the root `c`, the values they have
below. -/
private theorem env_rename (c : k) :
    (fun i => RootSum.env k (n := n + 1) c
        ((Fin.lastCases (Fin.last (n + 1)) fun j => j.castSucc.castSucc :
          Fin (n + 1) → Fin (n + 2)) i)) =
      fun i => (RatFunc.C : K k n →+* K k (n + 1)) (RootSum.env k c i) :=
  funext fun i => RootSum.env_weaken c i

/-- The generator of the tower keeps its value when a root is adjoined to the generators. -/
private theorem env_gen (c : k) :
    RootSum.env k (n := n + 1) c (Fin.last n).castSucc = (RatFunc.X : RatFunc (K k n)) := by
  simp [RootSum.env, gens]

/-- A coefficient, as a term in the root, has at the root `c` its value at `c`. -/
private theorem eval_zterm (c : k) (q : Poly n) :
    ((zterm q).rename (Fin.lastCases (Fin.last (n + 1)) fun i => i.castSucc.castSucc)).eval
        (RootSum.env k (n := n + 1) c) =
      (RatFunc.C : K k n →+* K k (n + 1)) (zeval k c q) := by
  rw [Term.eval_rename, env_rename, ← Term.eval_map]
  exact congrArg _ (eval_toTerm (constHom k n c) q)

/-- A defined coefficient, as a term in the root, is defined at every root. -/
private theorem defined_zterm (c : k) {q : Poly n} (hq : Poly.Defined k q) :
    ((zterm q).rename (Fin.lastCases (Fin.last (n + 1)) fun i => i.castSucc.castSucc)).Defined
      (RootSum.env k (n := n + 1) c) := by
  rw [Term.defined_rename, env_rename, Term.defined_map]
  exact defined_toTerm (constHom k n c) hq

/-- The modulus of the sum of logarithms of a piece is not zero. -/
theorem toRootSum_modulus_ne_zero {pc : Poly n × BPoly n} (nm : Poly.Normal k pc.1) :
    Poly.model k (toRootSum pc).modulus ≠ 0 := by
  change Poly.model k (pc.1.map Term.weaken) ≠ 0
  rw [Poly.model_map_weaken]
  exact (Polynomial.map_ne_zero_iff RatFunc.C_injective).mpr nm.model_ne_zero

/-- The sum of logarithms of a piece runs over the constant roots of its modulus. -/
theorem toRootSum_roots {pc : Poly n × BPoly n} (nm : Poly.Normal k pc.1) (c : k) :
    c ∈ (toRootSum pc).roots k ↔ IsRootOf k pc.1 c := by
  rw [RootSum.mem_roots (toRootSum_modulus_ne_zero nm)]
  change (Poly.model k (pc.1.map Term.weaken)).IsRoot _ ↔ _
  rw [Poly.model_map_weaken, constHom_succ, IsRoot.def, eval_map_apply,
    map_eq_zero_iff _ RatFunc.C_injective]
  rfl

/-- The argument of the logarithm at the constant `c` is the polynomial in the generator that
the piece denotes at `c`. -/
theorem toRootSum_argAt {pc : Poly n × BPoly n} (c : k) :
    (toRootSum pc).argAt k c = algebraMap (K k n)[X] (RatFunc (K k n)) (bmodel k c pc.2) := by
  obtain ⟨m, g⟩ := pc
  change Term.eval (RootSum.env k (n := n + 1) c) (g.foldr _ _) = _
  induction g with
  | nil => simp [Term.eval, bmodel_nil]
  | cons q qs ih =>
    rw [List.foldr_cons, Term.eval, Term.eval, Term.eval, ih, eval_zterm, env_gen, bmodel_cons,
      map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

/-- The argument of the logarithm of a piece with defined coefficients is defined at every
constant. -/
theorem toRootSum_defined {pc : Poly n × BPoly n} (hd : BDefined k pc.2) (c : k) :
    (toRootSum pc).arg.Defined (RootSum.env k c) := by
  obtain ⟨m, g⟩ := pc
  change Term.Defined (RootSum.env k (n := n + 1) c) (g.foldr _ _)
  induction g with
  | nil => trivial
  | cons q qs ih =>
    exact ⟨defined_zterm c (bdefined_cons.mp hd).1, trivial, ih (bdefined_cons.mp hd).2⟩

/-- The sum of logarithms of a piece is regular when its modulus is not zero, its
coefficients are defined, and the polynomial it denotes at each root is not zero. -/
theorem toRootSum_regular {pc : Poly n × BPoly n} (nm : Poly.Normal k pc.1)
    (hd : BDefined k pc.2) (nz : ∀ c : k, IsRootOf k pc.1 c → bmodel k c pc.2 ≠ 0) :
    (toRootSum pc).Regular k := by
  refine ⟨toRootSum_modulus_ne_zero nm, fun c hc => ⟨toRootSum_defined hd c, ?_⟩⟩
  rw [toRootSum_argAt]
  exact RatFunc.algebraMap_ne_zero (nz c ((toRootSum_roots nm c).mp hc))

/-- The derivative of the sum of logarithms of a piece: for each root `c`, the constant `c`
times the logarithmic derivative of the polynomial that the piece denotes at `c`. -/
theorem toRootSum_deriv (t : Tower (n + 1)) (pc : Poly n × BPoly n) :
    (toRootSum pc).deriv k t = ∑ c ∈ (toRootSum pc).roots k,
      RatFunc.C (constHom k n c) *
        (algebraMap (K k n)[X] (RatFunc (K k n)) (Tower.polyDer k t (bmodel k c pc.2)) /
          algebraMap (K k n)[X] (RatFunc (K k n)) (bmodel k c pc.2)) := by
  rw [RootSum.deriv]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [toRootSum_argAt, Tower.der_algebraMap, constHom_succ]

/-! ### The constant roots of a polynomial -/

open Classical in
/-- The constants that are roots of a polynomial over the field. -/
noncomputable def rootSet (m : (K k n)[X]) : Finset k :=
  m.roots.toFinset.preimage (constHom k n) (constHom_injective k n).injOn

/-- A constant is in the root set of a nonzero polynomial exactly when it is a root. -/
theorem mem_rootSet {m : (K k n)[X]} (hm : m ≠ 0) (c : k) :
    c ∈ rootSet m ↔ m.IsRoot (constHom k n c) := by
  classical
  rw [rootSet, Finset.mem_preimage, Multiset.mem_toFinset, Polynomial.mem_roots hm]

/-- A sum of logarithms runs over the root set of its modulus. -/
theorem roots_eq_rootSet (s : RootSum n) : s.roots k = rootSet (Poly.model k s.modulus) := rfl

/-- The sum of logarithms of a piece runs over the root set of the modulus of the piece. -/
theorem toRootSum_roots_eq {pc : Poly n × BPoly n} (nm : Poly.Normal k pc.1) :
    (toRootSum pc).roots k = rootSet (Poly.model k pc.1) := by
  ext c
  rw [toRootSum_roots nm, mem_rootSet nm.model_ne_zero]
  rfl

/-- The constant roots of a divisor of the image of a polynomial with constant coefficients
are roots of that polynomial. -/
theorem rootSet_subset {r : k[X]} {m : (K k n)[X]} (hm : m ≠ 0)
    (dvd : m ∣ r.map (constHom k n)) : ∀ c ∈ rootSet m, r.IsRoot c := by
  intro c hc
  have h := ((mem_rootSet hm c).mp hc).dvd dvd
  rw [IsRoot.def, eval_map_apply] at h
  exact (map_eq_zero_iff _ (constHom_injective k n)).mp h

open Classical in
/-- The constant roots of a product are those of its factors. -/
theorem rootSet_mul {a b : (K k n)[X]} (hab : a * b ≠ 0) :
    rootSet (a * b) = rootSet a ∪ rootSet b := by
  classical
  ext c
  rw [Finset.mem_union, mem_rootSet hab, mem_rootSet (left_ne_zero_of_mul hab),
    mem_rootSet (right_ne_zero_of_mul hab), root_mul]

/-- Two polynomials whose product divides the image of a squarefree polynomial with constant
coefficients have no constant root in common. -/
theorem rootSet_mul_disjoint {r : k[X]} (sq : Squarefree r) {a b : (K k n)[X]}
    (dvd : a * b ∣ r.map (constHom k n)) : Disjoint (rootSet a) (rootSet b) := by
  have rm0 : r.map (constHom k n) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (constHom_injective k n)).mpr sq.ne_zero
  have ab0 : a * b ≠ 0 := fun z => rm0 (zero_dvd_iff.mp (z ▸ dvd))
  have sqm : Squarefree (r.map (constHom k n)) :=
    ((PerfectField.separable_iff_squarefree.mpr sq).map).squarefree
  rw [Finset.disjoint_left]
  intro c ha hb
  have da := dvd_iff_isRoot.mpr ((mem_rootSet (left_ne_zero_of_mul ab0) c).mp ha)
  have db := dvd_iff_isRoot.mpr ((mem_rootSet (right_ne_zero_of_mul ab0) c).mp hb)
  exact not_isUnit_X_sub_C _ (sqm _ ((mul_dvd_mul da db).trans dvd))

section AlgClosed

variable [IsAlgClosed k]

/-- A divisor of the image of a squarefree polynomial with constant coefficients
splits, with distinct roots, all of them constants. -/
theorem splits_of_dvd_map {r : k[X]} (sq : Squarefree r) {m : (K k n)[X]}
    (dvd : m ∣ r.map (constHom k n)) :
    m.Splits ∧ m.roots.Nodup ∧ ∀ x ∈ m.roots, ∃ c : k, constHom k n c = x := by
  have rs : r.Splits := IsAlgClosed.splits r
  have rm0 : r.map (constHom k n) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (constHom_injective k n)).mpr sq.ne_zero
  have nd : r.roots.Nodup := nodup_roots (PerfectField.separable_iff_squarefree.mpr sq)
  have le : m.roots ≤ r.roots.map (constHom k n) := by
    rw [← rs.roots_map]
    exact roots.le_of_dvd rm0 dvd
  refine ⟨(rs.map _).of_dvd rm0 dvd,
    Multiset.nodup_of_le le (nd.map (constHom_injective k n)), fun x hx => ?_⟩
  obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_le le hx)
  exact ⟨c, rfl⟩

open Classical in
/-- The roots of a nonzero divisor of the image of a squarefree polynomial with constant
coefficients are the images of its constant roots. -/
theorem image_rootSet {r : k[X]} (sq : Squarefree r) {m : (K k n)[X]} (hm : m ≠ 0)
    (dvd : m ∣ r.map (constHom k n)) :
    (rootSet m).image (constHom k n) = m.roots.toFinset := by
  ext x
  rw [Finset.mem_image, Multiset.mem_toFinset]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (mem_roots hm).mpr ((mem_rootSet hm c).mp hc)
  · intro hx
    obtain ⟨c, rfl⟩ := (splits_of_dvd_map sq dvd).2.2 x hx
    exact ⟨c, (mem_rootSet hm c).mpr ((mem_roots hm).mp hx), rfl⟩

/-- A nonzero divisor of the image of a squarefree polynomial with constant coefficients has
as many constant roots as its degree. -/
theorem card_rootSet {r : k[X]} (sq : Squarefree r) {m : (K k n)[X]} (hm : m ≠ 0)
    (dvd : m ∣ r.map (constHom k n)) : (rootSet m).card = m.natDegree := by
  classical
  obtain ⟨sp, nd, -⟩ := splits_of_dvd_map sq dvd
  rw [← Finset.card_image_of_injective _ (constHom_injective k n), image_rootSet sq hm dvd,
    Multiset.toFinset_card_of_nodup nd, sp.natDegree_eq_card_roots]

/-- The sum of the constant roots of a divisor of positive degree of the image of a
squarefree polynomial with constant coefficients is minus the quotient of its second highest
coefficient by its leading coefficient. -/
theorem sum_rootSet {r : k[X]} (sq : Squarefree r) {m : (K k n)[X]} (hm : m ≠ 0)
    (dvd : m ∣ r.map (constHom k n)) (pos : 0 < m.natDegree) :
    constHom k n (∑ c ∈ rootSet m, c) = -(m.coeff (m.natDegree - 1) / m.leadingCoeff) := by
  classical
  obtain ⟨sp, nd, -⟩ := splits_of_dvd_map sq dvd
  have lc : m.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hm
  have sum : constHom k n (∑ c ∈ rootSet m, c) = m.roots.sum := by
    rw [map_sum, ← Finset.sum_image (f := fun x => x) (g := constHom k n)
      fun _ _ _ _ h => constHom_injective k n h, image_rootSet sq hm dvd,
      Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr nd,
      Multiset.map_id']
  have next := sp.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [nextCoeff_of_natDegree_pos pos] at next
  rw [sum, next]
  field_simp

end AlgClosed

end Residue

end SympyProofs.Calculus.Risch
