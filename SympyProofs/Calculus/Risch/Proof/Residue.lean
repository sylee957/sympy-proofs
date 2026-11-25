module

public import SympyProofs.Calculus.Risch.Algebra.LogPart
public import SympyProofs.Calculus.Risch.Proof.GcdMod
public import SympyProofs.Calculus.Risch.Proof.RootSums
public import SympyProofs.Calculus.Risch.Proof.ResidueCriterion
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The logarithmic part of a fraction `A / D` in lowest terms, with squarefree denominator,
normal prime factors and `deg A < deg D`, over an algebraically closed constant field.

For a constant `c` let `G c` be the greatest common divisor of `A - c D′` and `D` with
leading coefficient one. The pieces computed by `logPart` list the `G c` for the constant
roots `c` of the resultant: each root lies in exactly one piece, and the polynomial of the
piece takes the value `G c` there. So the degree test of `logPart` compares the sum of the
degrees of the `G c` with the degree of `D`.

* `logPart_sound`: when the test succeeds, `A / D` is the derivative of the sums of
  logarithms plus the constant returned.
* `logPart_complete`: when it fails, `A / D + L` has no elementary integral, for every `L`
  without poles at the prime factors of `D`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial

noncomputable local instance intAlgebraResidue {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

local notation "ι" => algebraMap (K k n)[X] (RatFunc (K k n))

/-- The derivative of a polynomial `G` with leading coefficient one differs from
`(deg G) · twist · G` by a polynomial of smaller degree. -/
theorem Tower.degree_polyDer_monic (t : Tower (n + 1)) {G : (K k n)[X]} (hG : G.Monic) :
    (Tower.polyDer k t G - C ((G.natDegree : K k n) * Term.value k t.twist) * G).degree <
      G.degree := by
  rw [degree_eq_natDegree hG.ne_zero, degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_sub, coeff_C_mul, Tower.coeff_polyDer]
  rcases Nat.eq_or_lt_of_le hm with rfl | hlt
  · rw [hG.coeff_natDegree, coeff_natDegree_succ_eq_zero, Derivation.map_one_eq_zero]
    ring
  · rw [coeff_eq_zero_of_natDegree_lt hlt, coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    ring

namespace Residue

/-! ### Sums over lists -/

theorem sum_filter_of_zero {α M : Type*} [AddCommMonoid M] (p : α → Bool) (f : α → M) :
    ∀ l : List α, (∀ x ∈ l, p x = false → f x = 0) →
      ((l.filter p).map f).sum = (l.map f).sum
  | [], _ => rfl
  | a :: l, h => by
    have ih := sum_filter_of_zero p f l fun x hx => h x (List.mem_cons_of_mem _ hx)
    cases hp : p a
    · rw [List.filter_cons_of_neg (by simp [hp]), ih, List.map_cons, List.sum_cons,
        h a List.mem_cons_self hp, zero_add]
    · rw [List.filter_cons_of_pos hp, List.map_cons, List.sum_cons, ih, List.map_cons,
        List.sum_cons]

theorem foldl_add_eq_sum {α : Type*} (f : α → ℕ) :
    ∀ (l : List α) (a : ℕ), l.foldl (fun s x => s + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add_eq_sum f l, List.map_cons, List.sum_cons, add_assoc]

/-- A sum of terms built with `Coeff.add` is defined and denotes the sum of the values. -/
theorem foldl_coeff_add {α : Type} (g : α → Term n) :
    ∀ (l : List α) (a : Term n), Term.InDomain k a → (∀ x ∈ l, Term.InDomain k (g x)) →
      Term.InDomain k (l.foldl (fun s x => Coeff.add s (g x)) a) ∧
        Term.value k (l.foldl (fun s x => Coeff.add s (g x)) a) =
          Term.value k a + (l.map fun x => Term.value k (g x)).sum
  | [], a, ha, _ => ⟨ha, by simp⟩
  | x :: l, a, ha, h => by
    obtain ⟨d, v⟩ := foldl_coeff_add g l (Coeff.add a (g x))
      (Coeff.inDomain_add ha (h x List.mem_cons_self)) fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨d, ?_⟩
    rw [List.foldl_cons, v, Coeff.value_add, List.map_cons, List.sum_cons, add_assoc]

/-! ### Root sets of a product -/

theorem rootSet_one : rootSet (1 : (K k n)[X]) = ∅ :=
  Finset.eq_empty_of_forall_notMem fun c hc => by
    have := (mem_rootSet one_ne_zero c).mp hc
    rw [IsRoot.def, eval_one] at this
    exact one_ne_zero this

theorem rootSet_congr {a b : (K k n)[X]} (ha : a ≠ 0) (h : Associated a b) :
    rootSet a = rootSet b := by
  have hb : b ≠ 0 := h.ne_zero_iff.mp ha
  ext c
  rw [mem_rootSet ha, mem_rootSet hb, ← dvd_iff_isRoot, ← dvd_iff_isRoot]
  exact h.dvd_iff_dvd_right

/-- A sum over the constant roots of a product of factors of a squarefree polynomial with
constant coefficients is the sum of the sums over the roots of the factors. -/
theorem sum_rootSet_list {r0 : k[X]} (sq : Squarefree r0) {M : Type} [AddCommMonoid M]
    (φ : k → M) : ∀ l : List (K k n)[X], l.prod ∣ r0.map (constHom k n) →
      (l.map fun m => ∑ c ∈ rootSet m, φ c).sum = ∑ c ∈ rootSet l.prod, φ c
  | [], _ => by
    rw [List.prod_nil, rootSet_one]
    rfl
  | a :: l, h => by
    rw [List.prod_cons] at h ⊢
    have rm0 : r0.map (constHom k n) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (constHom_injective k n)).mpr sq.ne_zero
    have ab0 : a * l.prod ≠ 0 := fun z => rm0 (zero_dvd_iff.mp (z ▸ h))
    classical
    rw [List.map_cons, List.sum_cons, sum_rootSet_list sq φ l (dvd_of_mul_left_dvd h),
      rootSet_mul ab0, Finset.sum_union (rootSet_mul_disjoint sq h)]

/-! ### The program, with its parts named -/

/-- The residue polynomial, with its rational coefficients as constants of the field. -/
def resMod (t : Tower (n + 1)) (A D : Poly n) : Poly n :=
  (constRoots (Resultant.resPoly A D (Poly.der t D))).map fun c => .const c.evalRat

/-- The pieces of the Euclidean algorithm, before those with constant greatest common
divisor are dropped. -/
def rawPieces (t : Tower (n + 1)) (A D : Poly n) : List (Poly n × BPoly n) :=
  if Nat.ble (resMod t A D).length 1 then []
  else gcdMod (D.length + 1) (resMod t A D) (shifted A (Poly.der t D)) (D.map fun c => [c])

/-- The pieces kept: those whose greatest common divisor is not constant. -/
def keep (piece : Poly n × BPoly n) : Bool := !Nat.ble piece.2.length 1

/-- The sum over the pieces of the degree of the divisor times minus the sum of the roots of
the modulus. -/
def constSum (pieces : List (Poly n × BPoly n)) : Term n :=
  pieces.foldl (fun s piece =>
    Coeff.add s (Coeff.mul (.const ((piece.2.length - 1 : Nat) : Rat))
      (.div (Poly.coeff piece.1 (piece.1.length - 2)) (Poly.lead piece.1)))) (.const 0)

theorem logPart_eq (t : Tower (n + 1)) (A D : Poly n) :
    logPart t A D =
      if Nat.ble D.length 1 then some ([], .const 0)
      else if ((rawPieces t A D).filter keep).foldl
          (fun s piece => s + (piece.1.length - 1) * (piece.2.length - 1)) 0 == D.length - 1 then
        some ((rawPieces t A D).filter keep,
          Coeff.mul (constSum ((rawPieces t A D).filter keep)) t.twist)
      else none := by
  have e : (rawPieces t A D).filter keep =
      if Nat.ble (resMod t A D).length 1 then []
      else (gcdMod (D.length + 1) (resMod t A D) (shifted A (Poly.der t D))
        (D.map fun c => [c])).filter fun piece => !Nat.ble piece.2.length 1 := by
    unfold rawPieces
    split <;> rfl
  rw [e]
  rfl

/-! ### The input conditions and the parts of the denominator -/

/-- The input conditions of the residue step: `A / D` is in lowest terms with `deg A < deg D`,
and `D` is squarefree with normal prime factors. -/
structure Input (k : Type) [Field k] [CharZero k] (t : Tower (n + 1)) (A D : Poly n) :
    Prop where
  ht : t.Admissible k
  dA : Poly.Defined k A
  dD : Poly.Defined k D
  nD : Poly.Normal k D
  squarefree : Squarefree (Poly.model k D)
  normal : ∀ q : (K k n)[X], Prime q → q ∣ Poly.model k D → ¬ q ∣ Tower.polyDer k t q
  cop : IsCoprime (Poly.model k A) (Poly.model k D)
  deg : (Poly.model k A).degree < (Poly.model k D).degree

/-- The part of `D` with residue `c`. -/
noncomputable def resG (k : Type) [Field k] [CharZero k] (t : Tower (n + 1)) (A D : Poly n)
    (c : k) : (K k n)[X] :=
  resGcd (Tower.polyDer k t) (Poly.model k A) (Poly.model k D) (constHom k n c)

variable {t : Tower (n + 1)} {A D : Poly n}

/-- The residue polynomial is defined, written without vanishing leading coefficient, and
the image of a squarefree polynomial over the constants. Its constant roots are the constant
roots of the resultant. -/
theorem resMod_spec (h : Input k t A D) :
    Poly.Defined k (resMod t A D) ∧ Poly.Normal k (resMod t A D) ∧
      (∃ r0 : k[X], Squarefree r0 ∧ Poly.model k (resMod t A D) = r0.map (constHom k n)) ∧
      ∀ c : k, c ∈ rootSet (Poly.model k (resMod t A D)) ↔
        (Poly.model k (Resultant.resPoly A D (Poly.der t D))).IsRoot (constHom k n c) := by
  have dD' := Poly.defined_der h.ht h.dD
  obtain ⟨-, n0, sq, roots⟩ := constRoots_spec (Resultant.defined_resPoly h.dA h.dD dD')
    (Resultant.resPoly_ne_zero A (Poly.der t D) h.dA h.dD dD' h.nD h.cop)
  have nr : Poly.Normal k (resMod t A D) := by
    unfold Poly.Normal
    rw [Poly.value_lead, resMod, model_lift, List.length_map, coeff_map, ← Poly.value_lead]
    exact (map_ne_zero (constHom k n)).mpr n0
  refine ⟨defined_lift _, nr, ⟨_, sq, model_lift _⟩, fun c => ?_⟩
  rw [mem_rootSet nr.model_ne_zero, ← roots c, resMod, model_lift, IsRoot.def, IsRoot.def,
    eval_map_apply]
  exact map_eq_zero_iff _ (constHom_injective k n)

/-- What the pieces say about the parts of `D`: each constant root `c` of the modulus of a
piece is a root of the resultant, the polynomial of the piece is `G c` there, and a sum over
the roots of the resultant is the sum over the pieces of the sums over their roots. -/
structure Cover (k : Type) [Field k] [CharZero k] (t : Tower (n + 1)) (A D : Poly n)
    (out : List (Poly n × BPoly n)) (S : Finset k) : Prop where
  defined : ∀ pc ∈ out, Poly.Defined k pc.1
  normal : ∀ pc ∈ out, Poly.Normal k pc.1
  bdefined : ∀ pc ∈ out, BDefined k pc.2
  length : ∀ pc ∈ out, 2 ≤ pc.1.length
  dvd : ∃ r0 : k[X], Squarefree r0 ∧ ∀ pc ∈ out, Poly.model k pc.1 ∣ r0.map (constHom k n)
  gcd : ∀ pc ∈ out, ∀ c : k, IsRootOf k pc.1 c →
    bmodel k c pc.2 = resG k t A D c ∧ (resG k t A D c).natDegree = pc.2.length - 1
  sum : ∀ (M : Type) [AddCommMonoid M] (φ : k → M),
    (out.map fun pc => ∑ c ∈ rootSet (Poly.model k pc.1), φ c).sum = ∑ c ∈ S, φ c

theorem rawPieces_cover (h : Input k t A D) :
    Cover k t A D (rawPieces t A D) (rootSet (Poly.model k (resMod t A D))) := by
  obtain ⟨dr, nr, ⟨r0, sq, mr⟩, -⟩ := resMod_spec h
  have D0 := h.nD.model_ne_zero
  unfold rawPieces
  split
  · rename_i hle
    refine ⟨by simp, by simp, by simp, by simp, ⟨r0, sq, by simp⟩, by simp, fun M _ φ => ?_⟩
    rw [List.map_nil, List.sum_nil]
    symm
    refine Finset.sum_eq_zero fun c hc => ?_
    exact absurd ((mem_rootSet nr.model_ne_zero c).mp hc)
      (not_isRootOf_of_length_le_one nr (Nat.le_of_ble_eq_true hle) c)
  · rename_i hgt
    have two : 2 ≤ (resMod t A D).length := by
      have : ¬ (resMod t A D).length ≤ 1 := fun hle => hgt (Nat.ble_eq_true_of_le hle)
      omega
    have dD' := Poly.defined_der h.ht h.dD
    have ok := gcdMod_spec (D.length + 1) dr nr (bdefined_shifted h.dA dD')
      (bdefined_const h.dD) (by rw [List.length_map]; omega)
    have len := gcdMod_length (D.length + 1) dr nr (bdefined_shifted h.dA dD')
      (bdefined_const h.dD) two
    refine ⟨fun pc hpc => (ok.defined pc hpc).1, ok.normal, fun pc hpc => (ok.defined pc hpc).2,
      len, ⟨r0, sq, fun pc hpc => ?_⟩, ?_, ?_⟩
    · rw [← mr]
      exact ok.dvd hpc
    · intro pc hpc c hc
      obtain ⟨ga, gb, bez, shape⟩ := ok.gcd pc hpc c hc
      rw [bmodel_shifted, Poly.model_der, bmodel_const] at bez
      rw [bmodel_shifted, Poly.model_der] at ga
      rw [bmodel_const] at gb
      rcases shape with e | ⟨mon, dg⟩
      · rw [e, bmodel_nil, zero_dvd_iff] at gb
        exact absurd gb D0
      · have eq : bmodel k c pc.2 = resG k t A D c := mgcd_unique mon ga gb bez D0
        exact ⟨eq, eq ▸ dg⟩
    · intro M _ φ
      have pd : ((gcdMod (D.length + 1) (resMod t A D) (shifted A (Poly.der t D))
          (D.map fun c => [c])).map fun pc => Poly.model k pc.1).prod ∣
          r0.map (constHom k n) := by
        rw [← mr]
        exact ok.prod.symm.dvd
      have := sum_rootSet_list sq φ _ pd
      rw [List.map_map] at this
      rw [rootSet_congr nr.model_ne_zero ok.prod]
      exact this

/-- A sum over the pieces kept, of a quantity that is a sum over the roots of each piece and
vanishes where the part of `D` is one, is the sum over the roots of the resultant. -/
theorem Cover.sum_filter {out : List (Poly n × BPoly n)} {S : Finset k}
    (cv : Cover k t A D out S) (D0 : Poly.model k D ≠ 0) {M : Type} [AddCommMonoid M]
    (g : Poly n × BPoly n → M) (φ : k → M)
    (hg : ∀ pc ∈ out, g pc = ∑ c ∈ rootSet (Poly.model k pc.1), φ c)
    (hz : ∀ c : k, resG k t A D c = 1 → φ c = 0) :
    ((out.filter keep).map g).sum = ∑ c ∈ S, φ c := by
  rw [sum_filter_of_zero keep g out, List.map_congr_left hg, cv.sum M φ]
  intro pc hpc hk
  rw [hg pc hpc]
  refine Finset.sum_eq_zero fun c hc => hz c ?_
  have hc' := (mem_rootSet (cv.normal pc hpc).model_ne_zero c).mp hc
  obtain ⟨-, dg⟩ := cv.gcd pc hpc c hc'
  have len : pc.2.length ≤ 1 := by
    rw [keep, Bool.not_eq_false'] at hk
    exact Nat.le_of_ble_eq_true hk
  have mon : (resG k t A D c).Monic := mgcd_monic D0
  exact eq_one_of_monic_natDegree_zero mon (by rw [dg]; omega)

section Closed

variable [IsAlgClosed k]

/-- The quantity tested by `logPart` is the sum of the degrees of the parts of `D`. -/
theorem total_eq {out : List (Poly n × BPoly n)} {S : Finset k} (cv : Cover k t A D out S)
    (D0 : Poly.model k D ≠ 0) :
    (out.filter keep).foldl (fun s piece => s + (piece.1.length - 1) * (piece.2.length - 1)) 0 =
      ∑ c ∈ S, (resG k t A D c).natDegree := by
  obtain ⟨r0, sq, dvd⟩ := cv.dvd
  rw [foldl_add_eq_sum, zero_add]
  refine cv.sum_filter D0 _ _ (fun pc hpc => ?_) (fun c hc => by rw [hc, natDegree_one])
  have nz := (cv.normal pc hpc).model_ne_zero
  rw [Finset.sum_congr rfl fun c hc => (cv.gcd pc hpc c ((mem_rootSet nz c).mp hc)).2,
    Finset.sum_const, card_rootSet sq nz (dvd pc hpc), (cv.normal pc hpc).natDegree, smul_eq_mul]

/-- The constant returned by `logPart`, before the factor `twist`. -/
theorem const_eq {out : List (Poly n × BPoly n)} {S : Finset k} (cv : Cover k t A D out S)
    (D0 : Poly.model k D ≠ 0) :
    ((out.filter keep).map fun pc => ((pc.2.length - 1 : ℕ) : K k n) *
      ((Poly.model k pc.1).coeff (pc.1.length - 2) / Term.value k (Poly.lead pc.1))).sum =
      ∑ c ∈ S, -(((resG k t A D c).natDegree : K k n) * constHom k n c) := by
  obtain ⟨r0, sq, dvd⟩ := cv.dvd
  refine cv.sum_filter D0 _ _ (fun pc hpc => ?_)
    (fun c hc => by rw [hc, natDegree_one, Nat.cast_zero, zero_mul, neg_zero])
  have nm := cv.normal pc hpc
  have nz := nm.model_ne_zero
  have len := cv.length pc hpc
  have sr := sum_rootSet sq nz (dvd pc hpc) (by rw [nm.natDegree]; omega)
  rw [nm.natDegree, nm.leadingCoeff, show pc.1.length - 1 - 1 = pc.1.length - 2 from by omega,
    map_sum] at sr
  have e : ∑ c ∈ rootSet (Poly.model k pc.1),
      -(((resG k t A D c).natDegree : K k n) * constHom k n c) =
      ∑ c ∈ rootSet (Poly.model k pc.1),
        -(((pc.2.length - 1 : ℕ) : K k n) * constHom k n c) :=
    Finset.sum_congr rfl fun c hc => by rw [(cv.gcd pc hpc c ((mem_rootSet nz c).mp hc)).2]
  rw [e, Finset.sum_neg_distrib, ← Finset.mul_sum, sr]
  ring

end Closed

/-- The derivative of the sums of logarithms of the pieces kept. -/
theorem deriv_eq {out : List (Poly n × BPoly n)} {S : Finset k} (cv : Cover k t A D out S)
    (D0 : Poly.model k D ≠ 0) :
    ((out.filter keep).map fun pc => (toRootSum pc).deriv k t).sum =
      ∑ c ∈ S, RatFunc.C (constHom k n c) *
        (ι (Tower.polyDer k t (resG k t A D c)) / ι (resG k t A D c)) := by
  refine cv.sum_filter D0 (M := RatFunc (K k n)) _ _ (fun pc hpc => ?_)
    (fun c hc => by rw [hc, Derivation.map_one_eq_zero, map_zero, zero_div, mul_zero])
  have nz := (cv.normal pc hpc).model_ne_zero
  rw [toRootSum_deriv t pc, toRootSum_roots_eq (cv.normal pc hpc)]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [(cv.gcd pc hpc c ((mem_rootSet nz c).mp hc)).1]

/-- The value of the sum of constants. -/
theorem constSum_spec {pieces : List (Poly n × BPoly n)}
    (hd : ∀ pc ∈ pieces, Poly.Defined k pc.1 ∧ Poly.Normal k pc.1) :
    Term.InDomain k (constSum pieces) ∧ Term.value k (constSum pieces) =
      (pieces.map fun pc => ((pc.2.length - 1 : ℕ) : K k n) *
        ((Poly.model k pc.1).coeff (pc.1.length - 2) / Term.value k (Poly.lead pc.1))).sum := by
  obtain ⟨d, v⟩ := foldl_coeff_add (k := k) (fun piece : Poly n × BPoly n =>
    Coeff.mul (.const ((piece.2.length - 1 : Nat) : Rat))
      (.div (Poly.coeff piece.1 (piece.1.length - 2)) (Poly.lead piece.1))) pieces (.const 0)
    trivial (fun pc hpc => Coeff.inDomain_mul trivial
      ⟨Poly.defined_coeff (hd pc hpc).1 _, Poly.defined_lead (hd pc hpc).1, (hd pc hpc).2⟩)
  refine ⟨d, ?_⟩
  rw [constSum, v, Poly.value_zero, zero_add]
  refine congrArg List.sum (List.map_congr_left fun pc _ => ?_)
  rw [Coeff.value_mul, Term.value_const, Rat.cast_natCast]
  change _ * (Term.value k (Poly.coeff pc.1 _) / Term.value k (Poly.lead pc.1)) = _
  rw [Poly.value_coeff]

/-! ### The specification of `logPart` -/

variable [IsAlgClosed k]

/-- The embedding of the constants. -/
noncomputable def constEmb (k : Type) [Field k] [CharZero k] (n : ℕ) : k ↪ K k n :=
  ⟨constHom k n, constHom_injective k n⟩

/-- When the degrees of the parts add up to the degree of `D`, the sums of logarithms of the
pieces kept are regular and `A / D` is their derivative plus the constant. -/
theorem pieces_sound (h : Input k t A D) {out : List (Poly n × BPoly n)} {S : Finset k}
    (cv : Cover k t A D out S)
    (h2 : (out.filter keep).foldl
      (fun s piece => s + (piece.1.length - 1) * (piece.2.length - 1)) 0 = D.length - 1) :
    Term.InDomain k (Coeff.mul (constSum (out.filter keep)) t.twist) ∧
      (∀ pc ∈ out.filter keep, (toRootSum pc).Regular k) ∧
      ι (Poly.model k A) / ι (Poly.model k D) =
        ((out.filter keep).map fun pc => (toRootSum pc).deriv k t).sum +
          RatFunc.C (Term.value k (Coeff.mul (constSum (out.filter keep)) t.twist)) := by
  have D0 := h.nD.model_ne_zero
  have tot := total_eq cv D0
  have sum' : ∑ x ∈ S.map (constEmb k n),
      (resGcd (Tower.polyDer k t) (Poly.model k A) (Poly.model k D) x).natDegree =
      (Poly.model k D).natDegree := by
    rw [Finset.sum_map, h.nD.natDegree, ← h2, tot]
    rfl
  have id := logPart_identity (Tower.polyDer k t) (Term.value k t.twist)
    (fun G hG => t.degree_polyDer_monic hG) h.squarefree h.normal h.deg _ sum'
  rw [Finset.sum_map, Finset.sum_map] at id
  obtain ⟨dQ, vQ⟩ := constSum_spec (k := k) (pieces := out.filter keep)
    fun pc hpc => ⟨cv.defined pc (List.mem_of_mem_filter hpc),
      cv.normal pc (List.mem_of_mem_filter hpc)⟩
  refine ⟨Coeff.inDomain_mul dQ (Tower.inDomain_twist h.ht), fun pc hpc => ?_, ?_⟩
  · have hm := List.mem_of_mem_filter hpc
    refine toRootSum_regular (cv.normal pc hm) (cv.bdefined pc hm) fun c hc => ?_
    rw [(cv.gcd pc hm c hc).1]
    exact (mgcd_monic D0).ne_zero
  · rw [id, deriv_eq cv D0, Coeff.value_mul, vQ, const_eq cv D0, Finset.sum_neg_distrib,
      neg_mul, map_neg, sub_eq_add_neg]
    rfl

/-- When `logPart` returns pieces and a constant, the sums of logarithms are regular and
`A / D` is their derivative plus the constant. -/
theorem logPart_sound (h : Input k t A D) {pieces : List (Poly n × BPoly n)} {Q : Term n}
    (e : logPart t A D = some (pieces, Q)) :
    Term.InDomain k Q ∧ (∀ pc ∈ pieces, (toRootSum pc).Regular k) ∧
      ι (Poly.model k A) / ι (Poly.model k D) =
        (pieces.map fun pc => (toRootSum pc).deriv k t).sum + RatFunc.C (Term.value k Q) := by
  have D0 := h.nD.model_ne_zero
  rw [logPart_eq] at e
  by_cases h1 : Nat.ble D.length 1 = true
  · rw [ite_eq_left h1] at e
    have len : D.length ≤ 1 := Nat.le_of_ble_eq_true h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    have A0 : Poly.model k A = 0 := by
      have := h.deg
      rw [degree_eq_natDegree D0, h.nD.natDegree, show D.length - 1 = 0 by omega,
        Nat.cast_zero] at this
      exact degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp this)
    refine ⟨trivial, by simp, ?_⟩
    rw [A0, map_zero, zero_div, List.map_nil, List.sum_nil, Poly.value_zero, map_zero, add_zero]
  · rw [ite_eq_right h1] at e
    by_cases h2 : (((rawPieces t A D).filter keep).foldl
        (fun s piece => s + (piece.1.length - 1) * (piece.2.length - 1)) 0 == D.length - 1) = true
    · rw [ite_eq_left h2] at e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
      exact pieces_sound h (rawPieces_cover h) (beq_iff_eq.mp h2)
    · rw [ite_eq_right h2] at e
      exact absurd e (by simp)

/-- When `logPart` fails, `A / D + L` has no elementary integral, for every `L` without a
pole at the prime factors of `D`. -/
theorem logPart_complete (h : Input k t A D) {L : RatFunc (K k n)}
    (hL : ∀ p : (K k n)[X], Prime p → p ∣ Poly.model k D → SimplePole.Integral p L)
    (e : logPart t A D = none) :
    ¬ t.Elementary k (ι (Poly.model k A) / ι (Poly.model k D) + L) := by
  intro form
  have D0 := h.nD.model_ne_zero
  have cv := rawPieces_cover h
  have res := t.residue_necessary h.squarefree h.normal hL form
  have sum := degree_sum_of_residues (Tower.polyDer k t) (A := Poly.model k A) h.squarefree
    h.normal ((rootSet (Poly.model k (resMod t A D))).map (constEmb k n))
    (fun p hp hpD => by
      obtain ⟨r, hr⟩ := res p hp hpD
      refine ⟨constHom k n r, Finset.mem_map.mpr ⟨r, ?_, rfl⟩, hr⟩
      rw [(resMod_spec h).2.2.2]
      exact Resultant.root_of_residue A (Poly.der t D) h.dA h.dD (Poly.defined_der h.ht h.dD)
        h.nD hp hpD (constHom k n r)
        (by rw [Poly.model_der]; exact hr))
  rw [Finset.sum_map, h.nD.natDegree] at sum
  have tot : ((rawPieces t A D).filter keep).foldl
      (fun s piece => s + (piece.1.length - 1) * (piece.2.length - 1)) 0 = D.length - 1 :=
    (total_eq cv D0).trans sum
  rw [logPart_eq, tot] at e
  by_cases h1 : Nat.ble D.length 1 = true
  · rw [ite_eq_left h1] at e
    exact absurd e (by simp)
  · rw [ite_eq_right h1, ite_eq_left (beq_self_eq_true _)] at e
    exact absurd e (by simp)

end Residue

end SympyProofs.Calculus.Risch
