module

public import SympyProofs.Calculus.Antiderivative.Extension.Derivation
public import SympyProofs.Calculus.Antiderivative.Extension.Liouville
public import Mathlib.FieldTheory.Differential.Liouville
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Liouville forms over a differential field `K` and over the field of rational functions
`K(θ)` with `θ′ = a θ + b`. An element is in Liouville form when it is a derivative plus a
combination of logarithmic derivatives with constant coefficients.

A Liouville form of a polynomial in `θ` is projected at infinity: its polynomial part gives
one differential equation in `K` for each coefficient, and what remains of the constant term
is a Liouville form in `K`. At an exponential generator the projection at zero, the only
special place, gives the equations for the negative powers of a Laurent polynomial. The
same projection shows that a primitive or exponential generator admits Liouville descent,
and hence so does a finite tower of such generators and algebraic extensions. The notions
themselves are defined in `Liouville.lean`. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Extension.LiouvilleForm

open Polynomial Differential

variable {K : Type*} [Field K]

section Differential

variable [Differential K]

variable [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
variable {a b : K}

/-- Evaluation of the formal affine derivation in the differential rational function field. -/
theorem affineDeriv_map (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C b)
    (p : K[X]) : (algebraMap K[X] (RatFunc K) p)′ =
      algebraMap K[X] (RatFunc K) (affine a b p) := by
  simp only [← RatFunc.aeval_X_left_eq_algebraMap]
  apply deriv_aeval_eq_implicitDeriv
  simpa using dx

end Differential

namespace AtInfinity

/-- Proper fractions, including zero. -/
def Proper (x : RatFunc K) : Prop := x = 0 ∨ x.intDegree < 0

def Bounded (x : RatFunc K) : Prop := x.intDegree ≤ 0

theorem proper_zero : Proper (0 : RatFunc K) := Or.inl rfl

theorem Proper.bounded {x : RatFunc K} (hx : Proper x) : Bounded x := by
  rcases hx with rfl | h
  · simp [Bounded]
  · exact h.le

theorem Proper.add {x y : RatFunc K} (hx : Proper x) (hy : Proper y) : Proper (x + y) := by
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · simpa only [add_zero, Proper] using (Or.inr hx : Proper x)
  by_cases hz : x + y = 0
  · exact Or.inl hz
  · exact Or.inr ((RatFunc.intDegree_add_le hz).trans_lt (max_lt hx hy))

theorem Proper.neg {x : RatFunc K} (h : Proper x) : Proper (-x) := by
  simpa [Proper] using h

theorem Proper.sub {x y : RatFunc K} (hx : Proper x) (hy : Proper y) : Proper (x-y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem Proper.mul_bounded {x y : RatFunc K} (hx : Proper x) (hy : Bounded y) : Proper (x*y) := by
  rcases hx with rfl | hx
  · simpa using (proper_zero (K := K))
  by_cases hz : y = 0
  · simp [hz, Proper]
  have hn : x ≠ 0 := by rintro rfl; simp at hx
  right
  rw [RatFunc.intDegree_mul hn hz]
  exact add_neg_of_neg_of_nonpos hx hy

theorem bounded_C (k : K) : Bounded (RatFunc.C k) := by simp [Bounded]

theorem proper_polynomial {p : K[X]} :
    Proper (algebraMap K[X] (RatFunc K) p) ↔ p = 0 := by
  simp [Proper]

theorem proper_div {p q : K[X]} (hq : q ≠ 0) (hp : p.degree < q.degree) :
    Proper (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) := by
  by_cases h : p = 0
  · simp [h, Proper]
  · right
    rw [RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero h) (RatFunc.algebraMap_ne_zero hq)]
    simp only [RatFunc.intDegree_polynomial, sub_neg, Int.ofNat_lt]
    exact (natDegree_lt_iff_degree_lt h).mpr (by simpa [degree_eq_natDegree hq] using hp)

theorem exists_polynomial_part (v : RatFunc K) :
    ∃ p : K[X], Proper (v - algebraMap K[X] (RatFunc K) p) := by
  refine ⟨v.num / v.denom, ?_⟩
  let emb := algebraMap K[X] (RatFunc K)
  have h := congrArg emb (EuclideanDomain.mod_add_div v.num v.denom)
  change emb (v.num % v.denom + v.denom * (v.num / v.denom)) = emb v.num at h
  rw [map_add, map_mul] at h
  have he : v - emb (v.num / v.denom) = emb (v.num % v.denom) / emb v.denom := by
    conv_lhs => lhs; rw [← v.num_div_denom]
    change emb v.num / emb v.denom - emb (v.num / v.denom) = _
    rw [← h]
    field_simp [show emb v.denom ≠ 0 from RatFunc.algebraMap_ne_zero v.denom_ne_zero]
    ring
  rw [he]
  exact proper_div v.denom_ne_zero (degree_mod_lt _ v.denom_ne_zero)

noncomputable def leadingRatio (v : RatFunc K) : K :=
  v.num.leadingCoeff / v.denom.leadingCoeff

theorem Bounded.add {x y : RatFunc K} (hx : Bounded x) (hy : Bounded y) : Bounded (x+y) := by
  by_cases hz : x+y = 0
  · simp [hz, Bounded]
  · exact (RatFunc.intDegree_add_le hz).trans (max_le hx hy)

theorem Proper.sum {ι : Type*} (s : Finset ι) {v : ι → RatFunc K} (hp : ∀ i ∈ s, Proper (v i)) :
    Proper (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (proper_zero (K := K))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self ..)).add (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))

variable [Differential K] [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
variable {a b : K}
local notation "emb" => algebraMap K[X] (RatFunc K)

theorem proper_logDeriv_polynomial
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C b)
    {p : K[X]} (hp : p ≠ 0) : Proper (logDeriv (emb p) -
      RatFunc.C (logDeriv p.leadingCoeff + (p.natDegree : K) * a)) := by
  let c := logDeriv p.leadingCoeff + (p.natDegree : K) * a
  have hd : (affine a b p - C c * p).degree < p.degree := by
    rw [degree_eq_natDegree hp, degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_sub, coeff_affine, coeff_C_mul]
    obtain rfl | hm := hm.eq_or_lt
    · rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), coeff_natDegree]
      dsimp [c, logDeriv]
      field_simp [leadingCoeff_ne_zero.mpr hp]
      ring
    · simp [coeff_eq_zero_of_natDegree_lt hm,
        coeff_eq_zero_of_natDegree_lt (hm.trans (Nat.lt_succ_self m))]
  convert proper_div hp hd using 1
  rw [logDeriv, affineDeriv_map dx, map_sub, map_mul, RatFunc.algebraMap_C]
  change _ - RatFunc.C c = _
  field_simp [RatFunc.algebraMap_ne_zero hp]

theorem proper_logDeriv
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C b) (v : RatFunc K) :
    Proper (logDeriv v - RatFunc.C (logDeriv (leadingRatio v) + (v.intDegree : K) * a)) := by
  by_cases hz : v = 0
  · simp [hz, leadingRatio, Proper]
  have hn := RatFunc.num_ne_zero hz
  have hd := v.denom_ne_zero
  have hr := (proper_logDeriv_polynomial dx hn).sub (proper_logDeriv_polynomial dx hd)
  convert hr using 1
  conv_lhs => enter [1, 1]; rw [← v.num_div_denom]
  rw [logDeriv_div _ _ (RatFunc.algebraMap_ne_zero hn) (RatFunc.algebraMap_ne_zero hd)]
  rw [leadingRatio, logDeriv_div _ _ (leadingCoeff_ne_zero.mpr hn) (leadingCoeff_ne_zero.mpr hd),
    RatFunc.intDegree]
  push_cast
  simp only [map_add, map_mul, map_sub]
  ring

theorem bounded_logDeriv
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C b) (v : RatFunc K) :
    Bounded (logDeriv v) := by
  have h := (proper_logDeriv dx v).bounded.add
    (bounded_C (logDeriv (leadingRatio v) + (v.intDegree : K) * a))
  simpa only [sub_add_cancel] using h

theorem Proper.deriv
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C b)
    {v : RatFunc K} (hv : Proper v) : Proper v′ := by
  by_cases hz : v = 0
  · simp [hz, Proper]
  · have h := hv.mul_bounded (bounded_logDeriv dx v)
    rwa [show v * logDeriv v = v′ by unfold logDeriv; field_simp] at h

end AtInfinity

open AtInfinity

section Projection

variable [Differential K]
variable [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
variable {a b : K}
local notation "emb" => algebraMap K[X] (RatFunc K)

theorem project_polynomial {ι : Type*} [Fintype ι]
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C b)
    (q : K[X]) (c : ι → K) (u : ι → RatFunc K) (v : RatFunc K)
    (h : emb q = ∑ i, RatFunc.C (c i) * logDeriv (u i) + v′) :
    ∃ p : K[X], q = affine a b p + C
      (∑ i, c i * (logDeriv (leadingRatio (u i)) + ((u i).intDegree : K) * a)) := by
  have error : Proper (emb q - (∑ i, RatFunc.C (c i) * logDeriv (u i) + v′)) := by
    rw [h, sub_self]
    exact proper_zero
  classical
  obtain ⟨p, hp⟩ := exists_polynomial_part v
  refine ⟨p, sub_eq_zero.mp (proper_polynomial.mp ?_)⟩
  let k (i : ι) := logDeriv (leadingRatio (u i)) + ((u i).intDegree : K) * a
  have hu (i : ι) : Proper (RatFunc.C (c i) * logDeriv (u i) - RatFunc.C (c i * k i)) := by
    convert (proper_logDeriv dx (u i)).mul_bounded (bounded_C (c i)) using 1
    rw [map_mul]
    dsimp only [k]
    ring
  have hs := Proper.sum Finset.univ (fun i _ => hu i)
  have hv := hp.deriv dx
  rw [map_sub, affineDeriv_map dx] at hv
  rw [map_sub, map_add, RatFunc.algebraMap_C, map_sum]
  convert error.add (hs.add hv) using 1
  rw [Finset.sum_sub_distrib]
  abel

section
omit [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]

theorem exponential_positive_coefficient {p q : K[X]} {j : ℕ} (hj : 0 < j) {k a : K}
    (eqn : q = affine a 0 p + C k) :
    (p.coeff j)′ + (j : K) * a * p.coeff j = q.coeff j := by
  rw [eqn, coeff_add, coeff_affine, coeff_C]
  simp [hj.ne']

/-- The constant term remaining after projection is a lower-field Liouville
form, with the degree contribution absorbed into a derivative. -/
theorem exponential_constant_coefficient {ι : Type} [Fintype ι] {p q : K[X]}
    (g : K) (c : ι → K) (hc : ∀ i, (c i)′ = 0) (u : ι → RatFunc K)
    (eqn : q = affine g′ 0 p + C
      (∑ i, c i * (logDeriv (leadingRatio (u i)) + ((u i).intDegree : K) * g′))) :
    InLiouvilleForm K (q.coeff 0) := by
  let m := ∑ i, c i * ((u i).intDegree : K)
  have dm : m′ = 0 := by simp [m, Derivation.leibniz, hc]
  refine ⟨ι, inferInstance, c, hc, fun i => leadingRatio (u i), p.coeff 0 + m * g, ?_⟩
  have hh := congrArg (fun f : K[X] => f.coeff 0) eqn
  simp [coeff_affine, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul] at hh
  simpa [Derivation.leibniz, dm, m, add_comm, add_assoc, add_left_comm] using hh

end

end Projection

section Exponential

variable [Differential K] [Differential (RatFunc K)]
variable [DifferentialAlgebra K (RatFunc K)]
local notation "emb" => algebraMap K[X] (RatFunc K)

/-- Reassemble the polynomial derivative with a lower-field Liouville form. -/
theorem polynomial_derivative_add_constant {a b : K}
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C b)
    (p : K[X]) {h : K} (form : InLiouvilleForm K h) :
    InLiouvilleForm K (emb (affine a b p + C h)) := by
  obtain ⟨ι, inst, c, hc, u, v, eqn⟩ := form
  refine ⟨ι, inst, c, hc, fun i => algebraMap K (RatFunc K) (u i),
    emb p + algebraMap K (RatFunc K) v, ?_⟩
  rw [map_add, RatFunc.algebraMap_C, ← affineDeriv_map dx, eqn, map_add, map_sum, map_add]
  have d (v : K) : RatFunc.C v′ = (algebraMap K (RatFunc K) v)′ := (deriv_algebraMap v).symm
  have logC (z : K) : logDeriv (RatFunc.C z) = RatFunc.C (logDeriv z) := logDeriv_algebraMap z
  simp only [Algebra.algebraMap_self_apply, map_mul, RatFunc.algebraMap_eq_C,
    logC, d, add_comm, add_left_comm]

/-- A polynomial in an exponential generator is in Liouville form exactly when
its constant term has such a form in the lower field and the finitely many
positive coefficients admit Risch multipliers there. -/
theorem exponential_polynomial_iff (g : K)
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C g′ * RatFunc.X)
    (q : K[X]) : InLiouvilleForm K (emb q) ↔ InLiouvilleForm K (q.coeff 0) ∧
      ∀ n : ℕ, 0 < n → n ≤ q.natDegree → ∃ r : K, r′ + (n : K)*g′*r = q.coeff n := by
  have dx' : (RatFunc.X : RatFunc K)′ = RatFunc.C g′ * RatFunc.X + RatFunc.C 0 := by simpa using dx
  constructor
  · rintro ⟨ι, inst, c, hc, u, v, h⟩
    obtain ⟨p, hp⟩ := project_polynomial dx' q c u v h
    exact ⟨exponential_constant_coefficient g c hc u hp, fun n hn _ =>
      ⟨p.coeff n, exponential_positive_coefficient hn hp⟩⟩
  · classical
    rintro ⟨lower, multipliers⟩
    let r (n : Fin (q.natDegree+1)) : K := if hn : 0 < n.val then
      (multipliers n hn (Nat.le_of_lt_succ n.isLt)).choose else 0
    have rpos (n : Fin (q.natDegree+1)) (hn : 0 < n.val) :
        r n = (multipliers n hn (Nat.le_of_lt_succ n.isLt)).choose := dite_eq_left hn
    let p := ofFn (q.natDegree+1) r
    have hp : q = affine g′ 0 p + C (q.coeff 0) := by
      ext n
      rw [coeff_add, coeff_affine]
      by_cases small : n < q.natDegree+1
      · rw [show p.coeff n = r ⟨n,small⟩ from ofFn_coeff_eq_val_of_lt ..]
        cases n with
        | zero => simp [r]
        | succ n =>
          rw [rpos _ (Nat.succ_pos n)]
          simpa [coeff_C_succ] using
            (multipliers (n+1) (Nat.succ_pos _) (Nat.le_of_lt_succ small)).choose_spec.symm
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
        rw [show p.coeff n = 0 from ofFn_coeff_eq_zero_of_ge _ (by omega)]
        simp [coeff_C, show n ≠ 0 by omega]
    rw [hp]
    exact polynomial_derivative_add_constant dx' p lower

end Exponential

section DegreeBound

variable [Differential K]
variable [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
variable [CharZero K]

omit [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
  [CharZero K] in
theorem primitive_positive_coefficient {q p : K[X]} {k b : K} (hp : q = affine 0 b p + C k)
    (i : ℕ) : (p.coeff (i+1))′ + ((i+2 : ℕ) : K)*b*p.coeff (i+2) = q.coeff (i+1) := by
  have he := congrArg (fun f : K[X] => f.coeff (i+1)) hp
  simpa only [coeff_C_succ, coeff_add, add_zero, coeff_affine, mul_zero, zero_mul] using he.symm

omit [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)] in
/-- In a primitive monomial with unchanged constants, the polynomial part of
a Liouville antiderivative has degree at most one above the integrand. -/
theorem primitive_projection_degree_le {b : K} (hb : ¬ ∃ w : K, w′ = b)
    {p q : K[X]} {k : K} (hp : q = affine 0 b p + C k) : p.natDegree ≤ q.natDegree+1 := by
  have recurrence (i : ℕ) (hi : q.natDegree < i+1) := (primitive_positive_coefficient hp i).trans
    (coeff_eq_zero_of_natDegree_lt hi)
  by_contra! hn
  let n := p.natDegree - 2
  have hn' : p.natDegree = n+2 := by dsimp [n]; omega
  let u := p.coeff (n+2)
  have hlead : u = p.leadingCoeff := by rw [← coeff_natDegree, hn']
  have nz : u ≠ 0 := by
    rw [hlead, leadingCoeff_ne_zero]
    rintro rfl
    simp at hn
  have hhi : p.coeff (n+1+2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have dc : u′ = 0 := by simpa only [hhi, mul_zero, add_zero] using recurrence (n+1) (by omega)
  let d : K := ((n+2 : ℕ) : K) * u
  have d0 : d ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) nz
  have dd : d′ = 0 := by
    simp only [d, Derivation.leibniz, Derivation.map_natCast, dc, smul_zero, add_zero]
  have du : (p.coeff (n+1))′ = -(d*b) := by
    have hr := recurrence n (by omega)
    change (p.coeff (n+1))′ + (n+2 : ℕ) * b * u = 0 at hr
    dsimp only [d]
    linear_combination hr
  apply hb
  refine ⟨-(p.coeff (n+1)) / d, ?_⟩
  rw [Derivation.leibniz_div, map_neg, du, dd]
  simp only [smul_eq_mul, mul_zero, sub_zero, neg_neg]
  field_simp [d0]

end DegreeBound

section Primitive

variable [Differential K] [Differential (RatFunc K)]
variable [DifferentialAlgebra K (RatFunc K)]
local notation "emb" => algebraMap K[X] (RatFunc K)

/-- Polynomial reduction for a primitive monomial. The coefficient vector must
satisfy the triangular system through degree deg(q)+1. Only the remaining
constant term needs a lower-field Liouville form. For a logarithmic monomial,
b is the logarithmic derivative of the adjoined logarithm's argument. -/
theorem primitive_polynomial_iff [CharZero K]
    (b : K) (hb : ¬ ∃ w : K, w′ = b) (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C b) (q : K[X]) :
    InLiouvilleForm K (emb q) ↔ ∃ p : K[X], p.natDegree ≤ q.natDegree+1 ∧
      InLiouvilleForm K (q.coeff 0 - b*p.coeff 1) ∧
      ∀ i : ℕ, i ≤ q.natDegree →
        (p.coeff (i+1))′ + ((i+2 : ℕ) : K)*b*p.coeff (i+2) = q.coeff (i+1) := by
  have dx' : (RatFunc.X : RatFunc K)′ = RatFunc.C 0 * RatFunc.X + RatFunc.C b := by simpa using dx
  constructor
  · rintro ⟨ι, inst, c, hc, u, v, h⟩
    obtain ⟨p, hp⟩ := project_polynomial dx' q c u v h
    refine ⟨p, primitive_projection_degree_le hb hp, ?_,
      fun i _ => primitive_positive_coefficient hp i⟩
    refine ⟨ι, inst, c, hc, fun i => AtInfinity.leadingRatio (u i), p.coeff 0, ?_⟩
    have constant := congrArg (fun f : K[X] => f.coeff 0) hp
    simp [coeff_affine] at constant
    rw [constant]
    simp only [Algebra.algebraMap_self_apply]
    ring
  · rintro ⟨p, degree, lower, eqs⟩
    let r := p - C (p.coeff 0)
    have eqn : q = affine 0 b r + C (q.coeff 0 - b*p.coeff 1) := by
      ext n
      cases n with
      | zero => simp [r, coeff_affine]
      | succ i =>
        rw [coeff_add, coeff_C_succ, add_zero, coeff_affine]
        simp only [r, coeff_sub, coeff_C_succ, sub_zero, mul_zero, zero_mul, add_zero]
        by_cases hi : i ≤ q.natDegree
        · exact (eqs i hi).symm
        · simp [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i+1),
            coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i+1+1),
            coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < i+1)]
    rw [eqn]
    exact polynomial_derivative_add_constant dx' r lower

end Primitive

section ElementaryStep

variable [Differential K] [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]

/-- Liouville descent through a transcendental exponential. -/
theorem isLiouville_exp (g : K) (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C g′ * RatFunc.X) :
    IsLiouville K (RatFunc K) where
  isLiouville h ι _ c hc u v eqn := by
    have top : InLiouvilleForm K (algebraMap K[X] (RatFunc K) (C h)) :=
      ⟨ι, _, c, hc, u, v, by simpa only [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C] using eqn⟩
    obtain ⟨lower, _⟩ := (exponential_polynomial_iff g dx (C h)).mp top
    simpa only [InLiouvilleForm, coeff_C_zero, Algebra.algebraMap_self_apply] using lower

/-- Liouville descent through a transcendental logarithm whose derivative
has no primitive in the preceding field. -/
theorem isLiouville_log [CharZero K] (g : K) (nonprim : ¬ ∃ w : K, w′ = logDeriv g)
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C (logDeriv g)) :
    IsLiouville K (RatFunc K) where
  isLiouville h ι _ c hc u v eqn := by
    have top : InLiouvilleForm K (algebraMap K[X] (RatFunc K) (C h)) :=
      ⟨ι, _, c, hc, u, v, by simpa only [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C] using eqn⟩
    obtain ⟨p, hd, ⟨κ, iκ, k, hk, z, w, lower⟩, recurrence⟩ :=
      (primitive_polynomial_iff _ nonprim dx (C h)).mp top
    simp only [natDegree_C, zero_add] at hd
    have c1 : (p.coeff 1)′ = 0 := by
      simpa [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < 2)] using
        recurrence 0 (Nat.zero_le _)
    refine ⟨Option κ, inferInstance, Option.elim' (p.coeff 1) k, ?_,
      Option.elim' g z, w, ?_⟩
    · rintro (_ | i)
      · exact c1
      · exact hk i
    · rw [Fintype.sum_option]
      simp only [coeff_C_zero, Algebra.algebraMap_self_apply] at lower
      dsimp
      linear_combination lower

end ElementaryStep

universe u

private theorem transport_form {K R S : Type u} [Field K] [Field R] [Field S]
    [Differential K] [Differential S] [Algebra K R] [Algebra K S] [DifferentialAlgebra K S]
    (e : R ≃ₐ[K] S) : letI := Differential.equiv e.toRingEquiv
    IsLiouville K R → IsLiouville K S := by
  let := Differential.equiv e.toRingEquiv
  intro h
  constructor
  intro f ι _ c hc z v eqn
  apply h.isLiouville f ι c hc (e.symm ∘ z) (e.symm v)
  have d (w : S) : e.symm w′ = (e.symm w)′ := by
    change e.symm w′ = e.symm (e (e.symm w))′
    rw [e.apply_symm_apply]
  simpa only [Function.comp_apply, map_add, map_sum, map_mul, logDeriv, map_div₀,
    e.symm.commutes, d] using congrArg e.symm eqn

theorem ElementaryStep.isLiouville {K L : Type u} [Field K] [CharZero K] [Field L]
    [Differential K] [Differential L] [Algebra K L] [DifferentialAlgebra K L]
    (s : ElementaryStep K L) : IsLiouville K L := by
  cases s with
  | algebraic => infer_instance
  | exp e g dx =>
    apply transport_form e
    let := Differential.equiv e.toRingEquiv
    let := DifferentialAlgebra.equiv e
    apply isLiouville_exp g
    apply e.injective
    change e (e.symm (e RatFunc.X)′) = _
    simpa only [e.apply_symm_apply, map_mul, ← RatFunc.algebraMap_eq_C, e.commutes] using dx
  | log e g h dx =>
    apply transport_form e
    let := Differential.equiv e.toRingEquiv
    let := DifferentialAlgebra.equiv e
    apply isLiouville_log g h
    apply e.injective
    change e (e.symm (e RatFunc.X)′) = _
    simpa only [e.apply_symm_apply, ← RatFunc.algebraMap_eq_C, e.commutes] using dx

theorem ElementaryTower.isLiouville {F L : Type u} [Field F] [CharZero F] [Differential F]
    [Field L] [Differential L] [Algebra F L] (tower : ElementaryTower F L) : IsLiouville F L := by
  induction tower with
  | base => exact IsLiouville.rfl _
  | @adjoin K L _ _ _ _ _ _ _ _ _ _ _ lower step ih =>
    let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
    exact IsLiouville.trans F K ih step.isLiouville

/-- Any primitive in a finite elementary output tower yields a differential
plus finitely many constant logarithmic derivatives in its input field. -/
theorem ElementaryTower.form_of_primitive {F L : Type u} [Field F] [CharZero F] [Differential F]
    [Field L] [Differential L] [Algebra F L] (tower : ElementaryTower F L) (f : F)
    (v : L) (hv : v′ = algebraMap F L f) : InLiouvilleForm F f := by
  obtain ⟨ι, iι, c, hc, z, w, h⟩ := tower.isLiouville.isLiouville f (Fin 0)
    Fin.elim0 (fun i => i.elim0) Fin.elim0 v (by simpa using hv.symm)
  exact ⟨ι, iι, c, hc, z, w, by simpa only [Algebra.algebraMap_self_apply] using h⟩

/-! ### Regularity at a prime and Laurent polynomials in an exponential generator -/

section Laurent

noncomputable local instance intAlgebraLiouvilleForm {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _
local notation "emb" => algebraMap K[X] (RatFunc K)

namespace Residue

/-- Rational functions evaluable at the generic point of the prime polynomial. -/
def Regular (s : K[X]) (r : RatFunc K) : Prop :=
  ∃ p t : K[X], ¬s ∣ t ∧ r = emb p / emb t

theorem regular_poly {s : K[X]} (hs : Prime s) (p : K[X]) : Regular s (emb p) :=
  ⟨p, 1, fun h => hs.not_isUnit (isUnit_of_dvd_one h), by simp⟩

theorem Regular.add {s : K[X]} (hs : Prime s) {v w : RatFunc K} (hv : Regular s v)
    (hw : Regular s w) : Regular s (v+w) := by
  obtain ⟨p, t, ht, rfl⟩ := hv
  obtain ⟨q, d, hd, rfl⟩ := hw
  have tn : t ≠ 0 := fun h => ht (h ▸ dvd_zero _)
  have dn : d ≠ 0 := fun h => hd (h ▸ dvd_zero _)
  exact ⟨p*d+q*t, t*d, fun h => (hs.dvd_mul.mp h).elim ht hd,
    by
      simp only [map_add, map_mul]
      field_simp [RatFunc.algebraMap_ne_zero tn, RatFunc.algebraMap_ne_zero dn]⟩

theorem Regular.neg {s : K[X]} {v : RatFunc K} (hv : Regular s v) : Regular s (-v) := by
  obtain ⟨p,t,ht,rfl⟩ := hv
  exact ⟨-p,t, ht, by rw [map_neg, neg_div]⟩

theorem Regular.smul {s : K[X]} {v : RatFunc K} (hv : Regular s v) (c : K) :
    Regular s (RatFunc.C c*v) := by
  obtain ⟨p,t,ht,rfl⟩ := hv
  exact ⟨C c * p,t,ht, by simp [mul_div_assoc]⟩

theorem Regular.sum {s : K[X]} (hs : Prime s) {ι : Type*} (S : Finset ι) {v : ι → RatFunc K}
    (h : ∀ i ∈ S, Regular s (v i)) : Regular s (∑ i ∈ S, v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using regular_poly hs 0
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).add hs
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

variable [Differential K] [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
variable {a b : K}

private theorem regular_log_poly
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C b)
    {s : K[X]} (hs : Prime s) {p : K[X]} (hn : p ≠ 0) :
    ∃ n : ℕ, Regular s (logDeriv (emb p) - (n : RatFunc K)*logDeriv (emb s)) := by
  obtain ⟨t, ht, hst⟩ := (FiniteMultiplicity.of_prime_left hs hn).exists_eq_pow_mul_and_not_dvd
  have tn : t ≠ 0 := fun h => hst (h ▸ dvd_zero _)
  refine ⟨multiplicity s p, affine a b t, t, hst, ?_⟩
  conv_lhs => enter [1, 1]; rw [ht, map_mul, map_pow]
  rw [logDeriv_mul _ _ (pow_ne_zero _ (RatFunc.algebraMap_ne_zero hs.ne_zero))
      (RatFunc.algebraMap_ne_zero tn),
    Differential.logDeriv_pow, add_sub_cancel_left, Differential.logDeriv, affineDeriv_map dx]

theorem regular_logDeriv
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C b)
    {s : K[X]} (hs : Prime s) (v : RatFunc K) :
    ∃ j : ℤ, Regular s (logDeriv v - (j : RatFunc K)*logDeriv (emb s)) := by
  by_cases hv : v = 0
  · exact ⟨0, by simpa [hv] using regular_poly hs 0⟩
  obtain ⟨m, hm⟩ := regular_log_poly dx hs (RatFunc.num_ne_zero hv)
  obtain ⟨n, hn⟩ := regular_log_poly dx hs v.denom_ne_zero
  refine ⟨(m : ℤ)-n, ?_⟩
  convert hm.add hs hn.neg using 1
  conv_lhs => enter [1, 1]; rw [← v.num_div_denom]
  rw [logDeriv_div _ _ (RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hv))
    (RatFunc.algebraMap_ne_zero v.denom_ne_zero)]
  push_cast
  ring

end Residue

open AtInfinity Residue

variable [Differential K] [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
variable {a b : K}

/-- Projection at infinity of an integrand with a prescribed proper part. -/
theorem project_polynomial_add {ι : Type*} [Fintype ι]
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C b)
    (q : K[X]) {ρ : RatFunc K} (hρ : Proper ρ) (c : ι → K) (u : ι → RatFunc K) (v : RatFunc K)
    (h : emb q + ρ = ∑ i, RatFunc.C (c i) * Differential.logDeriv (u i) + v′) :
    ∃ p : K[X], q = affine a b p + C
      (∑ i, c i * (Differential.logDeriv (leadingRatio (u i)) + ((u i).intDegree : K) * a)) := by
  have error : Proper (emb q - (∑ i, RatFunc.C (c i) * Differential.logDeriv (u i) + v′)) := by
    rw [← h, sub_add_cancel_left]
    exact hρ.neg
  classical
  obtain ⟨p, hp⟩ := exists_polynomial_part v
  refine ⟨p, sub_eq_zero.mp (proper_polynomial.mp ?_)⟩
  let k (i : ι) := Differential.logDeriv (leadingRatio (u i)) + ((u i).intDegree : K) * a
  have hu (i : ι) :
      Proper (RatFunc.C (c i) * Differential.logDeriv (u i) - RatFunc.C (c i * k i)) := by
    convert (proper_logDeriv dx (u i)).mul_bounded (bounded_C (c i)) using 1
    rw [map_mul]
    dsimp only [k]
    ring
  have hs := Proper.sum Finset.univ (fun i _ => hu i)
  have hv := hp.deriv dx
  rw [map_sub, affineDeriv_map dx] at hv
  rw [map_sub, map_add, RatFunc.algebraMap_C, map_sum]
  convert error.add (hs.add hv) using 1
  rw [Finset.sum_sub_distrib]
  abel

/-- Differentiation preserves regularity at any prime. -/
theorem regular_deriv
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C b)
    {s : K[X]} (hs : Prime s) {r : RatFunc K} (h : Regular s r) : Regular s r′ := by
  obtain ⟨p, d, hd, rfl⟩ := h
  have dn : d ≠ 0 := fun h => hd (h ▸ dvd_zero _)
  refine ⟨affine a b p * d - p * affine a b d, d^2,
    fun h => hd (hs.dvd_of_dvd_pow h), ?_⟩
  rw [Derivation.leibniz_div, affineDeriv_map dx, affineDeriv_map dx]
  simp only [smul_eq_mul, map_sub, map_mul, map_pow]
  field_simp [RatFunc.algebraMap_ne_zero dn]

/-- For an exponential monomial, logarithmic derivatives have no pole at zero. -/
theorem regular_logDeriv_X (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X)
    (v : RatFunc K) : Regular (X : K[X]) (Differential.logDeriv v) := by
  have dx' : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C 0 := by simpa using dx
  obtain ⟨j, hj⟩ := regular_logDeriv dx' prime_X v
  have hX : Differential.logDeriv (emb (X : K[X])) = RatFunc.C a := by
    rw [RatFunc.algebraMap_X, Differential.logDeriv, dx, mul_div_assoc, div_self RatFunc.X_ne_zero,
      mul_one]
  have := hj.add prime_X (regular_poly prime_X (C ((j : K) * a)))
  convert this using 1
  rw [hX, RatFunc.algebraMap_C, map_mul, map_intCast]
  ring

omit [Differential K] [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)] in
/-- Every rational function is regular at zero up to a polynomial in the inverse generator. -/
theorem exists_principal_part (v : RatFunc K) (m₀ : ℕ) :
    ∃ (m : ℕ) (A : K[X]), m₀ ≤ m ∧ (∀ i, m ≤ i → A.coeff i = 0) ∧
      Regular (X : K[X]) (v - emb A / RatFunc.X ^ m) := by
  obtain ⟨d, hd, hXd⟩ :=
    (FiniteMultiplicity.of_prime_left prime_X v.denom_ne_zero).exists_eq_pow_mul_and_not_dvd
  generalize multiplicity (X : K[X]) v.denom = m₁ at hd
  have dn : d ≠ 0 := fun h => hXd (h ▸ dvd_zero _)
  have hv : v = emb v.num / (RatFunc.X ^ m₁ * emb d) := by
    conv_lhs => rw [← v.num_div_denom]
    rw [hd, map_mul, map_pow, RatFunc.algebraMap_X]
  generalize v.num = N at hv
  subst hv
  obtain ⟨α, β, hαβ⟩ : IsCoprime (X^m₁ : K[X]) d :=
    (prime_X.irreducible.coprime_iff_not_dvd.mpr hXd).pow_left
  obtain ⟨A, hA⟩ : ∃ A : K[X], A = (N * β) %ₘ X^m₁ := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : K[X], Q = (N * β) /ₘ X^m₁ := ⟨_, rfl⟩
  have split : A + X^m₁ * Q = N * β := by
    rw [hA, hQ]
    exact modByMonic_add_div _ _
  have small : ∀ i, m₁ ≤ i → A.coeff i = 0 := by
    intro i hi
    apply coeff_eq_zero_of_degree_lt
    rw [hA]
    refine (degree_modByMonic_lt _ (monic_X_pow m₁)).trans_le ?_
    rw [degree_X_pow]
    exact_mod_cast hi
  refine ⟨m₁ + m₀, A * X^m₀, Nat.le_add_left _ _, ?_, N * α + Q * d, d, hXd, ?_⟩
  · intro i hi
    rw [coeff_mul_X_pow']
    split
    · exact small _ (by omega)
    · rfl
  · have xn : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
    have dn' := RatFunc.algebraMap_ne_zero dn
    have h1 : emb α * RatFunc.X^m₁ + emb β * emb d = 1 := by
      simpa only [map_add, map_mul, map_pow, RatFunc.algebraMap_X, map_one] using congrArg emb hαβ
    have h2 : emb A + RatFunc.X^m₁ * emb Q = emb N * emb β := by
      simpa only [map_add, map_mul, map_pow, RatFunc.algebraMap_X] using congrArg emb split
    simp only [map_mul, map_add, map_pow, RatFunc.algebraMap_X]
    rw [div_sub_div _ _ (mul_ne_zero (pow_ne_zero _ xn) dn') (pow_ne_zero _ xn),
      div_eq_div_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero _ xn) dn') (pow_ne_zero _ xn)) dn']
    rw [pow_add]
    linear_combination (emb d * RatFunc.X^m₁ * RatFunc.X^m₀) * (-(emb N) * h1 - emb d * h2)

omit [Differential K] [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)] in
/-- A polynomial in the inverse generator without constant term that is regular at zero vanishes. -/
theorem principal_part_unique {m : ℕ} {A : K[X]} (hA : ∀ i, m ≤ i → A.coeff i = 0)
    (h : Regular (X : K[X]) (emb A / RatFunc.X ^ m)) : A = 0 := by
  obtain ⟨p, d, hd, eq⟩ := h
  have dn : d ≠ 0 := fun h => hd (h ▸ dvd_zero _)
  have poly : A * d = X^m * p := by
    apply RatFunc.algebraMap_injective K
    simp only [map_mul, map_pow, RatFunc.algebraMap_X]
    rw [div_eq_div_iff (pow_ne_zero _ RatFunc.X_ne_zero) (RatFunc.algebraMap_ne_zero dn)] at eq
    linear_combination eq
  have dvd : X^m ∣ A :=
    (IsCoprime.pow_left (prime_X.irreducible.coprime_iff_not_dvd.mpr hd)).dvd_of_dvd_mul_right
      ⟨p, poly⟩
  ext i
  by_cases hi : i < m
  · simpa using (X_pow_dvd_iff.mp dvd) i hi
  · simpa using hA i (by omega)

/-- The derivation of an exponential monomial acts on each power of the generator. -/
theorem deriv_div_X_pow (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X)
    (A : K[X]) (m : ℕ) :
    (emb A / RatFunc.X ^ m)′ =
      emb (affine a 0 A - C ((m : K) * a) * A) / RatFunc.X ^ m := by
  have dx' : (RatFunc.X : RatFunc K)′ = RatFunc.C a * RatFunc.X + RatFunc.C 0 := by simpa using dx
  have xn : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  induction m with
  | zero => simp [affineDeriv_map dx']
  | succ m ih =>
    rw [pow_succ, ← div_div, Derivation.leibniz_div, ih, dx]
    simp only [smul_eq_mul, map_sub, map_mul, RatFunc.algebraMap_C, map_natCast, Nat.cast_add,
      Nat.cast_one, map_add, map_one]
    field_simp
    ring

/-- A Laurent polynomial in an exponential generator in Liouville form has a constant
coefficient in Liouville form, and every other coefficient solves a Risch differential
equation in the lower field. -/
theorem exponential_laurent_necessary (g : K)
    (dx : (RatFunc.X : RatFunc K)′ = RatFunc.C g′ * RatFunc.X) (q : K[X]) (k : ℕ)
    (form : InLiouvilleForm K (emb q / RatFunc.X ^ k)) :
    InLiouvilleForm K (q.coeff k) ∧
      ∀ j : ℕ, j ≠ k → ∃ r : K, r′ + ((j : K) - (k : K)) * g′ * r = q.coeff j := by
  have dx' : (RatFunc.X : RatFunc K)′ = RatFunc.C g′ * RatFunc.X + RatFunc.C 0 := by simpa using dx
  have xn : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  obtain ⟨ι, inst, c, hc, u, v, h⟩ := form
  simp only [RatFunc.algebraMap_eq_C] at h
  -- the part at infinity
  obtain ⟨lo, hlo⟩ : ∃ lo : K[X], lo = q %ₘ X^k := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi : K[X], hi = q /ₘ X^k := ⟨_, rfl⟩
  have split : lo + X^k * hi = q := by
    rw [hlo, hhi]
    exact modByMonic_add_div _ _
  have lodeg : lo.degree < (X^k : K[X]).degree := by
    rw [hlo]
    exact degree_modByMonic_lt _ (monic_X_pow k)
  have hicoeff (i : ℕ) : hi.coeff i = q.coeff (i + k) := by
    have z : lo.coeff (i + k) = 0 := by
      apply coeff_eq_zero_of_degree_lt
      refine lodeg.trans_le ?_
      rw [degree_X_pow]
      exact_mod_cast Nat.le_add_left k i
    rw [← split, coeff_add, coeff_X_pow_mul, z, zero_add]
  have eqInf : emb hi + emb lo / emb (X^k) =
      ∑ i, RatFunc.C (c i) * Differential.logDeriv (u i) + v′ := by
    rw [← h, ← split, map_add, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp
    ring
  obtain ⟨p, hp⟩ :=
    project_polynomial_add dx' hi (proper_div (pow_ne_zero k X_ne_zero) lodeg) c u v eqInf
  refine ⟨?_, fun j hj => ?_⟩
  · have := exponential_constant_coefficient g c hc u hp
    rwa [hicoeff, zero_add] at this
  rcases Nat.lt_or_gt_of_ne hj with lt | gt
  · -- the part at zero
    obtain ⟨m, A, hm, hA, reg⟩ := exists_principal_part v k
    obtain ⟨B, hB⟩ : ∃ B : K[X], B = affine g′ 0 A - C ((m : K) * g′) * A := ⟨_, rfl⟩
    have dA : (emb A / RatFunc.X ^ m)′ = emb B / RatFunc.X ^ m := by
      rw [hB]
      exact deriv_div_X_pow dx A m
    obtain ⟨Q₁, hQ₁⟩ : ∃ Q : K[X], Q = (q * X^(m-k)) %ₘ X^m := ⟨_, rfl⟩
    obtain ⟨Q₂, hQ₂⟩ : ∃ Q : K[X], Q = (q * X^(m-k)) /ₘ X^m := ⟨_, rfl⟩
    have splitQ : Q₁ + X^m * Q₂ = q * X^(m-k) := by
      rw [hQ₁, hQ₂]
      exact modByMonic_add_div _ _
    have Qdeg : Q₁.degree < (X^m : K[X]).degree := by
      rw [hQ₁]
      exact degree_modByMonic_lt _ (monic_X_pow m)
    have Qsmall : ∀ i, m ≤ i → Q₁.coeff i = 0 := fun i hi =>
      coeff_eq_zero_of_degree_lt (Qdeg.trans_le (by rw [degree_X_pow]; exact_mod_cast hi))
    have Bsmall : ∀ i, m ≤ i → B.coeff i = 0 := by
      intro i hi
      rw [hB, coeff_sub, coeff_affine, coeff_C_mul, hA i hi, hA (i+1) (by omega)]
      simp
    have qfrac : emb q / RatFunc.X ^ k = emb Q₁ / RatFunc.X ^ m + emb Q₂ := by
      have e := congrArg emb splitQ
      simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X] at e
      have pw : (RatFunc.X : RatFunc K) ^ (m - k) * RatFunc.X ^ k = RatFunc.X ^ m := by
        rw [← pow_add, Nat.sub_add_cancel hm]
      rw [eq_comm, div_add' _ _ _ (pow_ne_zero m xn),
        div_eq_div_iff (pow_ne_zero m xn) (pow_ne_zero k xn)]
      linear_combination (RatFunc.X ^ k) * e + emb q * pw
    have regular : Regular (X : K[X]) (emb (Q₁ - B) / RatFunc.X ^ m) := by
      have sum : Regular (X : K[X]) (∑ i, RatFunc.C (c i) * Differential.logDeriv (u i)) :=
        Regular.sum prime_X Finset.univ fun i _ => (regular_logDeriv_X dx (u i)).smul (c i)
      have all := (sum.add prime_X (regular_deriv dx' prime_X reg)).add prime_X
        (regular_poly prime_X Q₂).neg
      convert all using 1
      rw [map_sub, sub_div, ← dA, map_sub, eq_sub_of_add_eq qfrac.symm, h]
      ring
    have eqB : Q₁ = B := sub_eq_zero.mp (principal_part_unique
      (fun i hi => by rw [coeff_sub, Qsmall i hi, Bsmall i hi, sub_zero]) regular)
    refine ⟨A.coeff (j + (m - k)), ?_⟩
    have cQ : Q₁.coeff (j + (m - k)) = q.coeff j := by
      have e := congrArg (fun P : K[X] => P.coeff (j + (m - k))) splitQ
      simp only [coeff_add, coeff_mul_X_pow] at e
      rw [← e, coeff_X_pow_mul', ite_eq_right (by omega), add_zero]
    rw [← cQ, eqB, hB, coeff_sub, coeff_affine, coeff_C_mul]
    have cast : ((j + (m - k) : ℕ) : K) = (j : K) - (k : K) + (m : K) := by
      rw [Nat.cast_add, Nat.cast_sub hm]
      ring
    rw [cast]
    ring
  · have pos : 0 < j - k := Nat.sub_pos_of_lt gt
    have := exponential_positive_coefficient pos hp
    rw [hicoeff, Nat.sub_add_cancel gt.le, Nat.cast_sub gt.le] at this
    exact ⟨p.coeff (j - k), this⟩

end Laurent

end SympyProofs.Calculus.Antiderivative.Extension.LiouvilleForm
