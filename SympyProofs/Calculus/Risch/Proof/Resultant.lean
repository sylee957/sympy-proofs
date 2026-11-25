module

public import SympyProofs.Calculus.Risch.Program.Resultant
public import SympyProofs.Calculus.Risch.Proof.Poly
public import SympyProofs.Calculus.Risch.Proof.Constraints
public import SympyProofs.Calculus.Risch.Proof.Subresultant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A bound on the natural numbers `j` for which `N - j E` and `B` have a common prime factor,
for polynomials in the newest generator over the field of a tower. The resultant of `B` and
`N - z E` in the unknown `z` is a nonzero polynomial over the field, and every such `j` is a
root of it. Its coefficients are quotients of polynomials in the generators with rational
coefficients, so a natural number that is a root of it is a root of each of its rational
slices. One slice is not zero, and the roots of a rational polynomial are bounded by Cauchy's
estimate.

`resPoly` computes the resultant by the subresultant algorithm one level up, where `z` is a
generator (`subresultant_spec`); `model_resPoly` identifies its result with Mathlib's
resultant of `B` and `N - z E` over the polynomials in `z`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial MPoly

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

namespace Resultant

/-! ### The resultant of `B` and `N - z E` -/

/-- The newest generator denotes the variable of the rational functions over the field
below. -/
theorem value_gen_last : Term.value k (.gen (Fin.last n) : Term (n + 1)) = RatFunc.X := by
  simp [Term.value, Term.eval, gens]

/-- `N - x E` is `N - z E` with `x` for `z`. -/
theorem map_eval_shift (N E : Poly n) (x : K k n) :
    ((Poly.model k N).map C - C X * (Poly.model k E).map C).map (evalRingHom x) =
      Poly.model k N - C x * Poly.model k E := by
  have hc : (evalRingHom x).comp C = RingHom.id (K k n) := by
    ext a
    simp
  simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, hc]

/-- `resPoly` computes the resultant of `B` and `N - z E`, as polynomials in the generator
whose coefficients are polynomials in `z`, and its coefficients are defined. -/
theorem model_resPoly {N B E : Poly n} (hN : Poly.Defined k N) (hB : Poly.Defined k B)
    (hE : Poly.Defined k E) :
    Poly.model k (resPoly N B E) =
        Polynomial.resultant ((Poly.model k B).map C)
          ((Poly.model k N).map C - C X * (Poly.model k E).map C) ∧
      Poly.Defined k (resPoly N B E) := by
  have dw : ∀ {p : Poly n}, Poly.Defined k p → Poly.Defined k (p.map Term.weaken) :=
    fun hp c hc => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
      exact (Term.inDomain_weaken a).mpr (hp a ha)
  obtain ⟨F, hF⟩ : ∃ F : Poly (n + 1), F = B.map Term.weaken := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Poly (n + 1),
      G = Poly.sub (N.map Term.weaken) (Poly.scale (.gen (Fin.last n)) (E.map Term.weaken)) :=
    ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = subresultant F G := ⟨_, rfl⟩
  have run : resPoly N B E =
      Poly.quot (Poly.ofTerm S).1 (Poly.trim (Poly.norm (Poly.ofTerm S).2)) := by
    rw [hS, hF, hG]
    rfl
  have dF : Poly.Defined k F := hF ▸ dw hB
  have dG : Poly.Defined k G := hG ▸ Poly.defined_sub (dw hN) (Poly.defined_scale trivial (dw hE))
  obtain ⟨dS, vS⟩ := subresultant_spec dF dG
  rw [← hS] at dS vS
  -- the computation over `K(z)` is the image of the resultant over `K[z]`
  have inj : Function.Injective (algebraMap (K k n)[X] (RatFunc (K k n))) :=
    RatFunc.algebraMap_injective (K k n)
  have comp : (algebraMap (K k n)[X] (RatFunc (K k n))).comp C = RatFunc.C := by
    ext a
    simp
  have eF : Poly.model k F = ((Poly.model k B).map C).map (algebraMap _ (RatFunc (K k n))) := by
    rw [hF, Poly.model_map_weaken, Polynomial.map_map, comp]
  have eG : Poly.model k G = ((Poly.model k N).map C - C X * (Poly.model k E).map C).map
      (algebraMap _ (RatFunc (K k n))) := by
    rw [hG, Poly.model_sub, Poly.model_scale, Poly.model_map_weaken, Poly.model_map_weaken,
      value_gen_last, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map,
      Polynomial.map_map, comp, Polynomial.map_C, RatFunc.algebraMap_X]
  have val : Term.value k S = algebraMap _ (RatFunc (K k n)) (Polynomial.resultant
      ((Poly.model k B).map C) ((Poly.model k N).map C - C X * (Poly.model k E).map C)) := by
    rw [vS, eF, eG, natDegree_map_eq_of_injective inj, natDegree_map_eq_of_injective inj,
      resultant_map_map]
  -- back to a polynomial in `z`, by exact division
  obtain ⟨hnum, hden⟩ := Poly.ofTerm_spec S dS
  obtain ⟨dnum, dden⟩ := Poly.ofTerm_defined (k := k) S
  obtain ⟨mD, dD, nrm, -⟩ := Poly.trim_spec (Poly.defined_norm dden)
  rw [Poly.model_norm dden] at mD
  have D0 : Poly.model k (Poly.ofTerm S).2 ≠ 0 := fun z => hden (by rw [z, map_zero])
  have nD : Poly.Normal k (Poly.trim (Poly.norm (Poly.ofTerm S).2)) :=
    nrm.resolve_left fun h => D0 (by rw [← mD, h, Poly.model_nil])
  have enum : Poly.model k (Poly.ofTerm S).1 = Polynomial.resultant ((Poly.model k B).map C)
      ((Poly.model k N).map C - C X * (Poly.model k E).map C) * Poly.model k (Poly.ofTerm S).2 :=
    inj (by rw [hnum, val, map_mul])
  have q := Poly.quot_of_dvd dnum dD nD (by rw [mD, enum]; exact Dvd.intro_left _ rfl)
  rw [mD, enum, mul_comm] at q
  refine ⟨?_, ?_⟩
  · rw [run]
    exact (mul_left_cancel₀ D0 q).symm
  · rw [run]
    exact (Poly.rem_spec dnum dD nD).2.1

/-- The coefficients of the resultant polynomial are defined. -/
theorem defined_resPoly {N B E : Poly n} (hN : Poly.Defined k N) (hB : Poly.Defined k B)
    (hE : Poly.Defined k E) : Poly.Defined k (resPoly N B E) :=
  (model_resPoly hN hB hE).2

/-- The value of the resultant polynomial at `x` is the resultant of `B` and `N - x E`, taken
with the degree of `B` and the degree of `N - z E` in the generator. -/
theorem eval_resPoly {N B E : Poly n} (hN : Poly.Defined k N) (hB : Poly.Defined k B)
    (hE : Poly.Defined k E) (x : K k n) :
    (Poly.model k (resPoly N B E)).eval x =
      Polynomial.resultant (Poly.model k B) (Poly.model k N - C x * Poly.model k E)
        (Poly.model k B).natDegree
        ((Poly.model k N).map C - C X * (Poly.model k E).map C).natDegree := by
  have hB' : ((Poly.model k B).map C).map (evalRingHom x) = Poly.model k B := by
    rw [Polynomial.map_map]
    convert Polynomial.map_id
    ext a
    simp
  rw [(model_resPoly hN hB hE).1, ← coe_evalRingHom, ← resultant_map_map, hB',
    map_eval_shift, natDegree_map_eq_of_injective (C_injective)]

private theorem padded {F : Type*} [Field F] (B p : F[X]) {m : ℕ} (hm : p.natDegree ≤ m) :
    Polynomial.resultant B p B.natDegree m =
      B.leadingCoeff ^ (m - p.natDegree) * Polynomial.resultant B p := by
  have h := resultant_add_right_deg B p B.natDegree p.natDegree (m - p.natDegree) le_rfl
  simpa only [Nat.add_sub_of_le hm, coeff_natDegree] using h

/-- Putting `x` for `z` does not raise the degree of `N - z E`. -/
theorem degree_shift_le (N E : Poly n) (x : K k n) :
    (Poly.model k N - C x * Poly.model k E).natDegree ≤
      ((Poly.model k N).map C - C X * (Poly.model k E).map C).natDegree := by
  rw [← map_eval_shift N E x]
  exact natDegree_map_le

/-- The resultant polynomial is not zero when `N` and `B` are coprime. -/
theorem resPoly_ne_zero (N E : Poly n) {B : Poly n} (dN : Poly.Defined k N)
    (dB : Poly.Defined k B) (dE : Poly.Defined k E) (hB : Poly.Normal k B)
    (cop : IsCoprime (Poly.model k N) (Poly.model k B)) :
    Poly.model k (resPoly N B E) ≠ 0 := by
  intro h
  have ev := eval_resPoly dN dB dE 0
  rw [h, eval_zero, padded _ _ (degree_shift_le N E 0)] at ev
  have e0 : Poly.model k N - C (0 : K k n) * Poly.model k E = Poly.model k N := by simp
  rw [e0] at ev
  exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hB.model_ne_zero))
    (resultant_ne_zero _ _ cop.symm) ev.symm

/-- If a prime factor of `B` divides `N - x E`, then `x` is a root of the resultant
polynomial. -/
theorem root_of_residue (N E : Poly n) {B : Poly n} (dN : Poly.Defined k N)
    (dB : Poly.Defined k B) (dE : Poly.Defined k E) (hB : Poly.Normal k B) {s : (K k n)[X]}
    (hs : Prime s) (h1 : s ∣ Poly.model k B) (x : K k n)
    (h2 : s ∣ Poly.model k N - Polynomial.C x * Poly.model k E) :
    (Poly.model k (resPoly N B E)).IsRoot x := by
  have nc : ¬ IsCoprime (Poly.model k B) (Poly.model k N - C x * Poly.model k E) := fun hc =>
    hs.not_isUnit (hc.isUnit_of_dvd' h1 h2)
  have zero : Polynomial.resultant (Poly.model k B) (Poly.model k N - C x * Poly.model k E) = 0 :=
    resultant_eq_zero_iff.mpr ⟨Or.inl hB.model_ne_zero, nc⟩
  rw [IsRoot.def, eval_resPoly dN dB dE, padded _ _ (degree_shift_le N E x), zero, mul_zero]

/-! ### Cauchy's estimate -/

/-- The rational polynomial that a list of coefficients denotes, lowest degree first. -/
noncomputable def qmodel : List ℚ → ℚ[X]
  | [] => 0
  | c :: cs => C c + X * qmodel cs

theorem qmodel_nil : qmodel [] = 0 := rfl

theorem qmodel_cons (c : ℚ) (cs : List ℚ) : qmodel (c :: cs) = C c + X * qmodel cs := rfl

/-- A coefficient list that denotes zero has only vanishing coefficients. -/
theorem eq_zero_of_qmodel_eq_zero : ∀ {p : List ℚ}, qmodel p = 0 → ∀ c ∈ p, c = 0
  | [], _ => by simp
  | c :: cs, h => by
    rw [qmodel_cons] at h
    have c0 : c = 0 := by simpa using congrArg (fun p : ℚ[X] => p.coeff 0) h
    have rest : qmodel cs = 0 := by
      ext i
      simpa using congrArg (fun p : ℚ[X] => p.coeff (i + 1)) h
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact c0
    · exact eq_zero_of_qmodel_eq_zero rest d hd

/-- `absQ` is the absolute value. -/
theorem absQ_eq (q : ℚ) : absQ q = |q| := by
  rw [absQ]
  split
  · rename_i h
    exact (abs_of_neg (show q < 0 from h)).symm
  · rename_i h
    exact (abs_of_nonneg (not_lt.mp (show ¬ q < 0 from h))).symm

/-- Trimming keeps the polynomial. -/
theorem qmodel_trimQ : ∀ p : List ℚ, qmodel (trimQ p) = qmodel p
  | [] => rfl
  | c :: cs => by
    have ih := qmodel_trimQ cs
    rw [trimQ]
    split
    · rename_i h
      rw [List.isEmpty_iff.mp h, qmodel_nil] at ih
      split
      · rename_i hc
        have c0 : c = 0 := by simpa using hc
        simp [qmodel_cons, qmodel_nil, ← ih, c0]
      · simp [qmodel_cons, qmodel_nil, ← ih]
    · rw [qmodel_cons, qmodel_cons, ih]

/-- The last coefficient of a trimmed list is not zero. -/
theorem trimQ_last_ne_zero : ∀ (p init : List ℚ) (l : ℚ), trimQ p = init ++ [l] → l ≠ 0
  | [], init, l, h => by simp [trimQ] at h
  | c :: cs, init, l, h => by
    rw [trimQ] at h
    split at h
    · split at h
      · simp at h
      · rename_i hc
        cases init with
        | nil =>
          have : c = l := by simpa using h
          rw [← this]
          simpa using hc
        | cons a init => simp at h
    · rename_i ne
      cases init with
      | nil =>
        have : trimQ cs = [] := by simpa using (List.cons.inj h).2
        simp [this] at ne
      | cons a init => exact trimQ_last_ne_zero cs init l (List.cons.inj h).2

theorem eval_qmodel_append (init : List ℚ) (l x : ℚ) :
    (qmodel (init ++ [l])).eval x = (qmodel init).eval x + x ^ init.length * l := by
  induction init with
  | nil => simp [qmodel_cons, qmodel_nil]
  | cons c cs ih =>
    simp only [List.cons_append, qmodel_cons, eval_add, eval_mul, eval_C, eval_X, ih,
      List.length_cons, pow_succ]
    ring

/-- At a point `x ≥ 1` the value of a polynomial is bounded by the sum of the absolute values
of its coefficients times a power of `x`. -/
theorem abs_eval_qmodel_mul_le {x : ℚ} (hx : 1 ≤ x) : ∀ cs : List ℚ,
    |(qmodel cs).eval x| * x ≤ (cs.map absQ).sum * x ^ cs.length
  | [] => by simp [qmodel_nil]
  | c :: cs => by
    have ih := abs_eval_qmodel_mul_le hx cs
    have x0 : 0 ≤ x := le_trans zero_le_one hx
    have h1 : |c + x * (qmodel cs).eval x| ≤ |c| + x * |(qmodel cs).eval x| := by
      calc
        _ ≤ |c| + |x * (qmodel cs).eval x| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg x0]
    have h2 : |c| * x ≤ |c| * x ^ (cs.length + 1) :=
      mul_le_mul_of_nonneg_left (le_self_pow₀ hx (Nat.succ_ne_zero _)) (abs_nonneg c)
    simp only [qmodel_cons, eval_add, eval_mul, eval_C, eval_X, List.map_cons, List.sum_cons,
      List.length_cons, absQ_eq]
    calc
      _ ≤ (|c| + x * |(qmodel cs).eval x|) * x := mul_le_mul_of_nonneg_right h1 x0
      _ = |c| * x + x * (|(qmodel cs).eval x| * x) := by ring
      _ ≤ |c| * x ^ (cs.length + 1) + x * ((cs.map absQ).sum * x ^ cs.length) :=
        add_le_add h2 (mul_le_mul_of_nonneg_left ih x0)
      _ = _ := by ring

/-- Cauchy's estimate: a natural number that is a root of a nonzero rational polynomial is at
most `radius` of its coefficient list. -/
theorem le_radius {p : List ℚ} (hp : qmodel p ≠ 0) {m : ℕ} (hm : (qmodel p).IsRoot (m : ℚ)) :
    m ≤ radius p := by
  rcases Nat.eq_zero_or_pos m with rfl | pos
  · exact Nat.zero_le _
  rcases List.eq_nil_or_concat (trimQ p) with e | ⟨init, l, e⟩
  · exact (hp (by rw [← qmodel_trimQ, e, qmodel_nil])).elim
  rw [List.concat_eq_append] at e
  have hl : 0 < |l| := abs_pos.mpr (trimQ_last_ne_zero p init l e)
  have hx : (1 : ℚ) ≤ m := by exact_mod_cast pos
  have xpos : (0 : ℚ) < (m : ℚ) ^ init.length := pow_pos (lt_of_lt_of_le zero_lt_one hx) _
  have root : (qmodel init).eval (m : ℚ) + (m : ℚ) ^ init.length * l = 0 := by
    rw [← eval_qmodel_append, ← e, qmodel_trimQ]
    exact hm
  have habs : |(qmodel init).eval (m : ℚ)| = (m : ℚ) ^ init.length * |l| := by
    rw [eq_neg_of_add_eq_zero_left root, abs_neg, abs_mul, abs_of_pos xpos]
  have bound := abs_eval_qmodel_mul_le hx init
  rw [habs] at bound
  have le : |l| * (m : ℚ) ≤ (init.map absQ).sum := by
    apply le_of_mul_le_mul_right _ xpos
    calc
      _ = (m : ℚ) ^ init.length * |l| * m := by ring
      _ ≤ _ := bound
  have key : (m : ℚ) ≤ 1 + (init.map absQ).sum / absQ l := by
    rw [absQ_eq]
    have : (m : ℚ) ≤ (init.map absQ).sum / |l| := (le_div_iff₀ hl).mpr (by linarith)
    linarith
  have run : radius p = (1 + (init.map absQ).sum / absQ l).ceil.toNat := by
    simp [radius, e, List.sum_eq_foldl]
  rw [run]
  have cast : ((m : ℤ) : ℚ) ≤ ((1 + (init.map absQ).sum / absQ l).ceil : ℚ) := by
    push_cast
    exact key.trans Rat.le_ceil
  have : (m : ℤ) ≤ (1 + (init.map absQ).sum / absQ l).ceil := by exact_mod_cast cast
  omega

/-! ### Rational slices -/

/-- The combination of the polynomials of a list with the powers of a rational number. -/
def evalNums (q : ℚ) : List (MPoly n) → MPoly n
  | [] => []
  | w :: ws => MPoly.add w (MPoly.mul (MPoly.scalar q) (evalNums q ws))

theorem asPoly_evalNums_map (q : ℚ) (g : MPoly n) : ∀ ws : List (MPoly n),
    asPoly (evalNums q (ws.map fun w => MPoly.mul w g)) = asPoly (evalNums q ws) * asPoly g
  | [] => by simp [evalNums]
  | w :: ws => by
    rw [List.map_cons, evalNums, evalNums, asPoly_add, asPoly_add, asPoly_mul, asPoly_mul,
      asPoly_mul, asPoly_evalNums_map q g ws]
    ring

/-- The numerators of the coefficients of a polynomial, combined with the powers of a
rational number, denote the value of the polynomial at that number times the common
denominator, which does not vanish. -/
theorem numerators_eval : ∀ {cs : Poly n}, Poly.Defined k cs →
    specialize (gens k n) (asPoly (numerators cs).2) ≠ 0 ∧ ∀ q : ℚ,
      specialize (gens k n) (asPoly (evalNums q (numerators cs).1)) =
        (Poly.model k cs).eval (q : K k n) * specialize (gens k n) (asPoly (numerators cs).2)
  | [], _ => by
    refine ⟨by simp [numerators], fun q => ?_⟩
    simp [numerators, evalNums, Poly.model_nil]
  | c :: cs, h => by
    obtain ⟨dn, ev⟩ := numerators_eval (cs := cs) fun e he => h e (List.mem_cons_of_mem _ he)
    obtain ⟨fe, fn⟩ := Term.fraction_spec (gens k n) c (h c List.mem_cons_self)
    change specialize (gens k n) (asPoly c.fraction.1) =
      Term.value k c * specialize (gens k n) (asPoly c.fraction.2) at fe
    refine ⟨by simp only [numerators, asPoly_mul, map_mul]; exact mul_ne_zero fn dn, fun q => ?_⟩
    have cq : specialize (gens k n) (asPoly (MPoly.scalar q : MPoly n)) = (q : K k n) := by simp
    simp only [numerators, evalNums, asPoly_add, asPoly_mul, asPoly_evalNums_map, map_add,
      map_mul, cq, ev q, Poly.model_cons, eval_add, eval_mul, eval_C, eval_X, fe]
    ring

/-- The value of a slice at a rational number is the coefficient of its monomial in the
combination of the polynomials with the powers of that number. -/
theorem eval_slice (μ : Mono n) (q : ℚ) : ∀ ws : List (MPoly n),
    (qmodel (slice μ ws)).eval q = (asPoly (evalNums q ws)).coeff (exps μ)
  | [] => by simp [slice, qmodel_nil, evalNums]
  | w :: ws => by
    have ih := eval_slice μ q ws
    rw [slice] at ih
    rw [slice, List.map_cons, qmodel_cons, eval_add, eval_mul, eval_C, eval_X, ih, evalNums,
      asPoly_add, asPoly_mul, asPoly_scalar, AddMonoidAlgebra.coeff_add]
    change _ = (asPoly w).coeff (exps μ) +
      (MvPolynomial.C q * asPoly (evalNums q ws)).coeff (exps μ)
    rw [MvPolynomial.coeff_C_mul, asPoly_coeff, asPoly_coeff]

/-- The slice of a monomial with a nonzero coefficient in some polynomial is not zero. -/
theorem slice_ne_zero (μ : Mono n) {ws : List (MPoly n)} (h : ∃ w ∈ ws, MPoly.coeff μ w ≠ 0) :
    qmodel (slice μ ws) ≠ 0 := by
  obtain ⟨w, hw, nz⟩ := h
  exact fun z => nz (eq_zero_of_qmodel_eq_zero z _ (List.mem_map.mpr ⟨w, hw, rfl⟩))

/-- The monomial found has a nonzero coefficient in some polynomial of the list. -/
theorem pick_sound {ws : List (MPoly n)} {μ : Mono n} (h : pick ws = some μ) :
    ∃ w ∈ ws, MPoly.coeff μ w ≠ 0 := by
  obtain ⟨w, hw, hf⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hf
  exact ⟨w, hw, by simpa using List.find?_some ht⟩

/-- A monomial is found when some polynomial of the list is not zero. -/
theorem pick_isSome {ws : List (MPoly n)} (h : ∃ w ∈ ws, asPoly w ≠ 0) : (pick ws).isSome := by
  obtain ⟨w, hw, nz⟩ := h
  by_contra hn
  have none : pick ws = none := by simpa using hn
  have all := List.findSome?_eq_none_iff.mp none w hw
  apply nz
  apply (MPoly.isZero_iff w).mp
  rw [MPoly.isZero, List.all_eq_true]
  intro t ht
  have := List.find?_eq_none.mp (Option.map_eq_none_iff.mp all) t ht
  simpa using this

theorem asPoly_evalNums_zero (q : ℚ) : ∀ {ws : List (MPoly n)},
    (∀ w ∈ ws, asPoly w = 0) → asPoly (evalNums q ws) = 0
  | [], _ => by simp [evalNums]
  | w :: ws, h => by
    rw [evalNums, asPoly_add, asPoly_mul, h w List.mem_cons_self,
      asPoly_evalNums_zero q fun v hv => h v (List.mem_cons_of_mem _ hv)]
    simp

/-- A natural number that is a root of a nonzero polynomial over the field of a tower is at
most `rootBound` of its coefficient list. -/
theorem le_rootBound {P : Poly n} (hP : Poly.Defined k P) (nz : Poly.model k P ≠ 0) {j : ℕ}
    (root : (Poly.model k P).IsRoot (j : K k n)) : j ≤ rootBound P := by
  obtain ⟨dn, ev⟩ := numerators_eval hP
  have inj := specialize_injective k n
  have some : (pick (numerators P).1).isSome := by
    apply pick_isSome
    by_contra hall
    have all : ∀ w ∈ (numerators P).1, asPoly w = 0 := by
      intro w hw
      by_contra hne
      exact hall ⟨w, hw, hne⟩
    apply nz
    apply eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun q : ℚ => (q : K k n))
      Rat.cast_injective fun q => ?_
    have := ev q
    rw [asPoly_evalNums_zero q all, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right dn
  obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.mp some
  rw [rootBound, hμ]
  apply le_radius (slice_ne_zero μ (pick_sound hμ))
  have zero := ev (j : ℚ)
  rw [Rat.cast_natCast, show (Poly.model k P).eval (j : K k n) = 0 from root, zero_mul] at zero
  have z2 : asPoly (evalNums (j : ℚ) (numerators P).1) = 0 := inj (zero.trans (map_zero _).symm)
  rw [IsRoot.def, eval_slice, z2]
  rfl

/-- A natural number `j` for which some prime factor of `B` divides `N - j E` is at most
`residueBound N B E`, when `N` and `B` are coprime. -/
theorem le_residueBound {N B E : Poly n} (hN : Poly.Defined k N) (hB : Poly.Defined k B)
    (hE : Poly.Defined k E) (nB : Poly.Normal k B)
    (cop : IsCoprime (Poly.model k N) (Poly.model k B)) {s : (K k n)[X]} (hs : Prime s)
    (h1 : s ∣ Poly.model k B) {j : ℕ}
    (h2 : s ∣ Poly.model k N - Polynomial.C (j : K k n) * Poly.model k E) :
    j ≤ residueBound N B E :=
  le_rootBound (defined_resPoly hN hB hE) (resPoly_ne_zero N E hN hB hE nB cop)
    (root_of_residue N E hN hB hE nB hs h1 _ h2)

end Resultant

end SympyProofs.Calculus.Risch
