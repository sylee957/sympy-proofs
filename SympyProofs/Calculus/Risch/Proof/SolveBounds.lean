module

public import SympyProofs.Calculus.Risch.Proof.SolvePieces
public import SympyProofs.Calculus.Risch.Proof.Pole
public import SympyProofs.Calculus.Risch.Proof.Resultant
public import SympyProofs.Calculus.Risch.Proof.Constants
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The two bounds of part (b) of the Main Theorem at a tower step (Risch 1969, pp. 184–187):
a denominator for every solution of `y′ + f y = Σ cᵢ gᵢ`, and a bound on the degree of the
numerator.

The equation is cleared to `R Y′ + S Y = Σ cᵢ Gᵢ` by `pieces`. The denominator is a product of
the denominator of the right-hand sides, a power of the denominator of `f` given by the bound
on integral residues, and at an exponential step a power of the generator.

At a primitive step a solution of degree beyond that of the right-hand side makes the two
highest coefficients of the left-hand side cancel. Then the ratio of its two leading
coefficients is a primitive of a known element up to a multiple of the derivative of the
generator, and that multiple is the degree. Part (b) in the preceding field finds it.

At an exponential step a pole of a solution at the generator, and a degree of its numerator,
beyond what the right-hand sides allow make an element `A` of the preceding field with
`A′/A = g + m u′` for a known `g`, where `m` is the order or the degree in question. The
integer `m` is bounded by `exponentBound`, read off the linear system of `relRows`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial Linear

noncomputable local instance intAlgebraSolveBounds {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

/-! ### The integer in a logarithmic derivative -/

namespace Rel

/-- The exponent of a system with one more row. -/
theorem exponent_cons (r : List ℚ) (rows : List (List ℚ)) :
    exponent (r :: rows) = if r.getD 1 0 == 0 then exponent rows
      else max (exponent rows) (-(r.getD 0 0) / r.getD 1 0).ceil.toNat := rfl

/-- Every row with a nonzero second entry contributes to the exponent. -/
theorem le_exponent : ∀ {rows : List (List ℚ)} {r : List ℚ}, r ∈ rows → r.getD 1 0 ≠ 0 →
    (-(r.getD 0 0) / r.getD 1 0).ceil.toNat ≤ exponent rows
  | r' :: rows, r, hr, h1 => by
    rw [exponent_cons]
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [ite_eq_right (by simpa using h1)]
      exact le_max_right _ _
    · have ih := le_exponent hr h1
      split
      · exact ih
      · exact ih.trans (le_max_left _ _)

omit [CharZero k] in
/-- A row applied to a vector of two entries. -/
theorem dotK_pair (r : List ℚ) (a b : k) :
    Linear.dotK r [a, b] = ((r.getD 0 0 : ℚ) : k) * a + ((r.getD 1 0 : ℚ) : k) * b := by
  rw [Linear.dotK_eq_sum]
  simp [Finset.sum_range_succ]

/-- When the test `expOk` succeeds, the derivative of the exponent does not lie in the space
that contains the logarithmic derivatives. -/
theorem not_rel_of_expOk {t : Tower n} {u : Term n} (ht : t.Admissible k)
    (hu : Term.InDomain k u) (ok : Rel.expOk t u = true) :
    ¬ Tower.Rel k t (t.der k (Term.value k u)) := by
  intro rel
  have hw : ∀ w ∈ [t.D u], Term.InDomain k w := by
    intro w hw
    rw [List.mem_singleton.mp hw]
    exact Tower.inDomain_D ht hu
  have rows := (relRows_spec t ht hw [1] rfl).mp (by
    rw [linComb_cons, linComb_nil_left, map_one, one_mul, add_zero, ← Tower.der_value]
    exact rel)
  rw [expOk, List.any_eq_true] at ok
  obtain ⟨r, hr, ne⟩ := ok
  have c := dotK_cast (k := k) r [1]
  rw [List.map_cons, List.map_nil, Rat.cast_one, rows r hr] at c
  have z : dot r [1] = 0 := by exact_mod_cast c.symm
  simp [z] at ne

/-- When the test `expOk` succeeds, the exponential of `u` is admissible over an admissible
tower in which `u` is defined. -/
theorem exp_admissible {t : Tower n} {u : Term n} (ht : t.Admissible k)
    (hu : Term.InDomain k u) (ok : Rel.expOk t u = true) : (t.exp u).Admissible k := by
  refine ⟨ht, hu, ?_⟩
  rintro ⟨m, v, mpos, vne, e⟩
  apply not_rel_of_expOk ht hu ok
  have rel := (Tower.rel_logDeriv t vne).const_mul ((m : k)⁻¹)
  rw [e, map_inv₀, map_natCast, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr mpos.ne'), one_mul] at rel
  exact rel

/-- An integer `m` for which `g + m u′` is a logarithmic derivative is at most
`exponentBound t u g`. -/
theorem exponentBound_spec {t : Tower n} {u g : Term n} (ht : t.Admissible k)
    (hu : Term.InDomain k u) (ok : Rel.expOk t u = true) (hg : Term.InDomain k g) {m : ℤ}
    {A : K k n} (hA : A ≠ 0)
    (eA : t.der k A = (Term.value k g + (m : K k n) * t.der k (Term.value k u)) * A) :
    m ≤ (Rel.exponentBound t u g : ℤ) := by
  have hw : ∀ w ∈ [g, t.D u], Term.InDomain k w := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hg
    · rw [List.mem_singleton.mp hw]
      exact Tower.inDomain_D ht hu
  have spec (α : List k) (hα : α.length = 2) := relRows_spec t ht hw α hα
  have lin (a b : k) : linComb [a, b] [g, t.D u] =
      constHom k n a * Term.value k g + constHom k n b * t.der k (Term.value k u) := by
    rw [linComb_cons, linComb_cons, linComb_nil_left, add_zero, Tower.der_value]
  have rows1 := (spec [1, (m : k)] rfl).mp (by
    rw [lin, map_one, one_mul, map_intCast]
    have := Tower.rel_logDeriv t hA
    rwa [eA, mul_div_assoc, div_self hA, mul_one] at this)
  have ex : ∃ r ∈ relRows t [g, t.D u], r.getD 1 0 ≠ 0 := by
    by_contra hne
    push Not at hne
    apply not_rel_of_expOk ht hu ok
    have := (spec [0, 1] rfl).mpr fun row hrow => by
      rw [dotK_pair, hne row hrow]
      simp
    rwa [lin, map_zero, zero_mul, zero_add, map_one, one_mul] at this
  obtain ⟨r, hr, h1⟩ := ex
  have e := rows1 r hr
  rw [dotK_pair, mul_one] at e
  have h1k : ((r.getD 1 0 : ℚ) : k) ≠ 0 := Rat.cast_ne_zero.mpr h1
  have hm : (m : ℚ) = -(r.getD 0 0) / r.getD 1 0 := by
    apply Rat.cast_injective (α := k)
    rw [Rat.cast_intCast, Rat.cast_div, Rat.cast_neg, eq_div_iff h1k]
    linear_combination e
  have c1 : m ≤ (-(r.getD 0 0) / r.getD 1 0).ceil := by
    rw [← hm, Rat.ceil_intCast]
  exact c1.trans ((Int.self_le_toNat _).trans (by exact_mod_cast le_exponent hr h1))

end Rel

namespace Solve

local notation "ι" => algebraMap (K k n)[X] (RatFunc (K k n))

/-! ### The cleared equation -/

private theorem model_one : Poly.model k ([.const 1] : Poly n) = 1 := by
  simp [Poly.model_cons, Poly.model_nil, Term.value_const]

private theorem defined_one : Poly.Defined k ([.const 1] : Poly n) := fun e he => by
  rw [List.mem_singleton.mp he]
  trivial

/-- The power of a coefficient list denotes the power of the polynomial. -/
theorem model_ppow (B : Poly n) : ∀ m, Poly.model k (ppow B m) = Poly.model k B ^ m
  | 0 => by rw [ppow, model_one, pow_zero]
  | m + 1 => by rw [ppow, Poly.model_mul, model_ppow B m, pow_succ]

/-- The powers of a defined coefficient list are defined. -/
theorem defined_ppow {B : Poly n} (hB : Poly.Defined k B) : ∀ m, Poly.Defined k (ppow B m)
  | 0 => defined_one
  | m + 1 => Poly.defined_mul (defined_ppow hB m) hB

/-- The equation `y′ + (N/B) y = H/T` for `y = Y/P` is the polynomial equation
`R Y′ + S Y = H P² B` with `R = P B T` and `S = T (N P - B P′)`. -/
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
    field_simp
    linear_combination he'
  · intro he
    apply RatFunc.algebraMap_injective (K k n)
    simp only [map_mul, map_add, map_sub]
    field_simp at he
    linear_combination he

/-- The cleared data of an instance satisfy their specification, with the exponent of the
generator in the denominator given by `special`. -/
theorem pieces_spec {t : Tower (n + 1)} (ht : t.Admissible k) {f : Term (n + 1)}
    {gs : List (Term (n + 1))} (hf : Term.InDomain k f) (hg : ∀ g ∈ gs, Term.InDomain k g) :
    PiecesSpec k t f gs
      (special t (pieces t f gs).N (pieces t f gs).B (pieces t f gs).T) (pieces t f gs) := by
  obtain ⟨fe, fn⟩ := Poly.ofTerm_spec f hf
  obtain ⟨dp, dq⟩ := Poly.ofTerm_defined (k := k) f
  have qn : Poly.model k (Poly.ofTerm f).2 ≠ 0 := fun z => fn (by rw [z, map_zero])
  obtain ⟨dN0, dB0, nB0, cop, ratio⟩ := Poly.reduce_spec dp dq qn
  obtain ⟨N, hN⟩ : ∃ N, N = Poly.norm (Poly.reduce (Poly.ofTerm f).1 (Poly.ofTerm f).2).1 :=
    ⟨_, rfl⟩
  have dN : Poly.Defined k N := by
    rw [hN]
    exact Poly.defined_norm dN0
  have mN : Poly.model k N =
      Poly.model k (Poly.reduce (Poly.ofTerm f).1 (Poly.ofTerm f).2).1 := by
    rw [hN]
    exact Poly.model_norm dN0
  obtain ⟨mB1, dB1, nrm, -⟩ := Poly.trim_spec (Poly.defined_norm dB0)
  obtain ⟨B, hB⟩ : ∃ B, B =
    Poly.trim (Poly.norm (Poly.reduce (Poly.ofTerm f).1 (Poly.ofTerm f).2).2) := ⟨_, rfl⟩
  rw [← hB] at mB1 dB1 nrm
  have mB : Poly.model k B =
      Poly.model k (Poly.reduce (Poly.ofTerm f).1 (Poly.ofTerm f).2).2 :=
    mB1.trans (Poly.model_norm dB0)
  rw [← mN, ← mB] at cop ratio
  have Bn : Poly.model k B ≠ 0 := by
    rw [mB]
    exact nB0
  have nB : Poly.Normal k B := nrm.resolve_left fun h => Bn (by rw [h, Poly.model_nil])
  obtain ⟨dT0, nT0, dW0, len0, comb0⟩ := Poly.commonDen_spec hg
  obtain ⟨T, hT⟩ : ∃ T, T = Poly.norm (Poly.commonDen gs).2 := ⟨_, rfl⟩
  have dT : Poly.Defined k T := by
    rw [hT]
    exact Poly.defined_norm dT0
  have mT : Poly.model k T = Poly.model k (Poly.commonDen gs).2 := by
    rw [hT]
    exact Poly.model_norm dT0
  have nT : Poly.model k T ≠ 0 := by
    rw [mT]
    exact nT0
  obtain ⟨Ws, hWs⟩ : ∃ Ws, Ws = (Poly.commonDen gs).1.map Poly.norm := ⟨_, rfl⟩
  have dW : ∀ W ∈ Ws, Poly.Defined k W := by
    intro W hW
    rw [hWs] at hW
    obtain ⟨W', hW', rfl⟩ := List.mem_map.mp hW
    exact Poly.defined_norm (dW0 W' hW')
  have lenW : Ws.length = gs.length := by rw [hWs, List.length_map, len0]
  have combW (c : List k) : pcomb c Ws = pcomb c (Poly.commonDen gs).1 := by
    rw [hWs]
    have := pcomb_map_congr Poly.norm (fun W => W) (Poly.commonDen gs).1 c
      (fun W hW => Poly.model_norm (dW0 W hW))
    rwa [List.map_id'] at this
  have dP0 : Poly.Defined k (Poly.mul (Poly.mono (special t N B T) (.const 1))
      (Poly.mul T (ppow B (Resultant.residueBound N B (Poly.der t B))))) :=
    Poly.defined_mul (Poly.defined_mono _ trivial) (Poly.defined_mul dT (defined_ppow dB1 _))
  obtain ⟨P, hP⟩ : ∃ P, P = Poly.norm (Poly.mul (Poly.mono (special t N B T) (.const 1))
    (Poly.mul T (ppow B (Resultant.residueBound N B (Poly.der t B))))) := ⟨_, rfl⟩
  have dP : Poly.Defined k P := by
    rw [hP]
    exact Poly.defined_norm dP0
  have Pval : Poly.model k P = X ^ special t N B T *
      (Poly.model k T * Poly.model k B ^ Resultant.residueBound N B (Poly.der t B)) := by
    rw [hP, Poly.model_norm dP0, Poly.model_mul, Poly.model_mul, model_ppow, Poly.model_mono,
      Term.value_const, Rat.cast_one, C_1, one_mul]
  have Pn : Poly.model k P ≠ 0 := by
    rw [Pval]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (mul_ne_zero nT (pow_ne_zero _ Bn))
  have dA : Poly.Defined k (Poly.mul P (Poly.mul B T)) :=
    Poly.defined_mul dP (Poly.defined_mul dB1 dT)
  have dBc : Poly.Defined k (Poly.mul T
      (Poly.sub (Poly.mul N P) (Poly.mul B (Poly.der t P)))) :=
    Poly.defined_mul dT (Poly.defined_sub (Poly.defined_mul dN dP)
      (Poly.defined_mul dB1 (Poly.defined_der ht dP)))
  obtain ⟨mR, dR, nR, -⟩ := Poly.trim_spec (Poly.defined_norm dA)
  obtain ⟨mS, dS, nS, -⟩ := Poly.trim_spec (Poly.defined_norm dBc)
  obtain ⟨R, hR⟩ : ∃ R, R = Poly.trim (Poly.norm (Poly.mul P (Poly.mul B T))) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = Poly.trim (Poly.norm (Poly.mul T
    (Poly.sub (Poly.mul N P) (Poly.mul B (Poly.der t P))))) := ⟨_, rfl⟩
  rw [← hR] at mR dR nR
  rw [← hS] at mS dS nS
  have Rval : Poly.model k R = Poly.model k P * (Poly.model k B * Poly.model k T) := by
    rw [mR, Poly.model_norm dA, Poly.model_mul, Poly.model_mul]
  have Sval : Poly.model k S = Poly.model k T *
      (Poly.model k N * Poly.model k P - Poly.model k B * Tower.polyDer k t (Poly.model k P)) := by
    rw [mS, Poly.model_norm dBc, Poly.model_mul, Poly.model_sub, Poly.model_mul, Poly.model_mul,
      Poly.model_der]
  have Rn : Poly.model k R ≠ 0 := by
    rw [Rval]
    exact mul_ne_zero Pn (mul_ne_zero Bn nT)
  have normR : Poly.Normal k R := nR.resolve_left fun h => Rn (by rw [h, Poly.model_nil])
  have dE0 : Poly.Defined k (Poly.mul (Poly.mul P P) B) :=
    Poly.defined_mul (Poly.defined_mul dP dP) dB1
  obtain ⟨E, hE⟩ : ∃ E, E = Poly.norm (Poly.mul (Poly.mul P P) B) := ⟨_, rfl⟩
  have dE : Poly.Defined k E := by
    rw [hE]
    exact Poly.defined_norm dE0
  have mE : Poly.model k E = Poly.model k P * Poly.model k P * Poly.model k B := by
    rw [hE, Poly.model_norm dE0, Poly.model_mul, Poly.model_mul]
  have key : PiecesSpec k t f gs (special t N B T) ⟨N, B, T, P, R, S, Ws,
      Ws.map (fun W => Poly.norm (Poly.mul W E)), max (R.length - 1) (S.length - 1)⟩ := by
    refine
      { dN := dN, dB := dB1, dP := dP, nB := nB, cop := cop, nT := nT, Pval := Pval, Rval := Rval,
        Sval := Sval, fval := ?_, dG := ?_, lenG := by simp [lenW], comb := ?_, Gval := ?_,
        good := ?_ }
    · have Bn' := RatFunc.algebraMap_ne_zero Bn
      have r' := congrArg ι ratio
      simp only [map_mul] at r'
      rw [eq_div_iff Bn']
      apply mul_right_cancel₀ fn
      rw [fe] at r'
      linear_combination r'
    · intro G hG
      obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hG
      exact Poly.defined_norm (Poly.defined_mul (dW W hW) dE)
    · intro c
      change _ = ι (pcomb c Ws) / ι (Poly.model k T)
      rw [combW c, mT]
      exact comb0 c
    · intro c
      change pcomb c (Ws.map fun W => Poly.norm (Poly.mul W E)) = _
      rw [pcomb_map_congr _ (fun W => Poly.mul W E) Ws c
        (fun W hW => Poly.model_norm (Poly.defined_mul (dW W hW) dE)), ← mE]
      exact pcombK_map_mul E Ws c
    · refine ⟨ht, dR, dS, ?_, ?_, ?_⟩
      · exact (Poly.natDegree_model_le _).trans (le_max_left _ _)
      · exact (Poly.natDegree_model_le _).trans (le_max_right _ _)
      · rcases nS with eS | normS
        · left
          rw [eS]
          simp only [List.length_nil, Nat.zero_sub, Nat.zero_le, max_eq_left]
          rw [← Poly.value_lead]
          exact normR
        · rcases le_total (R.length - 1) (S.length - 1) with le | le
          · right
            rw [max_eq_right le, ← Poly.value_lead]
            exact normS
          · left
            rw [max_eq_left le, ← Poly.value_lead]
            exact normR
  subst hE hS hR hP hWs hT hB hN
  exact key

/-! ### The denominator -/

/-- At a primitive step the denominator of every solution divides the computed one. -/
theorem prim_denominator {t : Tower n} {b : Term n} (ht : (t.prim b).Admissible k)
    {f : Term (n + 1)} {gs : List (Term (n + 1))} (hf : Term.InDomain k f)
    (hg : ∀ g ∈ gs, Term.InDomain k g) (y : K k (n + 1)) (c : List k)
    (eqn : (t.prim b).der k y + Term.value k f * y = linComb c gs) :
    y.denom ∣ Poly.model k (pieces (t.prim b) f gs).P := by
  have ps := pieces_spec ht hf hg
  obtain ⟨pc, hpc⟩ : ∃ pc, pc = pieces (t.prim b) f gs := ⟨_, rfl⟩
  rw [← hpc] at ps ⊢
  have Bn : Poly.model k pc.B ≠ 0 := ps.nB.model_ne_zero
  have eq0 : Pole.Equation (Tower.polyDer k (t.prim b)) (Poly.model k pc.N) (Poly.model k pc.B)
      (pcomb c pc.Ws) (Poly.model k pc.T) y.num y.denom :=
    (Pole.equation_iff (t.prim b) Bn ps.nT y.denom_ne_zero).mpr (by
      rw [RatFunc.num_div_denom, ← ps.fval, ← ps.comb]
      exact eqn)
  have dv := Pole.denominator_dvd (Tower.polyDer k (t.prim b))
    (fun s hs => Pole.prim_normal ht hs) Bn ps.nT y.denom_ne_zero
    y.isCoprime_num_denom.isRelPrime eq0
    (Resultant.residueBound pc.N pc.B (Poly.der (t.prim b) pc.B))
    (fun s m hs h1 h2 => Resultant.le_residueBound ps.dN ps.dB (Poly.defined_der ht ps.dB)
      ps.nB ps.cop hs h1 (by rw [Poly.model_der]; exact h2))
  rw [ps.Pval, special, pow_zero, one_mul]
  exact dv

/-- At an exponential step the denominator of every solution divides the computed one. -/
theorem exp_denominator {t : Tower n} {u : Term n} (ht : (t.exp u).Admissible k)
    (ok : Rel.expOk t u = true) {f : Term (n + 1)} {gs : List (Term (n + 1))}
    (hf : Term.InDomain k f) (hg : ∀ g ∈ gs, Term.InDomain k g) (y : K k (n + 1)) (c : List k)
    (eqn : (t.exp u).der k y + Term.value k f * y = linComb c gs) :
    y.denom ∣ Poly.model k (pieces (t.exp u) f gs).P := by
  have ps := pieces_spec ht hf hg
  obtain ⟨pc, hpc⟩ : ∃ pc, pc = pieces (t.exp u) f gs := ⟨_, rfl⟩
  rw [← hpc] at ps ⊢
  have Bn : Poly.model k pc.B ≠ 0 := ps.nB.model_ne_zero
  have eq0 : Pole.Equation (Tower.polyDer k (t.exp u)) (Poly.model k pc.N) (Poly.model k pc.B)
      (pcomb c pc.Ws) (Poly.model k pc.T) y.num y.denom :=
    (Pole.equation_iff (t.exp u) Bn ps.nT y.denom_ne_zero).mpr (by
      rw [RatFunc.num_div_denom, ← ps.fval, ← ps.comb]
      exact eqn)
  rw [ps.Pval]
  apply Pole.exp_denominator_dvd ht Bn ps.nT y.denom_ne_zero y.isCoprime_num_denom.isRelPrime eq0 _
    (fun s m hs h1 h2 => Resultant.le_residueBound ps.dN ps.dB (Poly.defined_der ht ps.dB)
      ps.nB ps.cop hs h1 (by rw [Poly.model_der]; exact h2))
  rw [special]
  rcases Pole.special_order ps.nT y.denom_ne_zero y.isCoprime_num_denom.isRelPrime ps.cop eq0
    with le | ⟨B0, A, hA, eA⟩
  · refine le.trans (le_trans ?_ (le_max_left _ _))
    have dv : X ^ multiplicity X (Poly.model k pc.T) ∣ Poly.model k pc.T :=
      pow_multiplicity_dvd _ _
    have deg := natDegree_le_of_dvd dv ps.nT
    rw [natDegree_X_pow] at deg
    exact deg.trans ((Poly.natDegree_model_le _).trans (Nat.sub_le _ _))
  · refine le_trans ?_ (le_max_right _ _)
    have dB0 : Term.InDomain k (Poly.coeff pc.B 0) := Poly.defined_coeff ps.dB 0
    have vB0 : Term.value k (Poly.coeff pc.B 0) ≠ 0 := by
      rw [Poly.value_coeff]
      exact B0
    have nz : ¬ (Poly.coeff pc.B 0).isZero = true := fun h => vB0 ((Term.isZero_iff dB0).mp h)
    rw [ite_eq_right nz]
    have hg' : Term.InDomain k
        (.neg (.div (Poly.coeff pc.N 0) (Poly.coeff pc.B 0)) : Term n) :=
      ⟨Poly.defined_coeff ps.dN 0, dB0, vB0⟩
    have := Rel.exponentBound_spec ht.1 ht.2.1 ok hg' (m := (multiplicity X y.denom : ℤ)) hA (by
      rw [eA]
      change _ = (-(Term.value k (Poly.coeff pc.N 0) / Term.value k (Poly.coeff pc.B 0)) +
        _) * A
      rw [Poly.value_coeff, Poly.value_coeff]
      push_cast
      ring)
    exact_mod_cast this

/-! ### The degree at an exponential step -/

/-- At an exponential step every polynomial solution has degree below the bound. -/
theorem exp_bound {t : Tower n} {u : Term n} (ht : (t.exp u).Admissible k)
    (ok : Rel.expOk t u = true) {R S : Poly n} {lam : ℕ} (g : Good k (t.exp u) R S lam)
    (lower : Term n → List (Term n) → List (Term n) × List (List ℚ)) {Gs : List (Poly n)}
    {p : List k} {Y : (K k n)[X]}
    (eq : L (t.exp u) (Poly.model k R) (Poly.model k S) Y = pcomb p Gs) :
    ∀ i, degBound (t.exp u) lower R S lam Gs ≤ i → Y.coeff i = 0 := by
  intro i hi
  by_cases Yz : Y = 0
  · rw [Yz, coeff_zero]
  apply coeff_eq_zero_of_natDegree_lt
  by_contra hge
  obtain ⟨a, ha⟩ : ∃ a, a = Y.natDegree := ⟨_, rfl⟩
  have big : degBound (t.exp u) lower R S lam Gs ≤ a := by omega
  rw [degBound] at big
  have base : maxLen Gs ≤ a := by
    split at big
    · exact big
    · exact (le_max_left _ _).trans big
  have Yne : Y.coeff a ≠ 0 := by
    rw [ha]
    exact leadingCoeff_ne_zero.mpr Yz
  have tw : Term.value k (t.exp u).twist = t.der k (Term.value k u) :=
    (Tower.der_value t u).symm
  have top := coeff_L_top (t.exp u) g.degR g.degS (le_of_eq ha.symm)
  rw [eq, coeff_pcomb_of_maxLen_le Gs p (by omega), tw] at top
  change 0 = (Poly.model k R).coeff lam * t.der k (Y.coeff a) + _ at top
  have dR := Poly.defined_coeff g.hR lam
  have dS := Poly.defined_coeff g.hS lam
  by_cases rz : (Poly.model k R).coeff lam = 0
  · rcases g.lead with h | h
    · exact h rz
    · rw [rz, zero_mul, mul_zero, zero_add, add_zero] at top
      exact (mul_ne_zero h Yne) top.symm
  · have vR : Term.value k (Poly.coeff R lam) ≠ 0 := by
      rw [Poly.value_coeff]
      exact rz
    have nz : ¬ (Poly.coeff R lam).isZero = true := fun h => vR ((Term.isZero_iff dR).mp h)
    rw [ite_eq_right nz] at big
    have hg' : Term.InDomain k (.div (Poly.coeff S lam) (Poly.coeff R lam) : Term n) :=
      ⟨dS, dR, vR⟩
    have := Rel.exponentBound_spec ht.1 ht.2.1 ok hg' (m := (a : ℤ)) (A := (Y.coeff a)⁻¹)
      (inv_ne_zero Yne) (by
        change _ = (Term.value k (Poly.coeff S lam) / Term.value k (Poly.coeff R lam) + _) * _
        rw [Poly.value_coeff, Poly.value_coeff, Derivation.leibniz_inv]
        simp only [smul_eq_mul]
        push_cast
        field_simp
        linear_combination top)
    have le : Rel.exponentBound t u (.div (Poly.coeff S lam) (Poly.coeff R lam)) + 1 ≤ a :=
      (le_max_right _ _).trans big
    omega

/-! ### The degree at a primitive step -/

/-- The coefficient just below the highest possible one of a product. -/
theorem coeff_mul_second {F : Type*} [Field F] {P Z : F[X]} {lam a : ℕ}
    (hP : P.natDegree ≤ lam) (hZ : Z.natDegree ≤ a + 1) :
    (P * Z).coeff (lam + a) =
      P.coeff lam * Z.coeff a + (if lam = 0 then 0 else P.coeff (lam - 1)) * Z.coeff (a + 1) := by
  cases lam with
  | zero =>
    rw [eq_C_of_natDegree_le_zero hP]
    simp
  | succ l =>
    obtain ⟨P₁, hP₁⟩ : ∃ P₁ : F[X], P₁ = P - C (P.coeff (l + 1)) * X ^ (l + 1) := ⟨_, rfl⟩
    have deg : P₁.natDegree ≤ l := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      rw [hP₁, coeff_sub, coeff_C_mul, coeff_X_pow]
      rcases (Nat.succ_le_of_lt hi).eq_or_lt with e | lt
      · rw [← e]
        simp
      · rw [coeff_eq_zero_of_natDegree_lt (hP.trans_lt lt), ite_eq_right (by omega)]
        simp
    have split : P = C (P.coeff (l + 1)) * X ^ (l + 1) + P₁ := by rw [hP₁]; ring
    have low : P₁.coeff l = P.coeff l := by
      rw [hP₁, coeff_sub, coeff_C_mul, coeff_X_pow, ite_eq_right (by omega)]
      simp
    have e1 : (C (P.coeff (l + 1)) * X ^ (l + 1) * Z).coeff (l + 1 + a) =
        P.coeff (l + 1) * Z.coeff a := by
      rw [mul_assoc, coeff_C_mul, add_comm (l + 1) a, coeff_X_pow_mul]
    have e2 : (P₁ * Z).coeff (l + 1 + a) = P.coeff l * Z.coeff (a + 1) := by
      rw [show l + 1 + a = l + (a + 1) by omega, coeff_mul_add_eq_of_natDegree_le deg hZ, low]
    conv_lhs => rw [split, add_mul, coeff_add, e1, e2]
    simp

/-- The value of the element that governs cancellation. -/
theorem value_cancelQ (R S : Poly n) (lam : ℕ) :
    Term.value k (cancelQ R S lam) =
      ((if lam = 0 then 0 else (Poly.model k R).coeff (lam - 1)) * (Poly.model k S).coeff lam -
        (Poly.model k R).coeff lam *
          (if lam = 0 then 0 else (Poly.model k S).coeff (lam - 1))) /
        ((Poly.model k R).coeff lam * (Poly.model k R).coeff lam) := by
  have low (A : Poly n) :
      Term.value k (if lam == 0 then (.const 0 : Term n) else Poly.coeff A (lam - 1)) =
        if lam = 0 then 0 else (Poly.model k A).coeff (lam - 1) := by
    by_cases h : lam = 0
    · subst h
      simp [Poly.value_zero]
    · simp [h, Poly.value_coeff]
  change (Term.value k _ * Term.value k (Poly.coeff S lam) -
    Term.value k (Poly.coeff R lam) * Term.value k _) /
      (Term.value k (Poly.coeff R lam) * Term.value k (Poly.coeff R lam)) = _
  rw [low R, low S, Poly.value_coeff, Poly.value_coeff]

/-- The element that governs cancellation is defined when the highest coefficient of `R`
does not vanish. -/
theorem inDomain_cancelQ {R S : Poly n} (hR : Poly.Defined k R) (hS : Poly.Defined k S)
    {lam : ℕ} (hr : (Poly.model k R).coeff lam ≠ 0) : Term.InDomain k (cancelQ R S lam) := by
  have rne : Term.value k (Poly.coeff R lam) ≠ 0 := by rwa [Poly.value_coeff]
  have low {A : Poly n} (hA : Poly.Defined k A) :
      Term.InDomain k (if lam == 0 then (.const 0 : Term n) else Poly.coeff A (lam - 1)) := by
    split
    · trivial
    · exact Poly.defined_coeff hA _
  exact ⟨⟨⟨low hR, Poly.defined_coeff hS lam⟩, Poly.defined_coeff hR lam, low hS⟩,
    ⟨Poly.defined_coeff hR lam, Poly.defined_coeff hR lam⟩, mul_ne_zero rne rne⟩

/-- If `Q - a b` has a primitive in the field and `b` has none, the program `third` finds the
natural number `a`. -/
theorem third_eq {t : Tower n}
    {lower : Term n → List (Term n) → List (Term n) × List (List ℚ)}
    (hl : SolveSpec k t lower) {b Q : Term n} (hb : Term.InDomain k b)
    (hQ : Term.InDomain k Q) (nonprim : ¬ ∃ v : K k n, t.der k v = Term.value k b) {a : ℕ}
    {v : K k n} (hv : t.der k v = Term.value k Q - (a : K k n) * Term.value k b) :
    third lower b Q = a := by
  have hf : Term.InDomain k (.const 0 : Term n) := trivial
  have hg : ∀ g ∈ [Q, b], Term.InDomain k g := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hQ
    · rw [List.mem_singleton.mp hg]
      exact hb
  have spec := (hl (.const 0) [Q, b] hf hg).2
  obtain ⟨sol, hsol⟩ : ∃ sol, sol = lower (.const 0) [Q, b] := ⟨_, rfl⟩
  rw [← hsol] at spec
  have comb (c₁ c₂ : k) : linComb [c₁, c₂] [Q, b] =
      constHom k n c₁ * Term.value k Q + constHom k n c₂ * Term.value k b := by
    rw [linComb_cons, linComb_cons, linComb_nil_left, add_zero]
  have first : t.der k v + Term.value k (.const 0 : Term n) * v =
      linComb [1, -(a : k)] [Q, b] := by
    rw [comb, hv, Poly.value_zero, map_one, map_neg, map_natCast]
    ring
  obtain ⟨d, dl, -, drows⟩ := (spec v [1, -(a : k)] rfl).mp first
  have some := normalized_complete (k := k) (rows := sol.2) (M := 2 + sol.1.length)
    ⟨1 :: -(a : k) :: d, by simp only [List.length_cons, dl]; omega, by simp, drows⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp some
  obtain ⟨xl, x0, xrows⟩ := normalized_sound hx
  obtain ⟨x₀, c, d', rfl⟩ : ∃ x₀ c d', x = x₀ :: c :: d' := by
    match x, xl with
    | x₀ :: c :: d', _ => exact ⟨x₀, c, d', rfl⟩
    | [_], h => simp at h; omega
    | [], h => simp at h; omega
  obtain rfl : x₀ = 1 := by simpa using x0
  have dl' : (d'.map fun (q : ℚ) => (q : k)).length = sol.1.length := by
    simp only [List.length_cons] at xl
    rw [List.length_map]
    omega
  have rows' : ∀ row ∈ sol.2,
      dotK row ([((1 : ℚ) : k), (c : k)] ++ d'.map fun (q : ℚ) => (q : k)) = 0 := by
    intro row hrow
    have := dotK_cast (k := k) row (1 :: c :: d')
    rw [xrows row hrow, Rat.cast_zero] at this
    exact this
  obtain ⟨y, hy⟩ : ∃ y, y = linComb (d'.map fun (q : ℚ) => (q : k)) sol.1 := ⟨_, rfl⟩
  have second := (spec y [((1 : ℚ) : k), (c : k)] rfl).mpr ⟨_, dl', hy, rows'⟩
  rw [comb, Poly.value_zero, zero_mul, add_zero, Rat.cast_one, map_one, one_mul] at second
  have diff : t.der k (v - y) = constHom k n (-(a : k) - (c : k)) * Term.value k b := by
    rw [map_sub, hv, second, map_sub, map_neg, map_natCast]
    ring
  have ez : -(a : k) - (c : k) = 0 := by
    by_contra ne
    apply nonprim
    refine ⟨constHom k n (-(a : k) - (c : k))⁻¹ * (v - y), ?_⟩
    rw [Derivation.leibniz, Tower.der_constHom, smul_zero, add_zero, smul_eq_mul, diff,
      ← mul_assoc, ← map_mul, inv_mul_cancel₀ ne, map_one, one_mul]
  have ce : -c = (a : ℚ) := by
    apply Rat.cast_injective (α := k)
    push_cast
    linear_combination ez
  simp only [third]
  rw [← hsol, hx]
  simp [ce]

/-- At a primitive step every polynomial solution has degree below the bound. -/
theorem prim_bound {t : Tower n} {b : Term n} (ht : (t.prim b).Admissible k) {R S : Poly n}
    {lam : ℕ} (g : Good k (t.prim b) R S lam)
    {lower : Term n → List (Term n) → List (Term n) × List (List ℚ)}
    (hl : SolveSpec k t lower) {Gs : List (Poly n)} {p : List k} {Y : (K k n)[X]}
    (eq : L (t.prim b) (Poly.model k R) (Poly.model k S) Y = pcomb p Gs) :
    ∀ i, degBound (t.prim b) lower R S lam Gs ≤ i → Y.coeff i = 0 := by
  intro i hi
  apply coeff_eq_zero_of_natDegree_lt
  by_contra hge
  have big : degBound (t.prim b) lower R S lam Gs ≤ Y.natDegree := by omega
  rw [degBound] at big
  have base : maxLen Gs + 2 ≤ Y.natDegree := by
    split at big
    · exact big
    · exact (le_max_left _ _).trans big
  obtain ⟨a, ha⟩ : ∃ a, Y.natDegree = a + 1 := ⟨Y.natDegree - 1, by omega⟩
  have Yne : Y ≠ 0 := by
    intro z
    rw [z, natDegree_zero] at ha
    omega
  have yne : Y.coeff (a + 1) ≠ 0 := by
    rw [← ha]
    exact leadingCoeff_ne_zero.mpr Yne
  have degY : Y.natDegree ≤ a + 1 := ha.le
  have tw : Term.value k (t.prim b).twist = 0 := Poly.value_zero
  have E1 := (coeff_L_top (t.prim b) g.degR g.degS degY).symm
  rw [eq, coeff_pcomb_of_maxLen_le Gs p (by omega), tw, mul_zero, zero_mul, add_zero] at E1
  have E2 : (L (t.prim b) (Poly.model k R) (Poly.model k S) Y).coeff (lam + a) = 0 := by
    rw [eq]
    exact coeff_pcomb_of_maxLen_le Gs p (by omega)
  have dtop := coeff_polyDer_top (t.prim b) degY
  rw [tw, mul_zero, zero_mul, add_zero] at dtop
  rw [L, coeff_add, coeff_mul_second g.degR ((natDegree_polyDer_le _ Y).trans degY),
    coeff_mul_second g.degS degY, dtop, Pole.coeff_polyDer_prim] at E2
  change (Poly.model k R).coeff lam * t.der k (Y.coeff (a + 1)) +
    (Poly.model k S).coeff lam * Y.coeff (a + 1) = 0 at E1
  change _ * (t.der k (Y.coeff a) + _) + _ * t.der k (Y.coeff (a + 1)) + _ = 0 at E2
  by_cases hr : (Poly.model k R).coeff lam = 0
  · rw [hr, zero_mul, zero_add] at E1
    exact yne ((mul_eq_zero.mp E1).resolve_left (g.lead.resolve_left (not_not.mpr hr)))
  · have rdom : Term.InDomain k (Poly.coeff R lam) := Poly.defined_coeff g.hR lam
    have nz : ¬ (Poly.coeff R lam).isZero = true := by
      rw [Term.isZero_iff rdom, Poly.value_coeff]
      exact hr
    have Dy : t.der k (Y.coeff (a + 1)) =
        -((Poly.model k S).coeff lam * Y.coeff (a + 1)) / (Poly.model k R).coeff lam := by
      rw [eq_div_iff hr]
      linear_combination E1
    have Dy0 : t.der k (Y.coeff a) =
        (-((if lam = 0 then 0 else (Poly.model k R).coeff (lam - 1)) *
            t.der k (Y.coeff (a + 1))) - (Poly.model k S).coeff lam * Y.coeff a -
          (if lam = 0 then 0 else (Poly.model k S).coeff (lam - 1)) * Y.coeff (a + 1)) /
            (Poly.model k R).coeff lam -
          ((a + 1 : ℕ) : K k n) * Term.value k b * Y.coeff (a + 1) := by
      rw [eq_sub_iff_add_eq, eq_div_iff hr]
      linear_combination E2
    have key : t.der k (Y.coeff a / Y.coeff (a + 1)) = Term.value k (cancelQ R S lam) -
        ((a + 1 : ℕ) : K k n) * Term.value k b := by
      rw [value_cancelQ, Derivation.leibniz_div]
      simp only [smul_eq_mul]
      rw [Dy0, Dy]
      field_simp
      ring
    have t3 := third_eq hl ht.2.1 (inDomain_cancelQ g.hR g.hS hr) ht.2.2 key
    rw [ite_eq_right nz, t3] at big
    have := le_max_right (maxLen Gs + 2) (a + 1 + 1)
    omega

end Solve

end SympyProofs.Calculus.Risch
