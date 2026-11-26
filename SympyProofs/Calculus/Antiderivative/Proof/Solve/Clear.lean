module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Describe
public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Polynomial
public import SympyProofs.Calculus.Antiderivative.Proof.PoleOrders

/-! Clearing the rational equation and interpreting the solver's common denominator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

local notation "ι" => algebraMap (M k n)[X] (RatFunc (M k n))

/-- The cleared polynomial identity is equivalent to the original rational equation. -/
theorem equation_iff {F : Type} [Field F] (δ : Derivation ℤ F[X] F[X]) {N B H T u d : F[X]}
    (hb : B ≠ 0) (ht : T ≠ 0) (hd : d ≠ 0) :
    let φ := algebraMap F[X] (RatFunc F)
    Extension.Pole.Equation δ N B H T u d ↔
      Extension.extend δ (φ u / φ d) + (φ N / φ B) * (φ u / φ d) = φ H / φ T := by
  dsimp only
  rw [Extension.extend_div]
  have hb' := RatFunc.algebraMap_ne_zero hb
  have ht' := RatFunc.algebraMap_ne_zero ht
  have hd' := RatFunc.algebraMap_ne_zero hd
  constructor
  · intro he
    have h := congrArg (algebraMap F[X] (RatFunc F)) he
    simp only [map_mul, map_add, map_sub, map_pow] at h
    field_simp [hb', ht', hd']
    linear_combination h
  · intro h
    field_simp [hb', ht', hd'] at h
    apply RatFunc.algebraMap_injective F
    simp only [map_mul, map_add, map_sub, map_pow]
    linear_combination h

/-- The model value of a combination of solution fractions has the same common denominator. -/
theorem combination_join (w : ℕ) (p : Poly (K R n)) (cols : List (Column R n))
    (a : Fin cols.length → k) :
    Model.stepEquiv k n (Model.linearCombination k (List.ofFn a)
      (cols.map fun v => K.join v.solution p)) =
      ι (Linear.accumulate cols (Column.value k w) a).2.1 / ι (modelPoly k p) := by
  classical
  rw [linearCombination_ofFn, map_sum, Linear.accumulate_apply, Prod.snd_sum, Prod.fst_sum,
    map_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul, Model.stepEquiv_scalar, K.join, map_div₀, val_joinPoly, Prod.smul_snd,
    Prod.smul_fst, Column.value]
  rw [Algebra.smul_def, map_mul, div_eq_mul_inv, ← mul_assoc]
  rfl

/-- Lifting an input vector through the computed columns is equivalent to solving the
cleared equation for its polynomial numerator. -/
theorem polynomial_coordinates [CharZero k] [NatBound (K R 0)] [LawfulNatBound (K R 0)]
    (t : Tower R n) (g : ReducedGen (K R n)) (hg : g.Admissible k t) (L : Level R n)
    (hs : L.SolveSpec k t) (hl : L.LogRelationsSpec k t)
    (a b : Poly (K R n)) (ha : a ≠ 0) (rhs : List (Poly (K R n)))
    (w : ℕ) (hw : rhs.length = w) (c : Fin w → k) (u : (M k n)[X]) :
    let cols := polynomialSolutions t.D g L a b rhs
    (∃ z : Fin cols.length → k, (Linear.accumulate cols (Column.value k w) z).1 = c ∧
      (Linear.accumulate cols (Column.value k w) z).2.1 = u) ↔
    operator k t g a b u = Model.polynomialCombination k (List.ofFn c) rhs := by
  subst w
  dsimp only
  let cols := polynomialSolutions t.D g L a b rhs
  let A := Linear.accumulate (k := k) cols (Column.value k rhs.length)
  have graph := polynomialSolutions_spec k t g hg L hs hl a b ha rhs
  constructor
  · rintro ⟨z,hc,hu⟩
    have mem := (Linear.mem_columns_iff cols _ (A z)).mpr ⟨z, rfl⟩
    have he := ((graph _).mp mem).2
    change (A z).2.1 = u at hu
    change (A z).1 = c at hc
    rwa [← hu, ← hc, ← accumulate_polynomial]
  · intro eqn
    have mem := (graph (c,u,0)).mpr ⟨rfl, (accumulate_polynomial k rhs c).symm ▸ eqn⟩
    obtain ⟨z,hz⟩ := (Linear.mem_columns_iff cols _ _).mp mem
    exact ⟨z,congrArg Prod.fst hz,congrArg (fun x => x.2.1) hz⟩

end SympyProofs.Calculus.Antiderivative.Solve
