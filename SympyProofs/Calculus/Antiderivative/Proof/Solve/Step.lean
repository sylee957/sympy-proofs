module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Clear
public import SympyProofs.Calculus.Antiderivative.Program.Decision

/-! The complete parametric differential equation at a primitive or exponential step. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

open Polynomial
variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
variable [CharZero k] [NatBound (K R 0)] [LawfulNatBound (K R 0)]

local notation "ι" => algebraMap (M k n)[X] (RatFunc (M k n))

/-- The result rows for a bounded polynomial problem describe exactly its solutions divided
by the common denominator. -/
theorem describe_polynomial (t : Tower R n) (g : ReducedGen (K R n)) (hg : g.Admissible k t)
    (L : Level R n) (hs : L.SolveSpec k t) (hl : L.LogRelationsSpec k t)
    (a b p : Poly (K R n)) (ha : a ≠ 0) (rhs : List (Poly (K R n)))
    (w : ℕ) (hw : rhs.length = w) (c : Fin w → k) (y : M k (n+1)) :
    let output := describe w p (polynomialSolutions t.D g L a b rhs)
    (∃ ds : List k, ds.length = output.1.length ∧ y = Model.linearCombination k ds output.1 ∧
      ∀ row ∈ output.2, Model.rowHolds k row (List.ofFn c ++ ds)) ↔
    ∃ u : (M k n)[X], Model.stepEquiv k n y = ι u / ι (modelPoly k p) ∧
      operator k t g a b u = Model.polynomialCombination k (List.ofFn c) rhs := by
  let cols := polynomialSolutions t.D g L a b rhs
  let A := Linear.accumulate (k := k) cols (Column.value k w)
  dsimp only
  rw [describe_spec]
  have hc := polynomial_coordinates k t g hg L hs hl a b ha rhs w hw c
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ⟨(A q).2.1, combination_join k w p cols q, (hc _).mp ⟨q,hq,rfl⟩⟩
  · rintro ⟨u,hy,he⟩
    obtain ⟨q,hq,hv⟩ := (hc u).mpr he
    refine ⟨q,hq,(Model.stepEquiv k n).injective ?_⟩
    rwa [combination_join k w p cols q, hv]

/-- Completeness and soundness of the executable rational solver for arbitrary model
solutions and coefficients in the constant field. -/
theorem step_spec (t : Tower R n) (g : ReducedGen (K R n)) (hg : g.Admissible k t)
    (L : Level R n)
    (hs : L.SolveSpec k t) (hl : L.LogRelationsSpec k t)
    (f : K R (n+1)) (gs : List (K R (n+1))) (y : M k (n+1)) (cs : List k)
    (hcs : cs.length = gs.length) :
    (t.step g).modelD k y + val k f * y = Model.linearCombination k cs gs ↔
      ∃ d : List k, d.length = (step t.D g L f gs).1.length ∧
        y = Model.linearCombination k d (step t.D g L f gs).1 ∧
        ∀ row ∈ (step t.D g L f gs).2, Model.rowHolds k row (cs ++ d) := by
  let c (i : Fin gs.length) := cs.get (Fin.cast hcs.symm i)
  have hc : cs = List.ofFn c := by
    apply List.ext_getElem
    · simpa using hcs
    · intro i hi hj
      simp [c]
  rw [hc]
  let N := f.split.1
  let B := f.split.2
  let T := (commonDen gs).2
  let ws := (commonDen gs).1
  let P := denominator t.D g L N B T
  let A := P * B
  let S := N * P - B * Step.polyDer t.D (g.velocity t.D) P
  let rhs := ws.map (· * ((P / T) * A))
  let φ := Step.modelPoly (val (R := R) (n := n) k)
  let x := Model.stepEquiv k n
  let D := t.polyDerModel k g
  let H := Model.polynomialCombination k (List.ofFn c) ws
  have hinj : Function.Injective φ :=
    (Polynomial.map_injective _ (val_injective k)).comp Poly.equiv.injective
  have hsplit := Prod.mk.inj (val_split k f)
  have hn : φ N = (x (val k f)).num := hsplit.1
  have hb : φ B = (x (val k f)).denom := hsplit.2
  have hB : φ B ≠ 0 := hb ▸ RatFunc.denom_ne_zero _
  have B0 : B ≠ 0 := fun z => hB (z ▸ φ.map_zero)
  have hcop : IsCoprime (φ B) (φ N) := by rw [hb,hn]; exact (RatFunc.isCoprime_num_denom _).symm
  have ht : T ≠ 0 := (commonDen_spec k gs).1
  have hT := (map_ne_zero_iff φ hinj).mpr ht
  have X0 : (Poly.X : Poly (K R n)) ≠ 0 := fun z => Polynomial.X_ne_zero (R := K R n) (by
    simpa using congrArg Poly.equiv z)
  have hp : P ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ X0) ht) (pow_ne_zero _ B0)
  have hP := (map_ne_zero_iff φ hinj).mpr hp
  have ha : A ≠ 0 := mul_ne_zero hp B0
  have hrhs : rhs.length = gs.length := by simpa [rhs, ws] using length_commonDen gs
  let result := describe gs.length P (polynomialSolutions t.D g L A S rhs)
  change _ ↔ ∃ ds : List k, ds.length = result.1.length ∧
    y = Model.linearCombination k ds result.1 ∧ ∀ row ∈ result.2, _
  have desc := describe_polynomial k t g hg L hs hl A S P ha rhs gs.length hrhs c y
  dsimp only at desc
  refine Iff.trans ?_ desc.symm
  have hx : x (val k f) = ι (φ N) / ι (φ B) := by rw [hn,hb,RatFunc.num_div_denom]
  have hgs : x (Model.linearCombination k (List.ofFn c) gs) = ι H / ι (φ T) :=
    (eq_div_iff (RatFunc.algebraMap_ne_zero hT)).mpr ((commonDen_spec k gs).2 _)
  rw [← x.injective.eq_iff, map_add, map_mul, hx, hgs, Tower.stepEquiv_modelD]
  change Extension.extend D (x y) + _ * x y = _ ↔ _
  have he (u : (M k n)[X]) :
      operator k t g A S u = Model.polynomialCombination k (List.ofFn c) rhs ↔
      Extension.Pole.Equation D (φ N) (φ B) H (φ T) u (φ P) := by
    change φ A * D u + φ S * u = _ ↔ _
    rw [Model.polynomialCombination_mul]
    change φ (P * B) * D u + φ (N * P - B * Step.polyDer t.D (g.velocity t.D) P) * u =
      H * φ ((P / T) * (P * B)) ↔ _
    have dvd : T ∣ P := (dvd_mul_left T _).mul_right _
    have hquot : φ (P / T) * φ T = φ P := by
      rw [← map_mul,mul_comm,EuclideanDomain.mul_div_cancel' ht dvd]
    rw [← mul_left_inj' hT]
    simp only [map_mul, map_sub, Extension.Pole.Equation]
    have hder : φ (Step.polyDer t.D (g.velocity t.D) P) = D (φ P) :=
      t.modelPoly_polyDer k g P
    rw [hder]
    constructor
    · intro h
      linear_combination h + H * φ P * φ B * hquot
    · intro h
      linear_combination h - H * φ P * φ B * hquot
  constructor
  · intro eqn
    have hy := (equation_iff D hB hT (RatFunc.denom_ne_zero (x y))).mpr
      (by rwa [RatFunc.num_div_denom])
    obtain ⟨v,hv⟩ := denominator_dvd k t g hg L hl N B T B0 ht hcop (x y) H hy
    change φ P = (x y).denom * v at hv
    have yv : x y = ι ((x y).num * v) / ι (φ P) := by
      rw [eq_div_iff (RatFunc.algebraMap_ne_zero hP), hv, map_mul, map_mul,
        ← mul_assoc]
      exact congrArg (· * ι v) ((eq_div_iff (RatFunc.algebraMap_ne_zero
        (RatFunc.denom_ne_zero (x y)))).mp (RatFunc.num_div_denom (x y)).symm)
    exact ⟨_,yv,(he _).mpr ((equation_iff D hB hT hP).mpr (by rwa [← yv]))⟩
  · rintro ⟨u,hy,hu⟩
    rw [hy]
    exact (equation_iff D hB hT hP).mp ((he u).mp hu)

end SympyProofs.Calculus.Antiderivative.Solve
