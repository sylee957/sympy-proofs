module

public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Common
public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Model
public import SympyProofs.Calculus.Antiderivative.Program.Decision

/-! Correctness of the rational logarithmic relation decision at a tower extension. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Polynomial Logarithmic
open scoped Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
variable [IntegerRelations (K R 0)] [LawfulIntegerRelations (K R 0)]
variable [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)]

omit [CharZero k] in
private theorem lower_rows (t : Tower R n) (g : ReducedGen (K R n)) (L : Level R n)
    (hl : L.LogRelationsSpec k t) (data : LogPoleData (K R n)) (q : List ℚ)
    (hs : data.normalDen ≠ 0) (hn : q.length = data.numerators.length)
    (hc : q.length = data.constants.length) :
    (∀ r ∈ factoredLogStep t.D g L.logRelations data (factorTower data.normalDen),
      Linear.dot q r = 0) ↔
      (∀ row ∈ data.poleRows, rationalCombination q row = 0) ∧
        (∀ p ∈ factorTower data.normalDen, ∃ e : ℚ, Poly.equiv p ∣
          Step.rationalPolynomial q data.numerators - C (e : K R n) *
          Poly.equiv (Step.polyDer t.D (g.velocity t.D) data.normalDen)) ∧
        ∃ e : ℚ, t.SaturatedLog k (val k (rationalCombination q data.constants) +
          (e : M k n) * val k (slope t g)) := by
  have hp (p : Poly (K R n)) (hp : p ∈ factorTower data.normalDen) : p.natDegree ≠ 0 := by
    have hirr := (MulEquiv.irreducible_iff (Poly.equiv (R := K R n))).mpr
      (factorTower_irreducible _ hs p hp)
    simpa only [Poly.natDegree_equiv] using hirr.natDegree_pos.ne'
  cases g with
  | prim b =>
    rw [factoredLogStep_prim _ _ _ _ _ _ hp hn, hl _ _ hc.symm]
    simp [ReducedGen.velocity, Gen.velocity, slope]
  | exp u =>
    rw [factoredLogStep_exp _ _ _ _ _ _ hp hn hc]
    have v : (ReducedGen.exp u).velocity t.D = Poly.C (t.D u) * Poly.X := by
      apply Poly.equiv.injective
      simp [ReducedGen.velocity, Gen.velocity, ← Polynomial.C_mul_X_pow_eq_monomial]
    rw [v]
    refine and_congr_right fun _ => and_congr_right fun _ => exists_congr fun e => ?_
    rw [hl _ _ (by simp [hc]), combination_append _ _ _ _ hc]
    simp [slope]

variable [NatBound (K R 0)]

/-- The logarithmic relation rows at an admissible primitive or exponential extension
characterize every rational combination with a positive multiple equal to a logarithmic
derivative in the full tower model. -/
theorem stepLevel_logRelations_spec (t : Tower R n) (g : ReducedGen (K R n)) (L : Level R n)
    (hg : g.Admissible k t) (hl : L.LogRelationsSpec k t) :
    (stepLevel t.D g L).LogRelationsSpec k (t.step g) := by
  intro ws q hlen
  let as := (commonDen ws).1
  let T := (commonDen ws).2
  let d := poleDerivative (exponential g) T
  let G := gcd T d
  let S := T / G
  let ns := as.map (· / G)
  let ps := ns.map (· / S)
  let cs := ps.map (·.coeff 0)
  let data := logPoleData g ws
  have data_eq : data = ⟨S, ns, coefficientSlices (as.map (· % G)) ++
      (coefficientSlices ps).drop 1, cs⟩ := by cases g <;> rfl
  obtain ⟨ht, hlen', he⟩ := value_commonDen k ws q
  have hsf : Squarefree (Poly.equiv S) := by
    let _ : CharZero (K R n) := (val (R := R) (n := n) k).charZero
    cases g with
    | prim _ => exact Step.squarefreeParts_spec ht
    | exp _ => exact (Step.expNormalDen_spec ht).1
  have hs : data.normalDen ≠ 0 := data_eq ▸ (map_ne_zero_iff _ Poly.equiv.injective).mp hsf.ne_zero
  have hn : q.length = data.numerators.length := by simp [data_eq, ns, as, hlen', hlen]
  have hc : q.length = data.constants.length := by simp [data_eq, cs, ps, ns, as, hlen', hlen]
  change (∀ r ∈ factoredLogStep t.D g L.logRelations data (factorTower data.normalDen),
    Linear.dot q r = 0) ↔ _
  rw [lower_rows k t g L hl data q hs hn hc, data_eq]
  change ((∀ row ∈ coefficientSlices (as.map (· % G)) ++ (coefficientSlices ps).drop 1,
      rationalCombination q row = 0) ∧ _) ↔ _
  have rows := poleRows_iff q as G S
  dsimp only at rows
  rw [rows]
  let W := Step.rationalPolynomial q as
  let N := Step.rationalPolynomial q ns
  have hN : N = W / Poly.equiv G := combination_div q as G
  have hcoeff : (N / Poly.equiv S).coeff 0 = rationalCombination q cs := by
    rw [← combination_div q ns S]
    exact combination_coeff q ps 0
  have sem := model_iff k t g hg T ht W N (rationalCombination q cs) hN hcoeff
  have m := saturated_equiv ((t.step g).modelD k)
    (Model.extendVariable (t.modelD k) (t.modelVelocity k g)) (Model.stepEquiv k n)
    (t.stepEquiv_modelD k g) (val k (rationalCombination q ws))
  rw [he] at m
  exact sem.symm.trans m.symm

end SympyProofs.Calculus.Antiderivative
