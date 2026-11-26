module

public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Pair

/-! Correctness of elementary integration in a mixed tangent tower with the answer returned
over the original computable constant field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

open Descent

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Fact (¬ IsSquare (-1 : K R 0))] {n : ℕ}
local notation "E" => WithI (K R 0)
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k]

namespace Trigonometric.Descent

/-- Interpretation of a quadratic answer after choosing either square root of negative one. -/
noncomputable def signed (j : k) (hj : j^2 = -1) : Interpretation E k n :=
  letI := (quadraticModelHom (R := R) k j hj).toAlgebra
  Interpretation.standard k

omit [CharZero k] in
theorem signed_fits (j : k) (hj : j^2 = -1) : Fits (signed (R := R) (n := n) k j hj) j :=
  fits_quadraticModelHom j hj

private theorem signed_half (j : k) (hj : j^2 = -1) (t : Tower R n) (s : RootSum E n)
    (h : (signed k j hj).Regular s) (hw : s.weight ≠ 0) :
    (signed k j hj).Regular (halfSum s) ∧
      (signed k j hj).derivative (t.modelD k) (halfSum s) =
        (signed k j hj).derivative (t.modelD k) s / 2 := by
  let _ : CharZero R := (algebraMap R k).charZero
  let _ := (quadraticModelHom (R := R) k j hj).toAlgebra
  have hr : s.Regular k := (Interpretation.standard_regular k s).mp h
  exact ⟨(Interpretation.standard_regular k _).mpr (half_regular k s hr hw),
    by simpa only [signed,Interpretation.standard_derivative] using half_derivative k t s hr hw⟩

private theorem rootSum_spec (t : Tower R n) (s : RootSum E n) (j : k) (hj : j^2 = -1)
    (hP : (signed k j hj).Regular s) (hN : (signed k (-j) (by simpa using hj)).Regular s) :
    let P := signed k j hj
    let N := signed k (-j) (by simpa using hj)
    (∀ r ∈ rootSum s, r.Regular k) ∧
      ((rootSum s).map (RootSum.deriv k t)).sum =
        (P.derivative (t.modelD k) s + N.derivative (t.modelD k) s)/2 := by
  let hj' : (-j)^2 = -1 := by simpa using hj
  let P := signed (R := R) (n := n) k j hj
  let N := signed (R := R) (n := n) k (-j) hj'
  dsimp only
  by_cases hw : s.weight = 0
  · simp [rootSum,hw,Interpretation.derivative]
  rw [rootSum,ite_eq_right hw]
  obtain ⟨rP,dP⟩ := signed_half k j hj t s hP hw
  obtain ⟨rN,dN⟩ := signed_half k (-j) hj' t s hN hw
  obtain ⟨hr,hd⟩ := pairedSums_spec k t (halfSum s) rfl P N j hj
    (signed_fits k j hj) (signed_fits k (-j) hj') rP rN
  refine ⟨hr,?_⟩
  rw [hd]
  change (signed k j hj).derivative _ (halfSum s) +
    (signed k (-j) hj').derivative _ (halfSum s) = _
  rw [dP,dN]
  ring

/-- The real field part and the descended logarithmic terms give the average derivative
of the two regular interpretations of a quadratic answer. -/
theorem answer_spec (t : Tower R n) (a : Answer E n) (j : k) (hj : j^2 = -1)
    (hP : ∀ s ∈ a.sums, (signed k j hj).Regular s)
    (hN : ∀ s ∈ a.sums, (signed k (-j) (by simpa using hj)).Regular s) :
    let P := signed (R := R) (n := n) k j hj
    let N := signed (R := R) (n := n) k (-j) (by simpa using hj)
    (answer a).Regular k ∧ Answer.deriv k t (answer a) =
      ((t.modelD k (P.field a.field) + (a.sums.map (P.derivative (t.modelD k))).sum) +
       (t.modelD k (N.field a.field) + (a.sums.map (N.derivative (t.modelD k))).sum))/2 := by
  let hj' : (-j)^2 = -1 := by simpa using hj
  let P := signed (R := R) (n := n) k j hj
  let N := signed (R := R) (n := n) k (-j) hj'
  let D := t.modelD k
  have hl (l : List (RootSum E n)) (hp : ∀ s ∈ l, P.Regular s) (hn : ∀ s ∈ l, N.Regular s) :
      ((l.flatMap rootSum).map (RootSum.deriv k t)).sum =
        ((l.map (P.derivative D)).sum + (l.map (N.derivative D)).sum)/2 := by
    induction l with
    | nil => simp
    | cons s l ih =>
      have hs := (rootSum_spec k t s j hj (hp s (by simp)) (hn s (by simp))).2
      simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
      rw [hs,ih (fun u hu => hp u (by simp [hu])) (fun u hu => hn u (by simp [hu]))]
      change (_ + _)/2 + (_ + _)/2 = (_ + _ + (_ + _))/2
      dsimp only [P,N,D]
      ring
  constructor
  · intro r hr
    obtain ⟨s,hs,hr⟩ := List.mem_flatMap.mp hr
    exact (rootSum_spec k t s j hj (hP _ hs) (hN _ hs)).1 _ hr
  change D (val k (project n a.field).re) +
    ((a.sums.flatMap rootSum).map (RootSum.deriv k t)).sum = _ / 2
  rw [hl a.sums hP hN]
  have pf := (signed_fits (R := R) (n := n) k j hj).field a.field
  have nf := (signed_fits (R := R) (n := n) k (-j) hj').field a.field
  rw [pf,nf,map_neg,neg_mul,← sub_eq_add_neg,map_add,map_sub]
  dsimp only [D,P,N]
  ring

end Trigonometric.Descent

variable [IsAlgClosed k]
variable [NatBound (K R 0)] [LawfulNatBound (K R 0)]
variable [IntegerRelations (K R 0)] [LawfulIntegerRelations (K R 0)]
variable [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)]

private theorem signed_integral (j : k) (hj : j^2 = -1) (t : Tower R n) (f : K R n)
    (a : Answer E n) (h : t.integrateOriginal quadraticConstantHom
      (K.C (WithI.imaginary (K R 0))) f = some (.elementary a)) :
    let J := signed (R := R) (n := n) k j hj
    (∀ s ∈ a.sums, J.Regular s) ∧
      t.modelD k (J.field a.field) + (a.sums.map (J.derivative (t.modelD k))).sum = val k f := by
  let _ : CharZero R := (algebraMap R k).charZero
  let _ := (quadraticModelHom (R := R) k j hj).toAlgebra
  obtain ⟨hr,hd⟩ := t.integrateOriginal_sound k quadraticConstantHom
    (quadraticConstantHom_compatible k j hj) _ quadraticI_sq f a h
  refine ⟨fun s hs => (Interpretation.standard_regular k s).mpr (hr s hs),?_⟩
  change t.modelD k (val k a.field) + (a.sums.map
    ((Interpretation.standard k).derivative (t.modelD k))).sum = val k f
  rw [funext (Interpretation.standard_derivative (S := E) k t)]
  exact hd

/-- Every elementary result is regular and differentiates to its input over the original
constant field, in the original primitive, exponential, and tangent coordinates. -/
theorem Tower.integrateAdjoinI_sound (t : Tower R n) (f : K R n) (a : Answer R n)
    (h : t.integrateAdjoinI f = some (.elementary a)) :
    a.Regular k ∧ Answer.deriv k t a = val k f := by
  obtain ⟨r,hr,h⟩ := Option.map_eq_some_iff.mp h
  cases r with
  | nonelementary => contradiction
  | elementary w =>
    cases h
    obtain ⟨j,hj⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) zero_lt_two
    obtain ⟨hp,dp⟩ := signed_integral k j hj t f w hr
    obtain ⟨hn,dn⟩ := signed_integral k (-j) (by simpa using hj) t f w hr
    obtain ⟨reg,res⟩ := answer_spec k t w j hj hp hn
    exact ⟨reg,by rw [res,dp,dn]; ring⟩

/-- The negative decision rules out every elementary primitive over the model of the
original tower. -/
theorem Tower.integrateAdjoinI_complete (t : Tower R n) (f : K R n)
    (h : t.integrateAdjoinI f = some .nonelementary) : ¬ t.Elementary k (val k f) := by
  obtain ⟨r,hr,h⟩ := Option.map_eq_some_iff.mp h
  cases r with
  | elementary w => contradiction
  | nonelementary =>
    obtain ⟨j,hj⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) zero_lt_two
    let _ : CharZero R := (algebraMap R k).charZero
    let _ := (quadraticModelHom (R := R) k j hj).toAlgebra
    exact t.integrateOriginal_complete k quadraticConstantHom
      (quadraticConstantHom_compatible k j hj) _ quadraticI_sq f hr

end SympyProofs.Calculus.Antiderivative
