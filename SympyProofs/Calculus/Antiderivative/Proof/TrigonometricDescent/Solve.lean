module

public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Solve
public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Graph
public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Span
public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Model
public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricResult

/-! Completeness of the parametric differential solver over the original coefficient field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Fact (¬ IsSquare (-1 : K R 0))] {n : ℕ}
local notation "E" => WithI (K R 0)
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

/-- Interpret the two original-coordinate columns at the chosen value of the imaginary unit. -/
private noncomputable def evalColumn (m : ℕ) (j : k) (v : GraphColumn E n) :
    (Fin m → k) × M k n :=
  columnValue k m (Descent.columnParts v).1 + j • columnValue k m (Descent.columnParts v).2

private theorem getD_map_zero {A B : Type} [Zero A] [Zero B] (f : A → B) (hf : f 0 = 0)
    (xs : List A) (i : ℕ) : (xs.map f).getD i 0 = f (xs.getD i 0) := by
  rw [← hf, List.getD_map]

private theorem column_parts (j : k) (hj : j^2 = -1) (m : ℕ) (v : GraphColumn E n) :
    letI := (quadraticModelHom (R := R) k j hj).toAlgebra
    columnValue k m v = evalColumn k m j v := by
  let _ := (quadraticModelHom (R := R) k j hj).toAlgebra
  have hc := quadraticConstantHom_compatible (R := R) k j hj
  have hi := quadraticI_value (R := R) k j hj
  have h0 : project (R := R) 0 0 = 0 := (coordinatesEquiv (R := R) 0).map_zero
  refine Prod.ext (funext fun l => ?_) ?_
  · change Model.constantHom k (v.1.getD l 0) =
      Model.constantHom k (((v.1.map (project 0)).map QuadraticAlgebra.re).getD l 0) +
      j * Model.constantHom k (((v.1.map (project 0)).map QuadraticAlgebra.im).getD l 0)
    rw [getD_map_zero QuadraticAlgebra.re rfl, getD_map_zero QuadraticAlgebra.im rfl,
      getD_map_zero (project 0) h0]
    exact constantHom_project k hc j hi _
  · change val k v.2 = val k (project n v.2).re + j • val k (project n v.2).im
    rw [Model.smul_eq_C_mul]
    exact val_project k hc j hi _ _

variable [CharZero k] [IsAlgClosed k]
variable [NatBound (K R 0)] [LawfulNatBound (K R 0)]
variable [IntegerRelations (K R 0)] [LawfulIntegerRelations (K R 0)]
variable [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)]

private theorem span_at (t : Tower R n) (f : K R n) (gs : List (K R n))
    (out : List (K E n) × List (List (K E 0)))
    (h : t.solveOriginal quadraticConstantHom (K.C (WithI.imaginary (K R 0))) f gs = some out)
    (j : k) (hj : j^2 = -1) (a : Fin gs.length → k) (y : M k n) :
    (a,y) ∈ Submodule.span k (evalColumn k gs.length j ''
      {v | v ∈ graphColumns gs.length out.1 out.2}) ↔
    t.modelD k y + val k f * y = Model.linearCombination k (List.ofFn a) gs := by
  let _ := (quadraticModelHom (R := R) k j hj).toAlgebra
  let _ : CharZero (K R 0) := (Model.constantHom (R := R) k).charZero
  let _ : CharZero E := (quadraticModelHom (R := R) k j hj).charZero
  have he : evalColumn (R := R) (n := n) k gs.length j = columnValue k gs.length :=
    (funext (column_parts (R := R) (n := n) k j hj gs.length)).symm
  rw [he, graphColumns_spec]
  exact (t.solveOriginal_spec k quadraticConstantHom (quadraticConstantHom_compatible k j hj)
    (K.C (WithI.imaginary (K R 0))) quadraticI_sq f gs h y (List.ofFn a) (by simp)).symm

/-- For every compatible algebraically closed model, the returned original-field generators
and homogeneous constant rows describe exactly every solution of the native mixed-tower
differential equation. -/
theorem Tower.solveAdjoinI_spec (t : Tower R n) (f : K R n) (gs : List (K R n))
    {out : List (K R n) × List (List (K R 0))} (h : t.solveAdjoinI f gs = some out)
    (y : M k n) (cs : List k) (hs : cs.length = gs.length) :
    t.modelD k y + val k f * y = Model.linearCombination k cs gs ↔
      ∃ ds : List k, ds.length = out.1.length ∧ y = Model.linearCombination k ds out.1 ∧
        ∀ row ∈ out.2, Model.rowHolds k row (cs ++ ds) := by
  obtain ⟨z,hz,rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨j,hj⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) zero_lt_two
  have j0 : j ≠ 0 := by rintro rfl; simp at hj
  have hj' : (-j)^2 = -1 := by simpa using hj
  let xs := graphColumns gs.length z.1 z.2
  let plus := evalColumn (R := R) (n := n) k gs.length j
  let minus := evalColumn (R := R) (n := n) k gs.length (-j)
  have spans : Submodule.span k (plus '' {v | v ∈ xs}) =
      Submodule.span k (minus '' {v | v ∈ xs}) := by
    ext ⟨p,u⟩
    exact (span_at k t f gs z hz j hj p u).trans (span_at k t f gs z hz (-j) hj' p u).symm
  have parts := Descent.span_parts xs Descent.columnParts (columnValue k gs.length) j j0 plus
    minus (fun _ _ => rfl) (fun _ _ => by simp [minus, evalColumn, sub_eq_add_neg]) spans
  let a (i : Fin gs.length) := cs.get (Fin.cast hs.symm i)
  have ha : List.ofFn a = cs := by
    apply List.ext_getElem
    · simpa using hs.symm
    · simp [a]
  rw [← ha]
  change _ ↔ ∃ ds : List k, ds.length = (describeGraph _ _).1.length ∧
    y = Model.linearCombination k ds (describeGraph _ _).1 ∧
    ∀ row ∈ (describeGraph _ _).2, Model.rowHolds k row (List.ofFn a ++ ds)
  rw [describeGraph_spec, parts]
  exact (span_at k t f gs z hz j hj a y).symm

end SympyProofs.Calculus.Antiderivative
