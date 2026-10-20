module

public import SympyProofs.Python.Int

@[expose] public section

namespace Python.Math

/-- Python's `math.prod`, using the carrier's multiplication and default start of one. -/
def prod {I : Type} [Mul I] [OfNat I 1] (values : Array I) : I :=
  values.foldl (· * ·) 1

/-- The left-to-right multiplication computes the mathematical product. -/
theorem prod_eq_prod (values : Array ℕ) : prod values = values.toList.prod := by
  rw [prod, ← Array.prod_eq_foldl_nat, Array.prod_toList]

/-- The abstract integer product has the expected mathematical value. -/
theorem toInt_prod {I : Type} [PythonInt I] (values : Array I) :
    PythonInt.toInt (prod values) = (values.toList.map PythonInt.toInt).prod := by
  rw [prod, ← Array.foldl_toList, List.prod_eq_foldl]
  simpa using (List.foldl_map_hom (a := (1 : I)) (l := values.toList)
    (fun x y => (PythonInt.toInt_mul x y).symm)).symm

end Python.Math
