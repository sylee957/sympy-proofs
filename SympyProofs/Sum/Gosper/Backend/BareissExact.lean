module

public import Mathlib

/-! Determinantal identities establishing exactness of Bareiss divisions. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Matrix

/-- Border a square matrix by one row and one column. -/
def bareissBorder {R α : Type*} (D : Matrix α α R) (u v : α → R) (a : R) :
    Matrix (α ⊕ Unit) (α ⊕ Unit) R :=
  Matrix.fromBlocks D (fun i _ => u i) (fun _ j => v j) (fun _ _ => a)

set_option backward.isDefEq.respectTransparency false in
/-- The two-by-two Sylvester identity around an invertible core. -/
theorem bareiss_sylvester_of_invertible {R α : Type*} [CommRing R]
    [Fintype α] [DecidableEq α] (D : Matrix α α R) [Invertible D]
    (B : Matrix α (Fin 2) R) (C : Matrix (Fin 2) α R) (E : Matrix (Fin 2) (Fin 2) R) :
    (bareissBorder D (fun i => B i 0) (C 0) (E 0 0)).det *
        (bareissBorder D (fun i => B i 1) (C 1) (E 1 1)).det -
      (bareissBorder D (fun i => B i 0) (C 1) (E 1 0)).det *
        (bareissBorder D (fun i => B i 1) (C 0) (E 0 1)).det =
      D.det * (Matrix.fromBlocks D B C E).det := by
  have hsmall (i j : Fin 2) :
      (bareissBorder D (fun r => B r j) (C i) (E i j)).det =
        D.det * (E - C * ⅟D * B) i j := by
    rw [bareissBorder, Matrix.det_fromBlocks₁₁]
    simp [Matrix.det_unique, Matrix.mul_apply, Matrix.sub_apply]
  rw [hsmall, hsmall, hsmall, hsmall, Matrix.det_fromBlocks₁₁, Matrix.det_fin_two]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Sylvester's identity over a domain only requires the previous pivot minor to be nonzero. -/
theorem bareiss_sylvester {R α : Type*} [CommRing R] [IsDomain R]
    [Fintype α] [DecidableEq α] (D : Matrix α α R) (hD : D.det ≠ 0)
    (B : Matrix α (Fin 2) R) (C : Matrix (Fin 2) α R) (E : Matrix (Fin 2) (Fin 2) R) :
    (bareissBorder D (fun i => B i 0) (C 0) (E 0 0)).det *
        (bareissBorder D (fun i => B i 1) (C 1) (E 1 1)).det -
      (bareissBorder D (fun i => B i 0) (C 1) (E 1 0)).det *
        (bareissBorder D (fun i => B i 1) (C 0) (E 0 1)).det =
      D.det * (Matrix.fromBlocks D B C E).det := by
  let f := algebraMap R (FractionRing R)
  have hf : Function.Injective f := IsFractionRing.injective R (FractionRing R)
  have hDf : (D.map f).det ≠ 0 := by
    rw [← show f D.det = (D.map f).det from f.map_det D]
    exact fun h => hD (hf (h.trans (map_zero f).symm))
  let : Invertible (D.map f) := Matrix.invertibleOfIsUnitDet (D.map f) (isUnit_iff_ne_zero.mpr hDf)
  have hid := bareiss_sylvester_of_invertible (D.map f) (B.map f) (C.map f) (E.map f)
  have hborder (i j : Fin 2) :
      f (bareissBorder D (fun a => B a j) (C i) (E i j)).det =
        (bareissBorder (D.map f) (fun a => (B.map f) a j) ((C.map f) i) ((E.map f) i j)).det := by
    rw [f.map_det]
    apply congrArg Matrix.det
    ext a b
    cases a <;> cases b <;> rfl
  have hbig : f (Matrix.fromBlocks D B C E).det =
      (Matrix.fromBlocks (D.map f) (B.map f) (C.map f) (E.map f)).det := by
    rw [f.map_det]
    apply congrArg Matrix.det
    ext a b
    cases a <;> cases b <;> rfl
  have hcore : f D.det = (D.map f).det := f.map_det D
  apply hf
  simp only [map_sub, map_mul, hborder, hbig, hcore]
  exact hid

/-- A bordered minor for a history of selected rows and columns. -/
def bareissMinor {R α ι κ : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (M : Matrix ι κ R) (rows : α → ι) (cols : α → κ) (i : ι) (j : κ) : R :=
  (bareissBorder (M.submatrix rows cols) (fun a => M (rows a) j)
    (fun a => M i (cols a)) (M i j)).det

def bareissTwoBorderEquiv (α : Type*) : ((α ⊕ Unit) ⊕ Unit) ≃ (α ⊕ Fin 2) where
  toFun
    | .inl (.inl a) => .inl a
    | .inl (.inr _) => .inr 0
    | .inr _ => .inr 1
  invFun
    | .inl a => .inl (.inl a)
    | .inr i => Fin.cases (.inl (.inr ())) (fun _ => .inr ()) i
  left_inv := by
    intro i
    rcases i with (i | ⟨⟩) | ⟨⟩ <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · rfl
    · fin_cases i <;> rfl

/-- Extending both histories makes the selected bordered minor the new core determinant. -/
theorem bareissMinor_core {R α ι κ : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (M : Matrix ι κ R) (rows : α → ι) (cols : α → κ) (i : ι) (j : κ) :
    (M.submatrix (Sum.elim rows (fun _ : Unit => i))
      (Sum.elim cols (fun _ : Unit => j))).det = bareissMinor M rows cols i j := by
  congr 1
  ext a b
  cases a <;> cases b <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The condensation identity for arbitrary (possibly repeated) row/column histories. -/
theorem bareissMinor_step {R α ι κ : Type*} [CommRing R] [IsDomain R]
    [Fintype α] [DecidableEq α] (M : Matrix ι κ R) (rows : α → ι) (cols : α → κ)
    (hcore : (M.submatrix rows cols).det ≠ 0) (r i : ι) (c j : κ) :
    bareissMinor M rows cols r c * bareissMinor M rows cols i j -
      bareissMinor M rows cols i c * bareissMinor M rows cols r j =
      (M.submatrix rows cols).det *
        bareissMinor M (Sum.elim rows (fun _ : Unit => r))
          (Sum.elim cols (fun _ : Unit => c)) i j := by
  let B : Matrix α (Fin 2) R := fun a k => Fin.cases (M (rows a) c) (fun _ => M (rows a) j) k
  let C : Matrix (Fin 2) α R := fun k a => Fin.cases (M r (cols a)) (fun _ => M i (cols a)) k
  let E : Matrix (Fin 2) (Fin 2) R := !![M r c, M r j; M i c, M i j]
  have hbig : bareissMinor M (Sum.elim rows (fun _ : Unit => r))
      (Sum.elim cols (fun _ : Unit => c)) i j =
        (Matrix.fromBlocks (M.submatrix rows cols) B C E).det := by
    unfold bareissMinor
    have hm : bareissBorder
        (M.submatrix (Sum.elim rows (fun _ : Unit => r)) (Sum.elim cols (fun _ : Unit => c)))
        (fun a => M (Sum.elim rows (fun _ : Unit => r) a) j)
        (fun a => M i (Sum.elim cols (fun _ : Unit => c) a)) (M i j) =
      (Matrix.fromBlocks (M.submatrix rows cols) B C E).submatrix
        (bareissTwoBorderEquiv α) (bareissTwoBorderEquiv α) := by
      ext a b
      rcases a with (a | a) | a <;> rcases b with (b | b) | b <;> rfl
    rw [hm, Matrix.det_submatrix_equiv_self]
  rw [hbig]
  exact bareiss_sylvester (M.submatrix rows cols) hcore B C E

/-- With no selected pivots, a bordered minor is the original matrix entry. -/
theorem bareissMinor_empty {R ι κ : Type*} [CommRing R]
    (M : Matrix ι κ R) (i : ι) (j : κ) :
    bareissMinor M (Fin.elim0 : Fin 0 → ι) (Fin.elim0 : Fin 0 → κ) i j = M i j := by
  let : Unique (Fin 0 ⊕ Unit) :=
    { default := Sum.inr (), uniq := by
        intro x
        rcases x with x | ⟨⟩
        · exact x.elim0
        · rfl }
  rw [bareissMinor, Matrix.det_unique]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Bordered minors commute with coefficient homomorphisms. -/
theorem bareissMinor_map {R S α ι κ : Type*} [CommRing R] [CommRing S]
    [Fintype α] [DecidableEq α] (f : R →+* S) (M : Matrix ι κ R)
    (rows : α → ι) (cols : α → κ) (i : ι) (j : κ) :
    f (bareissMinor M rows cols i j) = bareissMinor (M.map f) rows cols i j := by
  simp only [bareissMinor, bareissBorder, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.fromBlocks_map]
  rfl

end Gosper.Algorithm
