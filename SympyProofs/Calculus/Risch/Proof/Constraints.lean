module

public import SympyProofs.Calculus.Risch.Program.Constraints
public import SympyProofs.Calculus.Risch.Proof.Normal
public import SympyProofs.Calculus.Risch.Proof.Linear
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Ring

/-! The Lemma of Risch (1969, p. 178): a linear equation whose coefficients lie in the field
of a tower and whose unknowns are constants is equivalent to a finite linear system over
the rationals, because the generators are algebraically independent over the constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open MPoly Linear

variable (k : Type) [Field k] [CharZero k]

/-- Substitute the generators of the tower field in a polynomial over the constants. -/
noncomputable abbrev specializeK (n : ℕ) : MvPolynomial (Fin n) k →+* K k n :=
  MvPolynomial.eval₂Hom (constHom k n) (gens k n)

/-- The generators of a tower field are algebraically independent over the constants. -/
theorem specializeK_injective : ∀ n : ℕ, Function.Injective (specializeK k n)
  | 0 => by
    let e := MvPolynomial.isEmptyAlgEquiv k (Fin 0)
    have he : specializeK k 0 = (RingHom.id k).comp e.toRingHom := by
      apply MvPolynomial.ringHom_ext'
      · ext c
        simp [specializeK, constHom, e]
      · exact fun i => i.elim0
    rw [he]
    exact (RingHom.id k).injective.comp e.injective
  | n + 1 => by
    have ih := specializeK_injective n
    let v := specializeK k n
    let rot := MvPolynomial.renameEquiv k (finRotate (n + 1))
    let e := MvPolynomial.finSuccEquiv k n
    let P := Polynomial.mapRingHom v
    let ι := algebraMap (Polynomial (K k n)) (RatFunc (K k n))
    have he : specializeK k (n + 1) = ι.comp (P.comp (e.toRingHom.comp rot.toRingHom)) := by
      apply MvPolynomial.ringHom_ext'
      · ext c
        have hC : e (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
          simp [e, MvPolynomial.finSuccEquiv_apply]
        have hrot : rot (MvPolynomial.C c) = MvPolynomial.C c := by simp [rot]
        change specializeK k (n + 1) (MvPolynomial.C c) =
          ι (Polynomial.map v (e (rot (MvPolynomial.C c))))
        rw [hrot, hC, Polynomial.map_C]
        simp [specializeK, v, ι, RatFunc.algebraMap_C]
        rfl
      · simp only [specializeK, MvPolynomial.eval₂Hom_X']
        change ∀ i, gens k (n + 1) i = ι (Polynomial.map v (e (rot (MvPolynomial.X i))))
        apply Fin.lastCases
        · simp only [rot, e, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
            finRotate_last, MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, ι,
            RatFunc.algebraMap_X]
          simp [gens]
        · intro j
          have hrot : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
          simp only [rot, e, ι, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, hrot,
            MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, RatFunc.algebraMap_C]
          simp [v, specializeK, gens]
    rw [he]
    exact (RatFunc.algebraMap_injective _).comp ((Polynomial.map_injective v ih).comp
      (e.injective.comp rot.injective))

variable {k} {n : ℕ}

/-- A polynomial with rational coefficients, over the constants. -/
noncomputable def asPolyK (p : MPoly n) : MvPolynomial (Fin n) k :=
  MvPolynomial.map (Rat.castHom k) (asPoly p)

theorem specializeK_asPolyK (p : MPoly n) :
    specializeK k n (asPolyK p) = specialize (gens k n) (asPoly p) := by
  rw [asPolyK, specializeK, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
  congr 1
  exact Subsingleton.elim _ _

theorem coeff_asPolyK (p : MPoly n) (μ : Mono n) :
    (asPolyK (k := k) p).coeff (exps μ) = ((MPoly.coeff μ p : ℚ) : k) := by
  rw [asPolyK, MvPolynomial.coeff_map, asPoly_coeff]
  rfl

/-- A combination of polynomials with constant coefficients. -/
noncomputable def combine : List k → List (MPoly n) → MvPolynomial (Fin n) k
  | c :: cs, w :: ws => MvPolynomial.C c * asPolyK w + combine cs ws
  | _, _ => 0

theorem combine_map_mul (g : MPoly n) : ∀ (cs : List k) (ws : List (MPoly n)),
    combine cs (ws.map fun w => w.mul g) = combine cs ws * asPolyK g
  | [], _ => by simp [combine]
  | _ :: _, [] => by simp [combine]
  | c :: cs, w :: ws => by
    rw [List.map_cons, combine, combine, combine_map_mul g cs ws, asPolyK, asPolyK, asPolyK,
      asPoly_mul, map_mul]
    ring

theorem coeff_combine (μ : Mono n) : ∀ (ws : List (MPoly n)) (p : List k),
    (combine p ws).coeff (exps μ) = dotK (ws.map (MPoly.coeff μ)) p
  | [], p => by cases p <;> simp [combine, dotK]
  | w :: ws, [] => by simp [combine, dotK]
  | w :: ws, c :: cs => by
    have ih := coeff_combine μ ws cs
    simp only [dotK] at ih
    rw [combine, AddMonoidAlgebra.coeff_add]
    change (MvPolynomial.C c * asPolyK w).coeff (exps μ) + (combine cs ws).coeff (exps μ) = _
    rw [MvPolynomial.coeff_C_mul, coeff_asPolyK, ih]
    simp only [dotK, List.map_cons, List.zipWith_cons_cons, List.sum_cons]
    ring

theorem numerators_spec : ∀ {as : List (Term n)}, (∀ a ∈ as, Term.InDomain k a) →
    specialize (gens k n) (asPoly (numerators as).2) ≠ 0 ∧ ∀ p : List k,
      specializeK k n (combine p (numerators as).1) =
        linComb p as * specialize (gens k n) (asPoly (numerators as).2)
  | [], _ => by
    refine ⟨by simp [numerators], fun p => ?_⟩
    cases p <;> simp [numerators, combine, linComb]
  | a :: as, h => by
    obtain ⟨dn, ih⟩ := numerators_spec (as := as) fun e he => h e (List.mem_cons_of_mem _ he)
    obtain ⟨fe, fn⟩ := Term.fraction_spec (gens k n) a (h a List.mem_cons_self)
    change specialize (gens k n) (asPoly a.fraction.1) =
      Term.value k a * specialize (gens k n) (asPoly a.fraction.2) at fe
    refine ⟨by simp only [numerators, asPoly_mul, map_mul]; exact mul_ne_zero fn dn, fun p => ?_⟩
    cases p with
    | nil => simp [combine, linComb]
    | cons c cs =>
      have cC : specializeK k n (MvPolynomial.C c) = constHom k n c := by simp [specializeK]
      simp only [numerators, combine, combine_map_mul, map_add, map_mul, cC, ih cs,
        specializeK_asPolyK, asPoly_mul, fe, linComb_cons]
      ring

/-- The Lemma: constants solve the linear equation over the field of the tower exactly when
they solve the linear system over the rationals. -/
theorem rowsOf_spec {as : List (Term n)} (h : ∀ a ∈ as, Term.InDomain k a) (p : List k) :
    (∀ row ∈ rowsOf as, dotK row p = 0) ↔ linComb p as = 0 := by
  obtain ⟨dn, spec⟩ := numerators_spec h
  have sp := spec p
  constructor
  · intro rows
    have zero : combine p (numerators as).1 = 0 := by
      ext f
      obtain ⟨m, rfl⟩ := exists_exps f
      rw [coeff_combine]
      by_cases mem : m ∈ monomials (numerators as).1
      · exact rows _ (List.mem_map.mpr ⟨m, mem, rfl⟩)
      · apply dotK_zero_row
        intro e he
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
        apply coeff_eq_zero_of_absent
        intro t ht e
        exact mem (List.mem_flatMap.mpr ⟨w, hw, List.mem_map.mpr ⟨t, ht, e⟩⟩)
    rw [zero, map_zero] at sp
    exact (mul_eq_zero.mp sp.symm).resolve_right dn
  · intro zero row hr
    obtain ⟨μ, -, rfl⟩ := List.mem_map.mp hr
    rw [zero, zero_mul] at sp
    have z : combine p (numerators as).1 = 0 :=
      specializeK_injective k n (sp.trans (map_zero _).symm)
    rw [← coeff_combine, z]
    rfl

end SympyProofs.Calculus.Risch
