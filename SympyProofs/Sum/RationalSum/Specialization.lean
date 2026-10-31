module

public import SympyProofs.Sum.RationalSum.Model

/-! Specialization of the reduction model, without injectivity assumptions. -/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial
open scoped Classical

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]

def ShiftSum.map (f : R →ₐ[ℚ] S) (s : ShiftSum R) : ShiftSum S :=
  { numerator := s.numerator.map f.toRingHom
    denominator := s.denominator
    length := s.length }

def Residual.map (f : R →ₐ[ℚ] S) (s : Residual R) : Residual S :=
  { base := s.base, numerators := s.numerators.map (Polynomial.map f.toRingHom) }

def Result.map (f : R →ₐ[ℚ] S) (s : Result R) : Result S :=
  { polynomial := s.polynomial.map f.toRingHom
    rational := s.rational.map (ShiftSum.map f)
    residual := s.residual.map (Residual.map f) }

/-- Exactly the monicity conditions needed for specialization of division. -/
structure PreparedDenominator.Monic (p : PreparedDenominator) : Prop where
  denominator : p.monicDenominator.Monic
  factors : ∀ g ∈ p.groups, ∀ o ∈ g.occurrences, o.factor.Monic ∧ o.power.Monic

@[simp] theorem map_rationalPolynomial (f : R →ₐ[ℚ] S) (p : Polynomial ℚ) :
    (p.map (algebraMap ℚ R)).map f.toRingHom = p.map (algebraMap ℚ S) := by
  rw [Polynomial.map_map]
  congr 1
  exact f.comp_algebraMap

theorem array_map_modify {α β : Type*} (f : α → β) (u : α → α) (v : β → β)
    (h : ∀ x, f (u x) = v (f x)) (a : Array α) (i : ℕ) :
    (a.modify i u).map f = (a.map f).modify i v := by
  apply Array.ext
  · simp
  · intro j hj hk
    simp only [Array.getElem_map, Array.getElem_modify]
    split <;> simp_all

theorem foldl_map_mem {α β γ : Type*} (f : α → β)
    (u : α → γ → α) (v : β → γ → β) (l : List γ)
    (h : ∀ y ∈ l, ∀ x, v (f x) y = f (u x y)) (a : α) :
    l.foldl v (f a) = f (l.foldl u a) := by
  induction l generalizing a with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, h y (by simp)]
    exact ih (fun z hz => h z (by simp [hz])) _

namespace Model

def mapDigit (f : R →ₐ[ℚ] S)
    (s : Array (ShiftSum R) × Array (Polynomial R) × Polynomial R) :=
  (s.1.map (ShiftSum.map f), s.2.1.map (Polynomial.map f.toRingHom), s.2.2.map f.toRingHom)

def mapOccurrence (f : R →ₐ[ℚ] S) (s : Array (ShiftSum R) × Array (Polynomial R)) :=
  (s.1.map (ShiftSum.map f), s.2.map (Polynomial.map f.toRingHom))

def mapGroup (f : R →ₐ[ℚ] S) (s : Array (ShiftSum R) × Array (Residual R)) :=
  (s.1.map (ShiftSum.map f), s.2.map (Residual.map f))

theorem digit_map (f : R →ₐ[ℚ] S) (g : PreparedGroup) (o : PreparedOccurrence)
    (ho : o.factor.Monic) (s) (j : ℕ) :
    digit g o (mapDigit f s) j = mapDigit f (digit g o s j) := by
  have ha := array_map_modify (Polynomial.map f.toRingHom)
    (· + taylor ((-o.shift : ℤ) : R) (s.2.2 %ₘ o.factor.map (algebraMap ℚ R)))
    (· + taylor ((-o.shift : ℤ) : S) ((s.2.2.map f.toRingHom) %ₘ o.factor.map (algebraMap ℚ S)))
    (by intro x; simp [Polynomial.map_map, f.comp_algebraMap, Polynomial.map_modByMonic _ (ho.map _)] )
    s.2.1 (o.multiplicity - j - 1)
  simp only [Int.cast_neg] at ha
  simp only [digit, mapDigit]
  split <;> simp [Polynomial.map_map, f.comp_algebraMap, ShiftSum.map, Polynomial.map_modByMonic _ (ho.map _),
    Polynomial.map_divByMonic _ (ho.map _)] <;> exact ha.symm

theorem occurrence_map (f : R →ₐ[ℚ] S) (N : Polynomial R) (g : PreparedGroup)
    (o : PreparedOccurrence) (ho : o.factor.Monic ∧ o.power.Monic) (s) :
    occurrence (N.map f.toRingHom) g (mapOccurrence f s) o =
      mapOccurrence f (occurrence N g s o) := by
  have hi :
      ((mapOccurrence f s).1, (mapOccurrence f s).2,
        (N.map f.toRingHom * o.inverse.map (algebraMap ℚ S)) %ₘ o.power.map (algebraMap ℚ S)) =
      mapDigit f (s.1, s.2, (N * o.inverse.map (algebraMap ℚ R)) %ₘ
        o.power.map (algebraMap ℚ R)) := by
    simp [Polynomial.map_map, f.comp_algebraMap, mapOccurrence, mapDigit, Polynomial.map_modByMonic _ (ho.2.map _)]
  simp only [occurrence, hi, List.foldl_hom (mapDigit f) (digit_map f g o ho.1)]
  rfl

theorem group_map (f : R →ₐ[ℚ] S) (N : Polynomial R) (g : PreparedGroup)
    (hg : ∀ o ∈ g.occurrences, o.factor.Monic ∧ o.power.Monic) (s) :
    group (N.map f.toRingHom) (mapGroup f s) g = mapGroup f (group N s g) := by
  have hi : ((mapGroup f s).1, Array.replicate g.maxMultiplicity (0 : Polynomial S)) =
      mapOccurrence f (s.1, Array.replicate g.maxMultiplicity (0 : Polynomial R)) := by
    simp [mapGroup, mapOccurrence]
  have hf := foldl_map_mem (mapOccurrence f) (occurrence N g)
    (occurrence (N.map f.toRingHom) g) g.occurrences.toList
    (fun o ho s => occurrence_map f N g o (hg o (by simpa using ho)) s)
    (s.1, Array.replicate g.maxMultiplicity 0)
  simp only [group, hi, hf]
  simp [mapGroup, mapOccurrence, Residual.map]

end Model

/-- Reducing and then specializing gives exactly the same polynomial output as
specializing first. The algebra homomorphism need not be injective. -/
theorem model_map
    (f : R →ₐ[ℚ] S) (p : PreparedDenominator) (hp : p.Monic) (P : Polynomial R) :
    Model.result p (P.map f.toRingHom) = (Model.result p P).map f := by
  let A := C (algebraMap ℚ R p.coefficient⁻¹) * P
  let D := p.monicDenominator.map (algebraMap ℚ R)
  have hA : C (algebraMap ℚ S p.coefficient⁻¹) * P.map f.toRingHom = A.map f.toRingHom := by
    simp only [A, Polynomial.map_mul, Polynomial.map_C]
    exact congrArg (fun c : S => C c * P.map f.toRingHom) (f.commutes _).symm
  have hN := Polynomial.map_modByMonic f.toRingHom (hp.denominator.map (algebraMap ℚ R)) (p := A)
  have hQ := Polynomial.map_divByMonic f.toRingHom (hp.denominator.map (algebraMap ℚ R)) (p := A)
  have hf := foldl_map_mem (Model.mapGroup f) (Model.group (A %ₘ D))
    (Model.group ((A %ₘ D).map f.toRingHom)) p.groups.toList
    (fun g hg s => Model.group_map f (A %ₘ D) g (hp.factors g (by simpa using hg)) s)
    (#[], #[])
  simp only [Model.result, hA, ← map_rationalPolynomial f p.monicDenominator,
    ← hN, ← hQ, ← PolynomialSum.antidifference_map]
  change Result.mk _ _ _ = Result.mk _ _ _
  have hi : Model.mapGroup f (#[], #[]) = (#[], #[]) := by simp [Model.mapGroup]
  rw [hi] at hf
  rw [hf]
  rfl

end Gosper.RationalSum
