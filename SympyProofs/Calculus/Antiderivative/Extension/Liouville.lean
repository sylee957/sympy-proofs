module

public import Mathlib.FieldTheory.Differential.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The notions of Liouville's theorem for an abstract differential field `F`: Liouville
forms over `F`, and elementary extensions of `F`. `integrate_no_primitive` quantifies over
the elementary extensions defined here, and `ElementaryTower.form_of_primitive` is
Liouville's theorem for them. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Extension.LiouvilleForm

open Differential

/-- An element `v` of a differential field `L` over `F` is in Liouville form over `F` when
`v = Σ cᵢ uᵢ′/uᵢ + w′` for finitely many `uᵢ` and `w` in `L` and constants `cᵢ` of `F`. With
`L` the field of a tower, this is `Tower.Elementary` (`Tower.elementary_iff_form`). -/
def InLiouvilleForm (F : Type*) [Field F] [Differential F] {L : Type*} [Field L]
    [Differential L] [Algebra F L] (v : L) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ i, (c i)′ = 0) (u : ι → L) (w : L),
    v = ∑ i, algebraMap F L (c i) * logDeriv (u i) + w′

universe u

/-- One step `L` over `K` of an elementary extension: a finite algebraic extension, or
`L = K(θ)` with `θ` transcendental over `K`, where either `θ′ = g′θ` (an exponential of `g`)
or `θ′ = g′/g` (a logarithm of `g`, where `g′/g` has no primitive in `K`). In the second
case `L` is given with an isomorphism from the field of rational functions over `K`, which
takes `X` to `θ`. -/
inductive ElementaryStep (K L : Type u) [Field K] [Field L] [Differential K] [Differential L]
    [Algebra K L] : Prop where
  | algebraic [FiniteDimensional K L] : ElementaryStep K L
  | exp (e : RatFunc K ≃ₐ[K] L) (g : K)
      (dx : (e RatFunc.X)′ = algebraMap K L g′ * e RatFunc.X) : ElementaryStep K L
  | log (e : RatFunc K ≃ₐ[K] L) (g : K)
      (nonprim : ¬ ∃ w : K, w′ = logDeriv g)
      (dx : (e RatFunc.X)′ = algebraMap K L (logDeriv g)) : ElementaryStep K L

/-- An elementary extension `L` of `F`: finitely many `ElementaryStep`s, starting from `F`,
each a differential field extension of the one before. The constants of every field before
the last step lie in `F`, the hypothesis of Liouville's theorem. -/
inductive ElementaryTower (F : Type u) [Field F] [Differential F] :
    (L : Type u) → [Field L] → [Differential L] → [Algebra F L] → Prop where
  | base : ElementaryTower F F
  | adjoin {K L : Type u} [Field K] [Field L] [Differential K] [Differential L]
      [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
      [DifferentialAlgebra F K] [DifferentialAlgebra K L] [ContainConstants F K]
      (lower : ElementaryTower F K) (step : ElementaryStep K L) : ElementaryTower F L

end SympyProofs.Calculus.Antiderivative.Extension.LiouvilleForm
