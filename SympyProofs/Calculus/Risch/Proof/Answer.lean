module

public import SympyProofs.Calculus.Risch.Spec.Answer
public import SympyProofs.Calculus.Risch.Proof.Elementary
import Mathlib.Tactic.Ring

/-! The derivative of an answer is an elementary form, and an answer over the field below a
generator is an answer over the field above it, with the same derivative. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial

noncomputable local instance intAlgebraAnswer {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

namespace Term

/-- Evaluation commutes with a homomorphism of fields. -/
theorem eval_map {F G : Type*} [Field F] [Field G] (φ : F →+* G) (g : Fin n → F) (e : Term n) :
    φ (e.eval g) = e.eval fun i => φ (g i) := by
  induction e with
  | const q => simp [eval]
  | gen i => rfl
  | neg a ih => simp [eval, ih]
  | add a b ha hb => simp [eval, ha, hb]
  | sub a b ha hb => simp [eval, ha, hb]
  | mul a b ha hb => simp [eval, ha, hb]
  | div a b ha hb => simp [eval, ha, hb]

theorem defined_map {F G : Type*} [Field F] [Field G] (φ : F →+* G) (g : Fin n → F)
    (e : Term n) : (e.Defined fun i => φ (g i)) ↔ e.Defined g := by
  induction e with
  | const | gen => exact Iff.rfl
  | neg a ih => exact ih
  | add a b ha hb | sub a b ha hb | mul a b ha hb => exact and_congr ha hb
  | div a b ha hb =>
    change _ ∧ _ ∧ b.eval (fun i => φ (g i)) ≠ 0 ↔ _ ∧ _ ∧ b.eval g ≠ 0
    rw [ha, hb, ← eval_map, _root_.map_ne_zero]

theorem eval_rename {F : Type*} [Field F] {m : ℕ} (σ : Fin n → Fin m) (g : Fin m → F)
    (e : Term n) : (e.rename σ).eval g = e.eval fun i => g (σ i) := by
  induction e <;> simp [rename, eval, *]

theorem defined_rename {F : Type*} [Field F] {m : ℕ} (σ : Fin n → Fin m) (g : Fin m → F)
    (e : Term n) : (e.rename σ).Defined g ↔ e.Defined fun i => g (σ i) := by
  induction e <;> simp [rename, Defined, eval_rename, *]

end Term

namespace RootSum

theorem mem_roots {s : RootSum n} (hm : Poly.model k s.modulus ≠ 0) (c : k) :
    c ∈ s.roots k ↔ (Poly.model k s.modulus).IsRoot (constHom k n c) := by
  classical
  rw [roots, Finset.mem_preimage, Multiset.mem_toFinset, Polynomial.mem_roots hm]

/-- The values of the generators one level up, on the renumbered generators. -/
theorem env_weaken (c : k) (i : Fin (n + 1)) :
    env k (n := n + 1) c
        ((Fin.lastCases (Fin.last (n + 1)) fun j => j.castSucc.castSucc :
          Fin (n + 1) → Fin (n + 2)) i) =
      RatFunc.C (env k c i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [env, Fin.lastCases_last]
    rfl
  · simp [env, gens]

theorem argAt_weaken (s : RootSum n) (c : k) :
    s.weaken.argAt k c = RatFunc.C (s.argAt k c) := by
  rw [argAt, weaken, Term.eval_rename, argAt, Term.eval_map]
  congr 1
  funext i
  exact env_weaken c i

theorem roots_weaken (s : RootSum n) : s.weaken.roots k = s.roots k := by
  classical
  ext c
  by_cases hm : Poly.model k s.modulus = 0
  · have hm' : Poly.model k s.weaken.modulus = 0 := by
      change Poly.model k (s.modulus.map Term.weaken) = 0
      rw [Poly.model_map_weaken, hm, Polynomial.map_zero]
    simp [roots, hm, hm']
  · have hm' : Poly.model k s.weaken.modulus ≠ 0 := by
      change Poly.model k (s.modulus.map Term.weaken) ≠ 0
      rw [Poly.model_map_weaken]
      exact (Polynomial.map_ne_zero_iff RatFunc.C_injective).mpr hm
    rw [mem_roots hm', mem_roots hm]
    change (Poly.model k (s.modulus.map Term.weaken)).IsRoot _ ↔ _
    rw [Poly.model_map_weaken, constHom_succ, IsRoot.def, IsRoot.def, eval_map_apply,
      map_eq_zero_iff _ RatFunc.C_injective]

theorem regular_weaken {s : RootSum n} (h : s.Regular k) : s.weaken.Regular k := by
  obtain ⟨hm, hr⟩ := h
  refine ⟨?_, fun c hc => ?_⟩
  · change Poly.model k (s.modulus.map Term.weaken) ≠ 0
    rw [Poly.model_map_weaken]
    exact (Polynomial.map_ne_zero_iff RatFunc.C_injective).mpr hm
  · rw [roots_weaken] at hc
    obtain ⟨d, nz⟩ := hr c hc
    refine ⟨?_, ?_⟩
    · rw [weaken, Term.defined_rename]
      have e : (fun i => env k (n := n + 1) c
          ((Fin.lastCases (Fin.last (n + 1)) fun j => j.castSucc.castSucc :
            Fin (n + 1) → Fin (n + 2)) i)) =
          fun i => (RatFunc.C : K k n →+* K k (n + 1)) (env k c i) :=
        funext fun i => env_weaken c i
      rw [e, Term.defined_map]
      exact d
    · rw [argAt_weaken]
      exact (_root_.map_ne_zero _).mpr nz

theorem deriv_weaken_prim (t : Tower n) (b : Term n) (s : RootSum n) :
    s.weaken.deriv k (t.prim b) = RatFunc.C (s.deriv k t) := by
  rw [deriv, deriv, roots_weaken, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [argAt_weaken, Tower.der_prim_C, map_mul, map_div₀]
  rfl

theorem deriv_weaken_exp (t : Tower n) (u : Term n) (s : RootSum n) :
    s.weaken.deriv k (t.exp u) = RatFunc.C (s.deriv k t) := by
  rw [deriv, deriv, roots_weaken, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [argAt_weaken, Tower.der_exp_C, map_mul, map_div₀]
  rfl

/-- The derivative of a sum of logarithms is an elementary form. -/
theorem deriv_elementary (t : Tower n) (s : RootSum n) : t.Elementary k (s.deriv k t) := by
  classical
  rw [deriv]
  induction s.roots k using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact Tower.Elementary.zero
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact ((Tower.Elementary.logDeriv _).const_mul a).add ih

end RootSum

namespace Answer

theorem regular_weaken {a : Answer n} (h : a.Regular k) : a.weaken.Regular k := by
  refine ⟨(Term.inDomain_weaken _).mpr h.1, fun s hs => ?_⟩
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  exact RootSum.regular_weaken (h.2 s' hs')

theorem deriv_weaken_prim (t : Tower n) (b : Term n) (a : Answer n) :
    a.weaken.deriv k (t.prim b) = RatFunc.C (a.deriv k t) := by
  rw [deriv, deriv, weaken, Term.value_weaken, Tower.der_prim_C, map_add]
  congr 1
  induction a.sums with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons, map_add] at ih ⊢
    rw [ih, RootSum.deriv_weaken_prim]

theorem deriv_weaken_exp (t : Tower n) (u : Term n) (a : Answer n) :
    a.weaken.deriv k (t.exp u) = RatFunc.C (a.deriv k t) := by
  rw [deriv, deriv, weaken, Term.value_weaken, Tower.der_exp_C, map_add]
  congr 1
  induction a.sums with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons, map_add] at ih ⊢
    rw [ih, RootSum.deriv_weaken_exp]

/-- The derivative of an answer is an elementary form. -/
theorem deriv_elementary (t : Tower n) (a : Answer n) : t.Elementary k (a.deriv k t) := by
  rw [deriv]
  refine (Tower.Elementary.der _).add ?_
  induction a.sums with
  | nil => simpa using Tower.Elementary.zero
  | cons s ss ih =>
    rw [List.map_cons, List.sum_cons]
    exact (RootSum.deriv_elementary t s).add ih

theorem deriv_addField (t : Tower n) (W : Term n) (a : Answer n) :
    (a.addField W).deriv k t = t.der k (Term.value k W) + a.deriv k t := by
  rw [deriv, deriv, addField]
  change t.der k (Term.value k W + Term.value k a.field) + _ = _
  rw [map_add]
  ring

end Answer

end SympyProofs.Calculus.Risch
