module

public import SympyProofs.Calculus.Risch.Program.Linear
public import SympyProofs.Calculus.Risch.Spec.Linear
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.List.GetD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The specification of the linear algebra programs. The rows of a system are rational,
and the unknowns range over a field `k` of characteristic zero: the generators computed by
`kernel` span the solutions over `k`, `eliminate` removes one unknown, and `normalized`
finds a solution with first coordinate `1` exactly when one exists over `k`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.Linear

variable {k : Type} [Field k] [CharZero k]

/-- A combination over `k` of rational vectors, coordinatewise. -/
def lsum (es : List k) (G : List (List ℚ)) (i : ℕ) : k :=
  (List.zipWith (fun (e : k) (g : List ℚ) => e * ((g.getD i 0 : ℚ) : k)) es G).sum

/-! ### Rows applied to vectors -/

theorem dotK_cast : ∀ (row x : List ℚ),
    dotK row (x.map fun (q : ℚ) => (q : k)) = ((dot row x : ℚ) : k)
  | [], x => by simp [dotK, dot]
  | a :: row, [] => by simp [dotK, dot]
  | a :: row, c :: x => by
    change (a : k) * (c : k) + dotK row (x.map fun (q : ℚ) => (q : k)) =
      ((a * c + dot row x : ℚ) : k)
    rw [dotK_cast row x]
    push_cast
    rfl

omit [CharZero k] in
theorem dotK_eq_sum : ∀ (x : List k) (row : List ℚ),
    dotK row x = ∑ i ∈ Finset.range x.length, ((row.getD i 0 : ℚ) : k) * x.getD i 0
  | [], row => by simp [dotK]
  | c :: x, [] => by simp [dotK]
  | c :: x, r :: row => by
    change (r : k) * c + dotK row x = _
    rw [dotK_eq_sum x row, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

omit [CharZero k] in
theorem dotK_append {r s : List ℚ} {c d : List k} (h : r.length = c.length) :
    dotK (r ++ s) (c ++ d) = dotK r c + dotK s d := by
  simp [dotK, List.zipWith_append h]

omit [CharZero k] in
theorem dotK_snoc (r : List ℚ) (α : List k) (c : k) :
    dotK r (α ++ [c]) = dotK r α + ((r.getD α.length 0 : ℚ) : k) * c := by
  rw [dotK_eq_sum, dotK_eq_sum, List.length_append, List.length_singleton,
    Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]
  · rw [List.getD_append_right _ _ _ _ le_rfl]
    simp

omit [CharZero k] in
theorem dotK_zero_row : ∀ (row : List ℚ) (p : List k), (∀ e ∈ row, e = 0) → dotK row p = 0
  | [], p, _ => by simp [dotK]
  | r :: row, [], _ => by simp [dotK]
  | r :: row, c :: p, h => by
    change (r : k) * c + dotK row p = 0
    rw [dotK_zero_row row p fun y hy => h y (List.mem_cons_of_mem _ hy),
      h r List.mem_cons_self]
    simp

omit [CharZero k] in
theorem getD_map_cast (g : List ℚ) (i : ℕ) :
    (g.map fun (q : ℚ) => (q : k)).getD i 0 = ((g.getD i 0 : ℚ) : k) := by
  by_cases hi : i < g.length
  · simp [List.getD, hi]
  · simp [List.getD, hi]

theorem getD_map_range (N : ℕ) (f : ℕ → ℚ) (i : ℕ) :
    ((List.range N).map f).getD i 0 = if i < N then f i else 0 := by
  by_cases hi : i < N
  · simp [List.getD, hi]
  · simp [List.getD, hi]

/-! ### Unit vectors -/

theorem length_unit : ∀ m i, (unit m i).length = m
  | 0, _ => rfl
  | m + 1, 0 => by simp [unit]
  | m + 1, i + 1 => by simp [unit, length_unit m i]

omit [CharZero k] in
theorem dotK_unit : ∀ (m i : ℕ) (v : List k), i < m → dotK (unit m i) v = v.getD i 0
  | 0, _, _, h => by omega
  | m + 1, 0, [], _ => by simp [unit, dotK]
  | m + 1, 0, c :: v, _ => by
    change ((1 : ℚ) : k) * c + dotK (List.replicate m 0) v = c
    rw [dotK_zero_row (List.replicate m 0) v fun e he => List.eq_of_mem_replicate he]
    simp
  | m + 1, i + 1, [], _ => by simp [unit, dotK]
  | m + 1, i + 1, c :: v, h => by
    change ((0 : ℚ) : k) * c + dotK (unit m i) v = v.getD i 0
    rw [dotK_unit m i v (by omega)]
    simp

theorem getD_unit : ∀ (m i j : ℕ), i < m → (unit m i).getD j 0 = if j = i then 1 else 0
  | 0, _, _, h => by omega
  | m + 1, 0, 0, _ => by simp [unit]
  | m + 1, 0, j + 1, _ => by
    simp only [unit, List.getD_cons_succ]
    by_cases hj : j < m
    · simp [List.getD, hj]
    · simp [List.getD, hj]
  | m + 1, i + 1, 0, _ => by simp [unit]
  | m + 1, i + 1, j + 1, h => by
    simp only [unit, List.getD_cons_succ, getD_unit m i j (by omega)]
    simp

/-! ### Vectors as functions -/

variable (k) in
/-- A rational vector as a function on indices with values in `k`, zero beyond its length. -/
def fn (v : List ℚ) : ℕ → k := fun i => ((v.getD i 0 : ℚ) : k)

/-- A vector over `k` as a function on indices, zero beyond its length. -/
def vec (x : List k) : ℕ → k := fun i => x.getD i 0

/-- The linear form of a row on the first `M` coordinates. -/
noncomputable def form (M : ℕ) (r : List ℚ) : (ℕ → k) →ₗ[k] k where
  toFun f := ∑ i ∈ Finset.range M, ((r.getD i 0 : ℚ) : k) * f i
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

omit [CharZero k] in
theorem dotK_eq_form {M : ℕ} (r : List ℚ) {x : List k} (hx : x.length = M) :
    dotK r x = form M r (vec x) := by
  rw [dotK_eq_sum, hx]
  rfl

theorem form_fn {M : ℕ} (r : List ℚ) {g : List ℚ} (hg : g.length = M) :
    form M r (fn k g) = ((dot r g : ℚ) : k) := by
  rw [← dotK_cast, dotK_eq_sum, List.length_map, hg]
  change ∑ i ∈ Finset.range M, ((r.getD i 0 : ℚ) : k) * ((g.getD i 0 : ℚ) : k) = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_map_cast]

theorem length_vsub (M : ℕ) (u : List ℚ) (c : ℚ) (w : List ℚ) : (vsub M u c w).length = M := by
  simp [vsub]

theorem fn_vsub {M : ℕ} {u w : List ℚ} (c : ℚ) (hu : u.length = M) (hw : w.length = M) :
    fn k (vsub M u c w) = fn k u - (c : k) • fn k w := by
  funext i
  simp only [fn, vsub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, getD_map_range]
  by_cases hi : i < M
  · rw [ite_eq_left hi]
    push_cast
    rfl
  · rw [ite_eq_right hi, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    simp

/-! ### The span of the generators -/

variable (k) in
/-- The span over `k` of a list of rational vectors, as functions. -/
def span (G : List (List ℚ)) : Submodule k (ℕ → k) :=
  Submodule.span k (fn k '' {g | g ∈ G})

/-- A step keeps the lengths, and cuts the span down to the solutions of its equation. -/
theorem step_spec {M : ℕ} (r : List ℚ) {G : List (List ℚ)} (hG : ∀ g ∈ G, g.length = M) :
    (∀ g ∈ step M r G, g.length = M) ∧
      span k (step M r G) = span k G ⊓ LinearMap.ker (form (k := k) M r) := by
  rw [step]
  cases hfind : G.find? (fun g => dot r g != 0) with
  | none =>
    refine ⟨hG, ?_⟩
    have all := List.find?_eq_none.mp hfind
    apply le_antisymm
    · refine le_inf le_rfl ?_
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, rfl⟩
      have zero : dot r g = 0 := by simpa using all g hg
      rw [SetLike.mem_coe, LinearMap.mem_ker, form_fn r (hG g hg), zero, Rat.cast_zero]
    · exact inf_le_left
  | some w =>
    have hw : w ∈ G := List.mem_of_find?_eq_some hfind
    have hc : dot r w ≠ 0 := by simpa using List.find?_some hfind
    have wl := hG w hw
    have cform : form M r (fn k w) ≠ 0 := by
      rw [form_fn r wl]
      exact Rat.cast_ne_zero.mpr hc
    refine ⟨?_, ?_⟩
    · intro g hg
      obtain ⟨g', -, rfl⟩ := List.mem_map.mp hg
      exact length_vsub _ _ _ _
    obtain ⟨T, hT⟩ : ∃ T : (ℕ → k) →ₗ[k] (ℕ → k),
        ∀ x, T x = x - (form M r x / form M r (fn k w)) • fn k w := by
      refine ⟨LinearMap.id - (form M r).smulRight ((form M r (fn k w))⁻¹ • fn k w), fun x => ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, smul_smul,
        div_eq_mul_inv]
    have Tw : T (fn k w) = 0 := by rw [hT, div_self cform, one_smul, sub_self]
    have Tker (y : ℕ → k) (hy : form M r y = 0) : T y = y := by
      rw [hT, hy, zero_div, zero_smul, sub_zero]
    have image : fn k '' {g | g ∈ (G.erase w).map fun g => vsub M g (dot r g / dot r w) w} =
        T '' (fn k '' {g | g ∈ G.erase w}) := by
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        have gl := hG g' (List.mem_of_mem_erase hg')
        exact ⟨fn k g', ⟨g', hg', rfl⟩, by
          rw [hT, fn_vsub _ gl wl, form_fn r gl, form_fn r wl, Rat.cast_div]⟩
      · rintro ⟨_, ⟨g', hg', rfl⟩, rfl⟩
        have gl := hG g' (List.mem_of_mem_erase hg')
        exact ⟨vsub M g' (dot r g' / dot r w) w, List.mem_map.mpr ⟨g', hg', rfl⟩, by
          rw [hT, fn_vsub _ gl wl, form_fn r gl, form_fn r wl, Rat.cast_div]⟩
    have whole : fn k '' {g | g ∈ G} = insert (fn k w) (fn k '' {g | g ∈ G.erase w}) := by
      have sets : {g | g ∈ G} = insert w {g | g ∈ G.erase w} := by
        ext g
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
        rw [← List.mem_cons, (List.perm_cons_erase hw).mem_iff]
      rw [sets, Set.image_insert_eq]
    rw [span, image, ← Submodule.map_span, span, whole]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have xin : x ∈ Submodule.span k (insert (fn k w) (fn k '' {g | g ∈ G.erase w})) :=
        Submodule.span_mono (Set.subset_insert _ _) hx
      refine ⟨?_, ?_⟩
      · rw [hT]
        exact Submodule.sub_mem _ xin
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      · rw [SetLike.mem_coe, LinearMap.mem_ker, hT, map_sub, map_smul, smul_eq_mul,
          div_mul_cancel₀ _ cform, sub_self]
    · rintro y ⟨hy, hker⟩
      have mapped : T y ∈ Submodule.map T
          (Submodule.span k (insert (fn k w) (fn k '' {g | g ∈ G.erase w}))) := ⟨y, hy, rfl⟩
      rw [Submodule.map_span, Set.image_insert_eq, Tw, Submodule.span_insert_zero,
        ← Submodule.map_span, Tker y (LinearMap.mem_ker.mp hker)] at mapped
      exact mapped

theorem foldl_spec {M : ℕ} : ∀ (rows : List (List ℚ)) {G : List (List ℚ)},
    (∀ g ∈ G, g.length = M) →
    (∀ g ∈ rows.foldl (fun G r => step M r G) G, g.length = M) ∧
      ∀ f : ℕ → k, f ∈ span k (rows.foldl (fun G r => step M r G) G) ↔
        f ∈ span k G ∧ ∀ r ∈ rows, form M r f = 0
  | [], G, hG => ⟨hG, fun f => by simp⟩
  | r :: rows, G, hG => by
    obtain ⟨len, eq⟩ := step_spec (k := k) r hG
    obtain ⟨len', iff⟩ := foldl_spec rows len
    refine ⟨len', fun f => ?_⟩
    rw [List.foldl_cons, iff, eq, Submodule.mem_inf, LinearMap.mem_ker]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem length_of_mem_units {M : ℕ} : ∀ g ∈ (List.range M).map (unit M), g.length = M := by
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  exact length_unit M i

/-- Every generator has the length of the system. -/
theorem length_of_mem_kernel (rows : List (List ℚ)) (M : ℕ) :
    ∀ g ∈ kernel rows M, g.length = M :=
  (foldl_spec (k := ℚ) rows length_of_mem_units).1

/-- The span of the generators consists of the solutions, as functions. -/
theorem mem_span_kernel (rows : List (List ℚ)) (M : ℕ) (f : ℕ → k) :
    f ∈ span k (kernel rows M) ↔
      f ∈ span k ((List.range M).map (unit M)) ∧ ∀ r ∈ rows, form M r f = 0 :=
  (foldl_spec rows length_of_mem_units).2 f

omit [CharZero k] in
theorem mem_span_unit {M : ℕ} {x : List k} (hx : x.length = M) :
    vec x ∈ span k ((List.range M).map (unit M)) := by
  have eq : vec x = ∑ i ∈ Finset.range M, x.getD i 0 • fn k (unit M i) := by
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, fn, vec]
    by_cases hj : j < M
    · rw [Finset.sum_eq_single j]
      · rw [getD_unit M j j hj]
        simp
      · intro i hi hne
        rw [getD_unit M i j (Finset.mem_range.mp hi), ite_eq_right (Ne.symm hne), Rat.cast_zero,
          mul_zero]
      · intro h
        exact (h (Finset.mem_range.mpr hj)).elim
    · rw [List.getD_eq_default _ _ (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      rw [getD_unit M i j (Finset.mem_range.mp hi),
        ite_eq_right (by have := Finset.mem_range.mp hi; omega), Rat.cast_zero, mul_zero]
  rw [eq]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨unit M i, List.mem_map.mpr ⟨i, List.mem_range.mpr
    (Finset.mem_range.mp hi), rfl⟩, rfl⟩

omit [CharZero k] in
theorem mem_span_iff : ∀ (G : List (List ℚ)) (f : ℕ → k),
    f ∈ span k G ↔ ∃ es : List k, es.length = G.length ∧ ∀ i, f i = lsum es G i
  | [], f => by
    have : span k [] = ⊥ := by simp [span]
    rw [this, Submodule.mem_bot]
    constructor
    · rintro rfl
      exact ⟨[], rfl, fun i => by simp [lsum]⟩
    · rintro ⟨es, -, h⟩
      funext i
      simpa [lsum] using h i
  | g :: G, f => by
    have split : span k (g :: G) = Submodule.span k {fn k g} ⊔ span k G := by
      rw [span, span, ← Submodule.span_union]
      congr 1
      ext h
      simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_cons, Set.singleton_union,
        Set.mem_insert_iff]
      constructor
      · rintro ⟨v, rfl | hv, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨v, hv, rfl⟩
      · rintro (rfl | ⟨v, hv, rfl⟩)
        · exact ⟨g, Or.inl rfl, rfl⟩
        · exact ⟨v, Or.inr hv, rfl⟩
    rw [split, Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      obtain ⟨es, el, eh⟩ := (mem_span_iff G b).mp hb
      refine ⟨c :: es, by simp [el], fun i => ?_⟩
      simp [lsum, fn, eh i]
    · rintro ⟨es, el, eh⟩
      cases es with
      | nil => simp at el
      | cons c es =>
        refine ⟨c • fn k g, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
          fun i => lsum es G i, (mem_span_iff G _).mpr ⟨es, by simpa using el, fun _ => rfl⟩, ?_⟩
        funext i
        simp [eh i, lsum, fn]

/-! ### The solution space -/

/-- The generators have the length of the system, and their combinations over `k` are
exactly the solutions over `k`. -/
theorem kernel_spec (rows : List (List ℚ)) (M : ℕ) :
    (∀ g ∈ kernel rows M, g.length = M) ∧
    ∀ x : List k, x.length = M → ((∀ row ∈ rows, dotK row x = 0) ↔
      ∃ es : List k, es.length = (kernel rows M).length ∧
        ∀ i, x.getD i 0 = lsum es (kernel rows M) i) := by
  refine ⟨length_of_mem_kernel rows M, fun x hx => ?_⟩
  change _ ↔ ∃ es : List k, es.length = (kernel rows M).length ∧
    ∀ i, vec x i = lsum es (kernel rows M) i
  rw [← mem_span_iff (kernel rows M) (vec x), mem_span_kernel]
  constructor
  · intro h
    exact ⟨mem_span_unit hx, fun r hr => by rw [← dotK_eq_form r hx]; exact h r hr⟩
  · rintro ⟨-, h⟩ r hr
    rw [dotK_eq_form r hx]
    exact h r hr

/-! ### Elimination of one unknown -/

theorem dotK_reduceRow {m : ℕ} (b c : ℚ) (r p : List ℚ) {α : List k} (hα : α.length = m) :
    dotK (reduceRow m b r c p) α = (b : k) * dotK r α - (c : k) * dotK p α := by
  rw [dotK_eq_sum, dotK_eq_sum, dotK_eq_sum, hα, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [reduceRow, getD_map_range, ite_eq_left (Finset.mem_range.mp hi)]
  push_cast
  ring

/-- The reduced system holds for the first `m` unknowns exactly when the original system
holds for some value of the unknown at position `m`. -/
theorem eliminate_spec {m : ℕ} (rows : List (List ℚ)) {α : List k} (hα : α.length = m) :
    (∀ r ∈ eliminate m rows, dotK r α = 0) ↔ ∃ c : k, ∀ r ∈ rows, dotK r (α ++ [c]) = 0 := by
  unfold eliminate
  cases h : rows.find? (fun r => r.getD m 0 != 0) with
  | none =>
    have all : ∀ r ∈ rows, r.getD m 0 = 0 := by
      intro r hr
      have := List.find?_eq_none.mp h r hr
      simpa using this
    constructor
    · intro H
      exact ⟨0, fun r hr => by
        rw [dotK_snoc, hα, all r hr, Rat.cast_zero, zero_mul, add_zero]
        exact H r hr⟩
    · rintro ⟨c, H⟩ r hr
      have := H r hr
      rwa [dotK_snoc, hα, all r hr, Rat.cast_zero, zero_mul, add_zero] at this
  | some p =>
    have pm : p ∈ rows := List.mem_of_find?_eq_some h
    have pb : p.getD m 0 ≠ 0 := by simpa using List.find?_some h
    have pk : ((p.getD m 0 : ℚ) : k) ≠ 0 := Rat.cast_ne_zero.mpr pb
    constructor
    · intro H
      refine ⟨-(dotK p α) / ((p.getD m 0 : ℚ) : k), fun r hr => ?_⟩
      have := H _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
      rw [dotK_reduceRow _ _ _ _ hα] at this
      rw [dotK_snoc, hα]
      field_simp
      linear_combination this
    · rintro ⟨c, H⟩ r' hr'
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
      rw [dotK_reduceRow _ _ _ _ hα]
      have e1 := H r hr
      have e2 := H p pm
      rw [dotK_snoc, hα] at e1 e2
      linear_combination ((p.getD m 0 : ℚ) : k) * e1 - ((r.getD m 0 : ℚ) : k) * e2

/-! ### A solution with first coordinate one -/

omit [CharZero k] in
theorem lsum_eq_zero {i : ℕ} : ∀ (es : List k) (G : List (List ℚ)),
    (∀ g ∈ G, g.getD i 0 = 0) → lsum es G i = 0
  | [], G, _ => by simp [lsum]
  | e :: es, [], _ => by simp [lsum]
  | e :: es, g :: G, h => by
    change e * ((g.getD i 0 : ℚ) : k) + lsum es G i = 0
    rw [lsum_eq_zero es G fun g hg => h g (List.mem_cons_of_mem _ hg), h g List.mem_cons_self]
    simp

/-- The vector returned by `normalized` is a rational solution with first coordinate `1`. -/
theorem normalized_sound {rows : List (List ℚ)} {M : ℕ} {x : List ℚ}
    (h : normalized rows M = some x) :
    x.length = M ∧ x.getD 0 0 = 1 ∧ ∀ row ∈ rows, dot row x = 0 := by
  unfold normalized at h
  cases hfind : (kernel rows M).find? (fun g => g.getD 0 0 != 0) with
  | none =>
    rw [hfind] at h
    cases h
  | some g =>
    rw [hfind] at h
    obtain rfl := Option.some.inj h
    have hg : g ∈ kernel rows M := List.mem_of_find?_eq_some hfind
    have g0 : g.getD 0 0 ≠ 0 := by simpa using List.find?_some hfind
    have xl : (g.map fun a => a / g.getD 0 0).length = M := by
      rw [List.length_map, length_of_mem_kernel rows M g hg]
    have scaled : fn ℚ (g.map fun a => a / g.getD 0 0) = (g.getD 0 0)⁻¹ • fn ℚ g := by
      funext i
      simp only [fn, Rat.cast_id, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i < g.length
      · simp [List.getD, hi, div_eq_inv_mul]
      · simp [List.getD, hi]
    refine ⟨xl, ?_, fun row hrow => ?_⟩
    · have := congrFun scaled 0
      simp only [fn, Rat.cast_id, Pi.smul_apply, smul_eq_mul] at this
      rw [this, inv_mul_cancel₀ g0]
    · have mem : fn ℚ (g.map fun a => a / g.getD 0 0) ∈ span ℚ (kernel rows M) := by
        rw [scaled]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)
      have zero := ((mem_span_kernel rows M _).mp mem).2 row hrow
      rwa [form_fn row xl, Rat.cast_id] at zero

/-- If the system has a solution over `k` with first coordinate `1`, `normalized` finds a
rational one. -/
theorem normalized_complete {rows : List (List ℚ)} {M : ℕ}
    (h : ∃ x : List k, x.length = M ∧ x.getD 0 0 = 1 ∧ ∀ row ∈ rows, dotK row x = 0) :
    (normalized rows M).isSome := by
  obtain ⟨x, xl, x0, sol⟩ := h
  unfold normalized
  cases hfind : (kernel rows M).find? (fun g => g.getD 0 0 != 0) with
  | some g => rfl
  | none =>
    exfalso
    have all : ∀ g ∈ kernel rows M, g.getD 0 0 = 0 := by
      intro g hg
      have := List.find?_eq_none.mp hfind g hg
      simpa using this
    obtain ⟨es, -, comb⟩ := ((kernel_spec rows M).2 x xl).mp sol
    have := comb 0
    rw [x0, lsum_eq_zero es _ all] at this
    exact one_ne_zero this

end SympyProofs.Calculus.Risch.Linear
