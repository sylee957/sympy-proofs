module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Step
public import Mathlib.MeasureTheory.Constructions.Projective

import Mathlib.Data.Finset.Sort

/-!
# Consistent finite-dimensional laws

Sample the chain at a finite ordered list of times using the transition PMFs.
Unobserved coordinates are filled with an arbitrary state `d`. Restricting to
fewer observation times erases those filler coordinates and uses the semigroup
law to integrate out intermediate observations.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ) (d : ι)

/-- A finitely supported law on paths, with only the listed coordinates sampled. -/
noncomputable def sampleFuture (s : ℝ≥0) (i : ι) : List ℝ≥0 → PMF (ℝ≥0 → ι)
  | [] => PMF.pure (fun _ => d)
  | t :: ts => (step Q (t - s) i).bind fun j =>
      (sampleFuture t j ts).map (fun ω => Function.update ω t j)

/-- Integrating out an initial intermediate observation uses Chapman--Kolmogorov. -/
theorem sampleFuture_skip (s t : ℝ≥0) (hst : s ≤ t) (i : ι) (ts : List ℝ≥0)
    (hts : ∀ u ∈ ts, t ≤ u) :
    (step Q (t - s) i).bind (fun j => sampleFuture Q d t j ts) =
      sampleFuture Q d s i ts := by
  cases ts with
  | nil => simp [sampleFuture]
  | cons u us =>
    simp only [sampleFuture, ← PMF.bind_bind]
    rw [step_add]
    have htime : (t - s) + (u - t) = u - s := by
      rw [add_comm, tsub_add_tsub_cancel (hts u (by simp)) hst]
    rw [htime]

/-- Reading a sampled path at the times in `J` forgets the other observation times. -/
theorem sampleFuture_restrict (J : Finset ℝ≥0) (s : ℝ≥0) (i : ι) (ts : List ℝ≥0)
    (horder : ts.SortedLE) (hstart : ∀ t ∈ ts, s ≤ t) :
    (sampleFuture Q d s i ts).map J.restrict =
      (sampleFuture Q d s i (ts.filter (fun t => decide (t ∈ J)))).map J.restrict := by
  induction ts generalizing s i with
  | nil => simp [sampleFuture]
  | cons t ts ih =>
    obtain ⟨hhead, htail⟩ := List.sortedLE_cons.mp horder
    simp only [sampleFuture, PMF.map_bind, PMF.map_comp]
    by_cases ht : t ∈ J
    · simp only [List.filter_cons, decide_eq_true ht, ite_true, sampleFuture, PMF.map_bind,
        PMF.map_comp]
      congr 1
      funext j
      have he : J.restrict ∘ (fun ω : ℝ≥0 → ι => Function.update ω t j) =
          (fun x => Function.update x ⟨t, ht⟩ j) ∘ J.restrict := by
        funext ω
        exact Function.update_comp_eq_of_injective ω Subtype.val_injective ⟨t, ht⟩ j
      rw [he, ← PMF.map_comp, ← PMF.map_comp, ih t j htail hhead]
    · simp only [List.filter_cons, decide_eq_false ht, Bool.false_eq_true, ite_false]
      have he (j : ι) :
          J.restrict ∘ (fun ω : ℝ≥0 → ι => Function.update ω t j) = J.restrict := by
        funext ω
        exact Function.update_comp_eq_of_forall_ne ω j fun x hx => ht (hx ▸ x.2)
      simp only [he, ih t _ htail hhead]
      rw [← sampleFuture_skip Q d s t (hstart t (by simp)) i _
        (fun u hu => hhead u (List.mem_filter.mp hu).1), PMF.map_bind]

/-- Sample a finite set of times, starting with the given initial law at time zero. -/
noncomputable def sampledPath (p : PMF ι) (I : Finset ℝ≥0) : PMF (ℝ≥0 → ι) :=
  p.bind fun i => sampleFuture Q d 0 i (I.sort (· ≤ ·))

private theorem sort_filter_subset (I J : Finset ℝ≥0) (hJI : J ⊆ I) :
    (I.sort (· ≤ ·)).filter (fun t => decide (t ∈ J)) = J.sort (· ≤ ·) := by
  apply List.Pairwise.eq_of_mem_iff
    ((I.sortedLT_sort).pairwise.filter _) (J.sortedLT_sort).pairwise
  intro t
  simp only [List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
  exact and_iff_right_of_imp (fun h => hJI h)

/-- The joint distribution at a finite set of times. -/
noncomputable def finiteLaw (p : PMF ι) (I : Finset ℝ≥0) : PMF (I → ι) :=
  (sampledPath Q d p I).map I.restrict

theorem finiteLaw_projective (p : PMF ι) (I J : Finset ℝ≥0) (hJI : J ⊆ I) :
    (finiteLaw Q d p I).map (Finset.restrict₂ (π := fun _ : ℝ≥0 => ι) hJI) = finiteLaw Q d p J := by
  simp only [finiteLaw, sampledPath, PMF.map_comp, Finset.restrict₂_comp_restrict, PMF.map_bind]
  congr 1
  funext i
  rw [sampleFuture_restrict Q d J 0 i _ I.sortedLT_sort.sortedLE (fun _ _ => zero_le),
    sort_filter_subset I J hJI]

variable [MeasurableSpace ι]

theorem finiteLaw_isProjectiveMeasureFamily (p : PMF ι) :
    IsProjectiveMeasureFamily (α := fun _ : ℝ≥0 => ι) (fun I => (finiteLaw Q d p I).toMeasure) := by
  intro I J hJI
  exact (congrArg PMF.toMeasure (finiteLaw_projective Q d p I J hJI)).symm.trans
    (PMF.toMeasure_map _ _ (Finset.measurable_restrict₂ hJI)).symm

end SympyProofs.FiniteMarkovChain
