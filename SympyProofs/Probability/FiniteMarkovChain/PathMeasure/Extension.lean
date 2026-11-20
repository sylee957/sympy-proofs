module

public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

import Mathlib.Topology.Compactness.Compact

/-!
# Extension of finite-state distributions

Consistent finite-dimensional distributions on a finite state space extend to
an arbitrary index set. Finite discrete spaces are compact, so a decreasing
sequence of cylinder sets with empty intersection is eventually empty. This
supplies the continuity needed by the Carathéodory measure construction.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory Set Filter
open scoped Topology

variable {T ι : Type*} [Finite ι] [MeasurableSpace ι]
  {P : ∀ I : Finset T, Measure (I → ι)}
  [∀ I, IsFiniteMeasure (P I)]

private theorem finiteCylinder_eventually_empty (s : ℕ → Set (T → ι))
    (hs : ∀ n, s n ∈ measurableCylinders (fun _ : T => ι))
    (ha : Antitone s) (he : (⋂ n, s n) = ∅) : ∃ n, s n = ∅ := by
  classical
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  have hc (n : ℕ) : IsClosed (s n) := by
    obtain ⟨I, S, _, hS⟩ := (mem_measurableCylinders _).mp (hs n)
    rw [hS]
    exact (Set.toFinite S).isClosed.preimage (Finset.continuous_restrict I)
  by_contra! hn
  have hnon := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s
    (fun n => ha (Nat.le_succ n)) hn
    (hc 0).isCompact hc
  simp [he] at hnon

/-- Finite state spaces make a consistent cylinder content countably additive. -/
theorem finiteProjective_isSigmaSubadditive
    (hP : IsProjectiveMeasureFamily (α := fun _ : T => ι) P) :
    (projectiveFamilyContent hP).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hfUnion hfdisj => ?_)
  refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (projectiveFamilyContent hP) (fun _ _ => projectiveFamilyContent_ne_top hP) ?_
    hf hfUnion hfdisj
  intro s hs ha he
  obtain ⟨n, hn⟩ := finiteCylinder_eventually_empty s hs ha he
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with k hk
  have hempty : s k = ∅ := Set.eq_empty_iff_forall_notMem.mpr (by
    intro x hx
    simpa [hn] using ha hk hx)
  simp [hempty]

/-- Extend a consistent family of finite measures to the full product space. -/
noncomputable def finiteProjectiveLimit
    (hP : IsProjectiveMeasureFamily (α := fun _ : T => ι) P) : Measure (T → ι) :=
  (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge (finiteProjective_isSigmaSubadditive hP)

theorem finiteProjectiveLimit_isProjectiveLimit
    (hP : IsProjectiveMeasureFamily (α := fun _ : T => ι) P) :
    IsProjectiveLimit (finiteProjectiveLimit hP) P := by
  intro I
  ext S hS
  rw [Measure.map_apply (Finset.measurable_restrict I) hS,
    finiteProjectiveLimit, AddContent.measure_eq]
  · exact projectiveFamilyContent_cylinder hP hS
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hS

end SympyProofs.FiniteMarkovChain
