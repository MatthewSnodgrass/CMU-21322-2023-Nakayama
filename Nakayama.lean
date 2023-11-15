-- This module serves as the root of the `Nakayama` library.
-- Import modules here that should be built as part of the library.
import «Nakayama».Basic

import Mathlib.Tactic
import Mathlib.RingTheory.Finiteness
import Mathlib.RingTheory.Ideal.Operations

def invertible [CommRing A] (x : A) : Prop := ∃ u : A, u * x = 1

lemma GenRingInv [CommRing A] (x : A) : Ideal.span {x} = ⊤ ↔ (invertible x) := by
  constructor
  · intro hx
    rw[Ideal.eq_top_iff_one (Ideal.span {x})] at hx
    unfold invertible
    exact Ideal.mem_span_singleton'.mp hx
  · intro hx
    rw[Ideal.eq_top_iff_one (Ideal.span {x})]
    rcases hx with ⟨u, hu⟩
    refine Ideal.mem_span_singleton.mpr ?mpr.intro.a
    use u

lemma AvoidMaxInv [CommRing A] (x : A) : (∀ (I : Ideal A), ((Ideal.IsMaximal I) →
  ¬(x ∈ I))) ↔ (invertible x) := by
  constructor
  · intro hx
    rw[← GenRingInv]
    apply by_contradiction
    intro hx'
    rcases Ideal.exists_le_maximal (Ideal.span {x}) hx' with ⟨m, hm⟩
    have hasx : x ∈ m := by
      apply hm.right
      exact Ideal.mem_span_singleton_self x
    exact hx m hm.left hasx
  · intro hx m hm hxm
    rcases hx with ⟨u, hu⟩
    have bad : 1 ∈ m := by
      rw[← hu]
      exact Ideal.mul_mem_left m u hxm
    have ohno : m = ⊤ := by
      rw[Ideal.eq_top_iff_one m]
      exact bad
    have ohno2 : m ≠ ⊤ := by
      exact Ideal.IsPrime.ne_top'
    exact ohno2 ohno

lemma JacobsonIsIntersection [CommRing A] (x : A) :
        (∀ y : A, ∃ u : A, u * (1 - x * y) = 1) ↔
        x ∈ (Ideal.jacobson 0) := by
  constructor
  · intro hx
    unfold Ideal.jacobson
    simp
    intro m hm
    apply by_contradiction
    intro hx2
  · intro hx
    unfold Ideal.jacobson at hx
    simp at hx
    intro y
    have key : ∀ (m : Submodule A A), Ideal.IsMaximal m → ¬ (1 - x * y ∈ m) := by
      intro m' hm' hxy
      have h : x * y ∈ m' := by
        exact Ideal.mul_mem_right y m' (hx m' hm')
      have h' : 1 ∈ m' := by
        exact (Submodule.sub_mem_iff_left m' h).mp hxy
      have ohno : m' = ⊤ := by
        exact (Ideal.eq_top_iff_one m').mpr h'
      have ohno2 : ¬ (m' = ⊤) := by
        exact Ideal.IsPrime.ne_top'
      exact ohno2 ohno
    apply by_contradiction
    intro hx'
    push_neg at hx'
    have proper : Ideal.span {1 - x * y} ≠ ⊤ := by
      rw[Ideal.ne_top_iff_one (Ideal.span {1 - x * y})]
      intro h
      have xUnit : ∃ u : A, u * (1 - x * y) = 1 := by
        exact Ideal.mem_span_singleton'.mp h
      rcases xUnit with ⟨u, hu⟩
      exact hx' u hu


lemma DetMod1 [CommRing A] : true := by
  sorry

theorem CayleyHamilton [CommRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M] (I : Ideal A)
  (f : Module.End A M) (hfI : LinearMap.range f ≤ I • ⊤) :
  ∃ p : Polynomial A, Polynomial.Monic p ∧ ∀ k : ℕ,
  Polynomial.coeff p k ∈ I ^ ((Polynomial.natDegree p) - k) ∧
  (↑(Polynomial.aeval f) p = 0) := by
  sorry


theorem Nakayama [CommRing A]
  [AddCommGroup M] [Module A M] {I : Ideal A} (hIM : M = I • M) :
  ∃ a ∈ I, ∀ x : M, a • x = x := by
  sorry

theorem Nakayama2 [CommRing A]

#check Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
