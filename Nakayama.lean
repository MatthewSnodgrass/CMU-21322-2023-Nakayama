-- This module serves as the root of the `Nakayama` library.
-- Import modules here that should be built as part of the library.
import «Nakayama».Basic

import Mathlib.Tactic
import Mathlib.RingTheory.Finiteness
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Group.Defs

def invertible [CommRing A] (x : A) : Prop := ∃ u : A, u * x = 1

lemma Easy [CommRing A] [AddCommGroup M] [Module A M] (a : A) (ha : invertible a) (x : M) (hax : a • x = 0) : x = 0 := by
  rcases ha with ⟨b, hb⟩
  calc x = (1 : A) • x := by exact (one_smul A x).symm
  _ = (b * a) • x := by rw[hb]
  _ = b • (a • x) := mul_smul b a x
  _ = b • (0 : M) := by rw[hax]
  _ = 0 := smul_zero b

lemma Lemma1 [CommRing A] (x : A) (m : Ideal A) (hm : Ideal.IsMaximal m) :
  x ∈ m → ¬(1 - x ∈ m) := by
  intro h h'
  have fact : m = ⊤ := by
    rw[Ideal.eq_top_iff_one m]
    have comp : 1 = x + (1 - x) := by exact eq_add_of_sub_eq' rfl
    rw[comp]
    exact Ideal.add_mem m h h'
  have fact2 : m ≠ ⊤ := Ideal.IsPrime.ne_top'
  exact fact2 fact

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
    rw[← hu]
    exact mul_comm u x

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

lemma JacobsonIsIntersection [CommRing A] (x : A) : (∀ y : A, ∃ u : A, u * (1 - x * y) = 1) ↔
  x ∈ (Ideal.jacobson 0) := by
  constructor
  · intro hx
    unfold Ideal.jacobson
    simp
    intro m hm
    by_contra h
    have fact : ∃ a : A, ∃ b : m, a * x + b = 1 := by
      have fact2 : 1 ∈ (Ideal.span {x}) + m := by
        rw[← Ideal.eq_top_iff_one ((Ideal.span {x}) + m)]
        sorry
      apply?
    sorry
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
    have inv : invertible (1 - x * y) := by
      rw[← AvoidMaxInv]
      exact key
    exact hx' inv

open Set

theorem CayleyHamilton [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
  (I : Ideal A) (f : Module.End A M) (hfI : LinearMap.range f ≤ I • ⊤) :
  ∃ p : Polynomial A, Polynomial.Monic p ∧ (∀ k : ℕ,
  Polynomial.coeff p k ∈ I ^ ((Polynomial.natDegree p) - k)) ∧ ((Polynomial.aeval f) p = 0) := by
  rcases (Module.Finite.exists_fin : ∃ (n : ℕ) (s : Fin n → M), Submodule.span A (range s) = ⊤) with ⟨n, s, hs⟩
  sorry

open Polynomial

theorem Nakayama [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
  (I : Ideal A) (hIM : (⊤ : Submodule A M) = (I • ⊤)) : ∃ a ∈ I, ∀ x : M, a • x = x := by
  have fact : ∃ p : A[X], Polynomial.Monic p ∧ (∀ k : ℕ, Polynomial.coeff p k ∈ I ^ ((Polynomial.natDegree p) - k)) ∧
  ((Polynomial.aeval (1 : Module.End A M)) p = 0) := by
    apply CayleyHamilton
    exact LinearMap.range_le_iff_comap.mpr (id hIM.symm)
  rcases fact with ⟨p, hp⟩
  use (1 - (Polynomial.eval 1 p))
  constructor
  · rw[eval_eq_sum_range]
    have manip : Finset.sum (Finset.range (natDegree p + 1)) fun i => coeff p i * 1 ^ i = 1 + Finset.sum (Finset.range (natDegree p)) fun i => coeff p i * 1 ^ i
    sorry
  · intro x
    have fact₁ : Polynomial.aeval (1 : Module.End A M) p = (Polynomial.eval 1 p) • (1 : Module.End A M) := by
      have := aeval_algebraMap_apply_eq_algebraMap_eval (A := Module.End A M) (1 : A) p
      simp at this
      exact this
    have fact : (1 - (Polynomial.eval 1 p)) • x = (1 - (Polynomial.aeval (1 : Module.End A M) p)) • x := by
      rw [fact₁]
      simp [sub_smul]
    rw[fact]
    simp
    rw[hp.right.right]
    exact rfl

theorem Nakayama2 [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] (I : Ideal A)
  (hI : I ≤ Ideal.jacobson 0) (hIM : (⊤ : Submodule A M) = (I • ⊤)) : ∀ x : M, x = 0 := by
  have fact := Nakayama I hIM
  rcases fact with ⟨a, ha⟩
  have fact₁ : a ∈ Ideal.jacobson 0 := by
    apply hI
    exact ha.left
  rw[← JacobsonIsIntersection a] at fact₁
  specialize fact₁ 1
  simp at fact₁
  intro x
  have ax : (1 - a) • x = 0 := by
    calc (1 - a) • x = (1 : A) • x - a • x := by exact sub_smul 1 a x
    _ = x - a • x := by simp
    _ = 0 := by simp[ha.right x]
  exact Easy (1 - a) fact₁ x ax
