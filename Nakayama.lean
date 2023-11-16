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
    have fact := Ideal.IsMaximal.exists_inv hm h
    rcases fact with ⟨y, i, hiy⟩
    have fact₁ : 1 - x * y ∈ m := by
      calc 1 - x * y = i := by {
        rw[← hiy.right]
        ring
      }
      _ ∈ m := hiy.left
    specialize hx y
    rcases hx with ⟨u, hu⟩
    have fact₂ : u * (1 - x * y) ∈ m := by
      exact Ideal.mul_mem_left m u fact₁
    rw[hu] at fact₂
    exact Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one m).mpr fact₂)
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

open Set Polynomial BigOperators Finset

theorem CayleyHamilton [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
  (I : Ideal A) (f : Module.End A M) (hfI : LinearMap.range f ≤ I • ⊤) :
  ∃ p : Polynomial A, Monic p ∧ (∀ k : ℕ,
  coeff p k ∈ I ^ ((natDegree p) - k)) ∧ ((aeval f) p = 0) := by
  apply LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul
  exact hfI

theorem Nakayama [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
  (I : Ideal A) (hIM : (⊤ : Submodule A M) = (I • ⊤)) : ∃ a ∈ I, ∀ x : M, a • x = x := by
  have fact : ∃ p : A[X], Monic p ∧ (∀ k : ℕ, coeff p k ∈ I ^ ((natDegree p) - k)) ∧
  ((aeval (1 : Module.End A M)) p = 0) := by
    apply CayleyHamilton
    exact LinearMap.range_le_iff_comap.mpr (id hIM.symm)
  rcases fact with ⟨p, p_monic, p_coeff, p_one⟩
  use (1 - (eval 1 p))
  constructor
  · rw [eval_eq_sum_range, sum_range_succ]
    simp [p_monic]
    apply Ideal.sum_mem
    intro c hc
    have easy : c < natDegree p := by exact List.mem_range.mp hc
    have key : I ^ (natDegree p - c) ≤ I := by
      refine Ideal.pow_le_self ?hn
      exact Nat.sub_ne_zero_of_lt easy
    apply key
    exact p_coeff c
  · intro x
    have fact₁ : aeval (1 : Module.End A M) p = (eval 1 p) • (1 : Module.End A M) := by
      have := aeval_algebraMap_apply_eq_algebraMap_eval (A := Module.End A M) (1 : A) p
      simp at this
      exact this
    have fact : (1 - (eval 1 p)) • x = (1 - (aeval (1 : Module.End A M) p)) • x := by
      rw [fact₁]
      simp [sub_smul]
    rw[fact]
    simp only [LinearMap.smul_def, LinearMap.sub_apply, LinearMap.one_apply, sub_eq_self]
    rw[p_one]
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
    _ = x - a • x := by simp only [one_smul]
    _ = 0 := by simp[ha.right x]
  exact Easy (1 - a) fact₁ x ax
