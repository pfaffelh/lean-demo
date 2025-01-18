import Mathlib

open Nat

example (k l : ℕ) : k ∣ n ↔ ∃ l : ℕ, n = k * l := by
  rfl

example (n : ℕ): 2 ∣ 6 := by
  rw [dvd_def]
  use 3
  rfl

lemma l1 (n : ℕ) : n ∣ n := by
  use 1
  simp

#print l1

example (j k l : ℕ) (hjk : j ∣ k) (hkl : k ∣ l) : j ∣ l := by
  exact Nat.dvd_trans hjk hkl

open Function Set

variable {α : Type} [PartialOrder α] [OrderBot α]

example (J : Set α) (s t : α) (hs : ⋃₀ J ⊆ s) (ht : ⋃₀ K ⊆ t) (hd : Disjoint s t) : PairwiseDisjoint J id := by

  exact hd hs ht hst

lemma disjointSets_of_disjoint {α : Type*} [CompleteLattice α] {a b : α} {J K : Set α}
    (ha : ∀ c ∈ J, c ≤ a) (hb : ∀ d ∈ K, d ≤ b) (hJK : ⊥ ∉ J ∨ ⊥ ∉ K) (hcd : Disjoint a b) :
    Disjoint J K := by


  rw [disjoint_of_pairwiseDisjoint]
   PairwiseDisjoint {J, K}

  simp
  rw [Set.disjoint_iff_forall_ne]
  intros x hx y hy hxy
  obtain h1 : Disjoint x y := by
    exact Disjoint.mono (ha x hx) (hb y hy) hcd
  revert h1
  cases' hJK with hJ hK
  · rw [← hxy]
    exact (not_iff_not.mpr disjoint_self).mpr (ne_of_mem_of_not_mem hx hJ)
  · rw [hxy]
    exact (not_iff_not.mpr disjoint_self).mpr (ne_of_mem_of_not_mem hy hK)

lemma disjointSets_of_disjoint' {α : Type*} [PartialOrder α] [OrderBot α] {a b : α} {J K : Set α}
    (ha : ∀ c ∈ J, c ≤ a) (hb : ∀ d ∈ K, d ≤ b) (hJK : ⊥ ∉ J ∨ ⊥ ∉ K) (hcd : Disjoint a b) :
    Disjoint J K := by
  rw [Set.disjoint_iff_forall_ne]
  intros x hx y hy hxy
  obtain h1 : Disjoint x y := by
    exact Disjoint.mono (ha x hx) (hb y hy) hcd
  revert h1
  cases' hJK with hJ hK
  · rw [← hxy]
    exact (not_iff_not.mpr disjoint_self).mpr (ne_of_mem_of_not_mem hx hJ)
  · rw [hxy]
    exact (not_iff_not.mpr disjoint_self).mpr (ne_of_mem_of_not_mem hy hK)
