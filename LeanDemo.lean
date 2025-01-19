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

open Finset Set MeasureTheory Order

example [PartialOrder α] [OrderBot α] (x y : α) (h : Disjoint x y) (he : x ≠ ⊥ ∨ y ≠ ⊥) : x ≠ y := by
  exact (Disjoint.ne_iff h).mpr he

example {α : Type} [CompleteSemilatticeSup α] (K : Set α) (y : α) (hy : y ∈  K) : y ≤ sSup K := by
  apply CompleteSemilatticeSup.le_sSup K y hy



lemma sSup_disjoint_of_le_of_le {α : Type*} [CompleteLattice α] (s t : α) (J K : Set α) (hs : ∀ b ∈ J, b ≤ s) (ht : ∀ b ∈ K, b ≤ t) (hd : Disjoint s t) (he : ⊥ ∉ J ∨ ⊥ ∉ K) : Disjoint J K := by
  rw [disjoint_iff_forall_ne]
  intros x hx y hy
  rw [Disjoint.ne_iff]
  aesop
  exact Disjoint.mono (hs x hx) (ht y hy) hd

lemma sSup_disjoint {α : Type*} [CompleteLattice α] (a b : Set α) (hd : Disjoint (sSup a) (sSup b)) (he : ⊥ ∉ a ∨ ⊥ ∉ b) : Disjoint a b := sSup_disjoint_of_le_of_le (sSup a) (sSup b) a b (fun _ hc => le_sSup hc) (fun _ hc => le_sSup hc) hd he




example {α : Type*} (s t : Set α) (J K : Set (Set α)) (hs : ∀ b ∈ J, b ⊆ s) (ht : ∀ b ∈ K, b ⊆ t) (hd : Disjoint s t) (he : ∅ ∉ J ∨ ∅ ∉ K) : Disjoint J K := sSup_disjoint_of_le_of_le s t J K hs ht hd he


theorem disjoint_sSup_left{α : Type u_1} [CompleteLattice α] {a : Set α} {b : α} (d : Disjoint (sSup a) b) {i : α} (hi : i ∈ a) :
Disjoint i b


lemma disjointSets_of_disjoint {α : Type*} [CompleteLattice α] {a b : α} {J K : Set α}
    (ha : ∀ c ∈ J, c ≤ a) (hb : ∀ d ∈ K, d ≤ b) (hJK : ⊥ ∉ J ∨ ⊥ ∉ K) (hcd : Disjoint a b) :
    Disjoint J K := by
  exact disjointSets_of_disjoint' a b J K ha hb hcd hJK


lemma disjointSets_of_disjoint'' {α : Type*} [PartialOrder α] [OrderBot α] {a b : α} {J K : Set α}
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
