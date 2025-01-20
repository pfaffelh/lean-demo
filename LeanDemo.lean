import Mathlib

open Nat BigOperators

example (k : ℕ) : k ∣ n ↔ ∃ l : ℕ, n = k * l := by
  rfl

example : 2 ∣ 6 := by
  rw [dvd_def]
  use 3
  rfl

lemma l1 (n : ℕ) : n ∣ n := by
  use 1
  simp

#print l1

example (j k l : ℕ) (hjk : j ∣ k) (hkl : k ∣ l) : j ∣ l := by
  cases' hjk with m hm
  cases' hkl with n hn
  use m*n
  rw [← mul_assoc, ← hm, ← hn]



open Finset Set MeasureTheory Order

example [PartialOrder α] [OrderBot α] (x y : α) (h : Disjoint x y) (he : x ≠ ⊥ ∨ y ≠ ⊥) : x ≠ y := by
  exact (Disjoint.ne_iff h).mpr he

example {α : Type} [CompleteSemilatticeSup α] (K : Set α) (y : α) (hy : y ∈  K) : y ≤ sSup K := by
  apply CompleteSemilatticeSup.le_sSup K y hy



lemma disjoint_of_subset {α : Type*} [CompleteLattice α] (s t : Set α) (J K : Set (Set α)) (hs : ∀ b ∈ J, b ⊆ s) (ht : ∀ b ∈ K, b ⊆ t) (hd : Disjoint s t) (he : ∅ ∉ J ∨ ∅ ∉ K) : Disjoint J K := by
  rw [disjoint_iff_forall_ne]
  intros x hx y hy
  rw [Disjoint.ne_iff]
  aesop
  exact Disjoint.mono (hs x hx) (ht y hy) hd

lemma sSup_disjoint_of_le_of_le {α : Type*} [CompleteLattice α] (s t : α) (J K : Set α) (hs : ∀ b ∈ J, b ≤ s) (ht : ∀ b ∈ K, b ≤ t) (hd : Disjoint s t) (he : ⊥ ∉ J ∨ ⊥ ∉ K) : Disjoint J K := by
  rw [disjoint_iff_forall_ne]
  intros x hx y hy
  rw [Disjoint.ne_iff]
  aesop
  exact Disjoint.mono (hs x hx) (ht y hy) hd

lemma sSup_disjoint {α : Type*} [CompleteLattice α] (a b : Set α) (hd : Disjoint (sSup a) (sSup b)) (he : ⊥ ∉ a ∨ ⊥ ∉ b) : Disjoint a b := sSup_disjoint_of_le_of_le (sSup a) (sSup b) a b (fun _ hc => le_sSup hc) (fun _ hc => le_sSup hc) hd he






#check Finset.prod





variable {α β ι : Type*} [DecidableEq ι] [DecidableEq α] {f : ι → α} {g : α → β}

/-- If the images of `f` only overlap where `g (f i) = 1` , then `g (f j) = 1` whenever `g (f j) = g (f n)` for `n ≠ j`.-/
lemma filter_erase_of_pairwiseOne [CommMonoid β]
    {n : ι} {I : Finset ι} (hn : n ∈ I)
    (hf : (I.toSet).Pairwise fun i j => f i = f j → g (f i) = 1) :
    ∀ j ∈ (filter (fun i => f i = f n) I).erase n, g (f j) = 1 := by
  intro x hx
  simp only [mem_erase, ne_eq, mem_filter] at hx
  exact hf hx.2.1 hn hx.1 hx.2.2

@[to_additive (attr := simp)]
lemma prod_filter_of_pairwiseOne [CommMonoid β]
    {n : ι} {I : Finset ι} (hn : n ∈ I)
    (hf : (I : Set ι).Pairwise fun i j => f i = f j → g (f i) = 1) : ∏ j ∈ filter (fun j => f j = f n) I, g (f j) = g (f n) := by
  rw [← mul_one (g (f n))]
  rw [← (prod_eq_one (filter_erase_of_pairwiseOne hn hf))]
  rw [← (Finset.mul_prod_erase (filter (fun j => f j = f n) I) (fun i => g (f i))
    <| mem_filter.mpr ⟨hn , by rfl⟩)]

/-- If the images of `f`  on `I` only overlap where `g (f i) = 1` , then `f` can move inside the binder
of `∏ i in I, g (f i)`.-/
-- @[to_additive (attr := simp)]
lemma prod_image_of_pairwiseOne [CommMonoid β] {I : Finset ι}
    (hf : (I.toSet).Pairwise fun i j => f i = f j → g (f i) = 1) :
    ∏ s in I.image f, g s = ∏ i in I, g (f i) := by
  rw [prod_image']
  exact fun n hnI => (prod_filter_of_pairwiseOne hnI hf).symm

-- @[to_additive (attr := simp)]
/-- If the images of `f` are disjoint on `I`, then `f` can move inside the binder
of `∏ i in I, g (f i)`.-/
lemma Finset.prod_image_of_disjoint {α β : Type*} [CommMonoid β] [PartialOrder α] [OrderBot α] [DecidableEq α]
    [CommMonoid β] {g : α → β}
    (hg_bot : g ⊥ = 1) {f : ι → α} {I : Finset ι} (hf_disj : (I : Set ι).PairwiseDisjoint f) :
    ∏ s in I.image f, g s = ∏ i in I, g (f i) := by
  refine prod_image_of_pairwiseOne <| hf_disj.imp fun i j (hdisj : Disjoint _ _) hfij => ?_
  rw [← hfij, disjoint_self] at hdisj
  rw [hdisj, hg_bot]
