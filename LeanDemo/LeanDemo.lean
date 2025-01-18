import Mathlib.Tactic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separating

open Nat

example (x : ℕ → ℝ) (y z : ℝ) (hy: Filter.Tendsto (fun n ↦ x n) Filter.atTop (nhds Y))
(hz : Filter.Tendsto (fun n ↦ x n) Filter.atTop  (nhds z)) : y = z := by
  apply?
  sorry

#print And

section divisibility

example (k : ℕ) : k ∣ n ↔ ∃ l : ℕ, n = k * l := by
  rfl

example : 2 ∣ 6 := by
  use 3

lemma l1 (n : ℕ) : n ∣ n := by
  use 1
  simp only [mul_one]

example (j k l : ℕ) (hjk : j ∣ k) (hkl : k ∣ l) : j ∣ l := by
  exact Nat.dvd_trans hjk hkl

end divisibility

section classical

example (p : Prop) : (¬p) ↔ (p → False) := by
  rfl

example (p q r : Prop) (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  apply hqr (hpq hp)

lemma negneg_of_classical (p : Prop) (h : p ∨ ¬ p): (p ↔ ¬¬ p) := by
  constructor
  · intros hp h1
    exact h1 hp
  · sorry
end classical

inductive ~and (a b : Bool) : Bool :=
  | true  => b
  | false => false

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq ⟩

section intermediate_value

#check intermediate_value_univ₂

example (a b : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (hf1 : f a ≤ 0) (hf2 : 0 ≤ f b ) : ∃ x, f x = 0 := by
  sorry
end intermediate_value

example ℕ ⊆ ℤ := by
  sorry
