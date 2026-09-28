/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Olivier Fischer, Sorrachai Yingchareonthawornchai
-/
import Mathlib.Tactic

/-!
# Exercise File for Week 2
-- Additional instruction: for every problem, you must supply an informal proof before a Lean proof.
-/

/-
  Recall that sets are defined through membership predicates in Lean
-/
def Set' (α : Type) := α → Prop

namespace Set

variable {α : Type} (A B C : Set α)

/-
# Information
You are allowed to use the following tactics:
  `intro`, `ext`, `exact`, `apply`, `cases`, `obtain`, `left`, `right`, `expose_names`,
  `constructor`, `rewrite`, `rw`, `have`, `rfl`, `assumption`, `contradiction`,
  `by_contra`, `by_cases`, `unfold`, and `use`.
You are also allowed to use local definitions using `let`.
-/

/-
## Hints on using obtain
You can use `obtain` for destructuring conjunctions and existential propositions.
-- For `h : P ∧ Q`, you can write `obtain ⟨hp, hq⟩` to obtain `hp : P` and `hq : Q`
-- For `h : ∃ k : ℕ, P k`, you can write `obtain ⟨k, hk⟩` to obtain `k : ℕ` and `hk : P k`
-/
example (P Q : Prop) (h : P ∧ Q) : P := by
  obtain ⟨hp, hq⟩ := h -- hp : P, hq : Q
  exact hp

example (h : ∃ k : ℕ, k + 1 = 42) : ∃ k : ℕ, k + 1 = 43 := by
  obtain ⟨k, hk⟩ := h -- k : ℕ, hk : k+1 = 42
  use k+1
  rw [hk]

/-
## Hints on using cases
`cases h` eliminates the original hypothesis `h : P ∨ Q` and replaces it in each branch
with a proof of `P` or `Q`. These new proofs may initially have inaccessible names;
`expose_names` makes them usable, you can check the name in the InfoView (often is `h`).
Pattern matching lets you choose clear names such as `hP` and `hQ`.
-/
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  · right
    assumption
  · left
    assumption

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h <;> expose_names
  · right
    exact h
  · left
    exact h

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP =>
    right
    exact hP
  | inr hQ =>
    left
    exact hQ


/-
  Exercise 1:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.
-/

/-
  For any x, we show x ∈ A ∩ B ∪ C ↔ x ∈ (A ∪ C) ∩ (B ∪ C)
    First, we show ->
      Assume x is in A ⋂ B. Then, x ∈ A and x ∈ B, and trivialy x ∈ (A ∪ C) ∩ (B ∪ C)
      By contradiction, assume x ∉ A ⋂ B. Then, x ∈ C follows, and trivially x ∈ (A ∪ C) ∩ (B ∪ C)

    Now we show <-
      Assume x ∈ C. Then we trivially see that x ∈ A ∩ B ∪ C holds

      Otherwise, notice that x ∈ (A ∪ C) ∩ (B ∪ C) implies that x ∈ (A ∪ C) as well as x ∈ (B ∪ C).
      As x ∉ C, we get x ∈ A and x ∈ B; Therefore x ∈ A ⋃ B, and x ∈ A ∩ B ∪ C

-/
theorem Q1 : (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) := by
  ext x
  constructor
  · intro h
    cases h <;> expose_names
    · obtain ⟨ha, hb⟩ := h
      constructor <;> left <;> assumption
    · constructor <;> right <;> assumption
  · intro h
    obtain ⟨ha, hb⟩ := h
    by_cases hc : x ∈ C
    · right
      assumption
    left
    constructor
    cases ha
    · assumption
    · contradiction
    cases hb
    · assumption
    contradiction









/-
  We define the operation of the symmetric difference on sets.
-/
def symm_diff (A B : Set α) : Set α :=
  (A \ B) ∪ (B \ A)

notation A " ∆ " B => Set.symm_diff A B

#check symm_diff

/-
  Exercise 2:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.
-/

/-
  We notice that (x ∈ A ∩ B ∆ C) implies
    x ∈ A, and x ∈ B \ C ∪ C \ B

  Furthermore, x ∈ A ⋃ B → x ∈ A ∨ x ∈ B, for all A and B

  therefore, we get:
  x ∈ B \ C ∨ x ∈ C \ B, and we want to show x ∈ (A ∩ B) \ (A ∩ C) ∨ x ∈ (A ∩ C) \ (A ∩ B)

  We show following lemma:
  Let x ∈ A, x ∈ B \ C. Then, x ∈ (A ∩ B) \ (A ∩ C)
    x ∈ (A ∩ B) \ (A ∩ C) ↔ x ∈ A ∩ (B \ (A ∩ C))
    As x ∈ A, we only have to show x ∈ (B \ (A ∩ C)), but
    x ∈ (B \ (A ∩ C)) ↔ x ∈ (B \ A) ⋃ (B \ C)
    however, by assumption, x ∈ B \ C, and therefore x is also in the union

  Now, suppose X ∈ B \ C. Then, with this lemma, we get x ∈ (A ∩ B) \ (A ∩ C), and we are done
  Otherwise, suppose x ∈ C \ B, which implies x ∈ (A ∩ C) \ (A ∩ B), and we are done.

-/
theorem Q2 (x : α) : x ∈ A ∩ (B ∆ C) → x ∈ (A ∩ B) ∆ (A ∩ C) := by
  unfold symm_diff
  intro h
  obtain ⟨xa, xsym⟩ := h
  rw [mem_union]
  rw [mem_union] at xsym
  let ll (X Y Z : Set α) : x ∈ X → x ∈ Y \ Z → x ∈ (X ∩ Y) \ (X ∩ Z)
  · intro xx xyz
    rw [inter_sdiff_assoc]
    constructor
    assumption
    rw [sdiff_inter]
    right
    assumption
  cases xsym <;> expose_names
  · left
    apply ll
    assumption
    assumption
  right
  apply ll
  assumption
  assumption









/-
  Exercise 3:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.

  Hint: the following theorems may be helpful.
-/
#check Set.mem_union
#check Set.mem_inter
#check Set.mem_sdiff
#check Set.mem_compl_iff
#check Set.notMem_compl_iff
#check Iff.mp
#check Iff.mpr

/-
  We show the following lemma:
    x ∈ (X ∆ Y) → x ∈ Xᶜ ∆ Yᶜ which is the same as x ∈ X \ Y ∪ Y \ X → Xᶜ \ Yᶜ ∪ Yᶜ \ Xᶜ
    We use the following identities:
      x ∈ A ⋃ B ↔ x ∈ A ∨ X ∈ B
      x ∈ A \ B ↔ x ∈ A ∧ x ∉ B

    By first using 1, then twice 2, on both sides of the implication, we get

    x ∈ X ∧ x ∉ Y ∨ x ∈ Y ∧ x ∉ X → x ∈ Xᶜ ∧ x ∉ Yᶜ ∨ x ∈ Yᶜ ∧ x ∉ Xᶜ

    By switching x ∉ A for x ∈ Aᶜ , and vice versa, we get

    x ∈ X ∧ x ∉ Y ∨ x ∈ Y ∧ x ∉ X → x ∉ X ∧ x ∈ Y ∨ x ∉ Y ∧ x ∈ X

    which is obviously true, which we see by reordering the terms

  Proving (A ∆ B) = Aᶜ ∆ Bᶜ is the same as proving
  x ∈ (A ∆ B) ↔ x ∈ Aᶜ ∆ Bᶜ

  We show it for both sides:
    x ∈ (A ∆ B) ∈ x ∈ Aᶜ ∆ Bᶜ is precisely what our helper lemma states

    x ∈ (Aᶜ ∆ Bᶜ) → x ∈ A ∆ B is the same as
    x ∈ (Aᶜ ∆ Bᶜ) → x ∈ Aᶜᶜ ∆ Bᶜᶜ, to which our lemma is applicable
-/

theorem Q3 : (A ∆ B) = Aᶜ ∆ Bᶜ := by
  let elem_impl_one_side (X Y : Set α) (x : α) : x ∈ (X ∆ Y) → x ∈ Xᶜ ∆ Yᶜ
  · intro h
    unfold symm_diff at ⊢ h
    rw [mem_union, mem_sdiff, mem_sdiff] at ⊢ h
    rewrite [notMem_compl_iff]
    rewrite [notMem_compl_iff]
    rewrite [mem_compl_iff]
    rewrite [mem_compl_iff]
    cases h <;> expose_names <;> obtain ⟨hl, hr⟩ := h
    · right
      constructor
      assumption
      assumption
    · left
      constructor
      assumption
      assumption
  ext
  expose_names
  constructor
  · apply elem_impl_one_side
  · rewrite (occs := .pos [2]) [<-compl_compl A]
    rewrite (occs := .pos [2]) [<-compl_compl B]
    apply elem_impl_one_side


/-!
  Exercise 4:

  Prove the following theorems.
  You may only use the tactics stated at the start of the sheet.
  You can use Q4a and Q4b for Q4c, even if you have not proven them.
-/

-- The following theorems may be helpful
#check empty_sdiff
#check empty_inter
#check empty_union

#check sdiff_empty
#check inter_empty
#check union_empty

#check sdiff_self
#check inter_self
#check union_self

-- You can use also the following theorem
theorem symm_diff_assoc : ((A ∆ B) ∆ C) = (A ∆ (B ∆ C)) := by
  unfold symm_diff
  grind -- `grind` is a powerful tactic, but you are not allowed to use it yet

/-
  By simplifying with ∅ \ A = ∅, A \ ∅ = A, and ∅ ⋃ A = A, we easily conclude this result

  (∅ ∆ A) = A
  ∅ \ A ∪ A \ ∅ = A
  ∅ ∪ A \ ∅ = A
  ∅ ∪ A = A
  A = A
-/

theorem Q4a : (∅ ∆ A) = A := by
  unfold symm_diff
  rw [sdiff_empty, empty_sdiff, empty_union]

/-
  By simplifying with A \ A = ∅, and ∅ ⋃ ∅ = ∅, we get

  (A ∆ A) = ∅
  A \ A ∪ A \ A = ∅
  ∅ ∪ A \ A = ∅
  ∅ ∪ ∅ = ∅
  ∅ = ∅
-/
theorem Q4b : (A ∆ A) = ∅ := by
  unfold symm_diff
  rw [sdiff_self, empty_union]

/-
  We suspet that C should be A ∆ B.

  We prove this:
  (A ∆ (A ∆ B)) = ((A ∆ A) ∆ B) = (∅ ∆ B) = B, where we use symm_diff_assoc, Q4b and Q4a

-/

theorem Q4c : ∀ A : Set ℕ, ∀ B : Set ℕ, ∃ C : Set ℕ, (A ∆ C) = B := by
  intro A B
  use (A ∆ B)
  rw [<-symm_diff_assoc, Q4b, Q4a]


end Set

namespace Asymptotics

/-
  Consider the following definition of big-O-notation.
-/
def inBigO (f g : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, f n ≤ c * g n

def BigO (g : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {f : ℕ → ℕ | inBigO f g}

notation "O(" g ")" => BigO g

#check inBigO
#check BigO

/-
  Hint: The following theorems may be helpful.
-/
#check Set.mem_ofPred_eq
#check zero_lt_one
#check one_mul

/-
  Exercise 5:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.
-/

/-
  We set c = 1, and n₀ = 0.

  All assumptions are trivially satisfied.
-/
theorem Q5 (g : ℕ → ℕ) : g ∈ O(g) := by
  unfold BigO
  unfold inBigO
  rw [Set.mem_ofPred_eq]
  use 1
  constructor
  · exact zero_lt_one
  use 0
  intro n h
  rw [one_mul]

end Asymptotics
