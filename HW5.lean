/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Olivier Fischer, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false

/-!
# Homework File for Week 5

There are 5 exercises. Each correctly solved exercise is worth 20 points.

All tactics **except `grind`** are welcome. However, if you use `grind`
in an exercise, you can still get up to half the points.

We also reserve the right to subtract points for unreadable code.
Please use the code style used in the lecture. If you deviate from it,
please explain why and what the code does in the comments.
-/

@[simp] def Nat.MinOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y
@[simp] def Nat.MaxOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≥ y

namespace HW5

/-!
  **Exercise 1**

  First fill in the definition of the `rename` function, then prove the theorem below.
-/
inductive RegEx (α : Type) where
  | epsilon : RegEx α
  | symbol (a : α) : RegEx α
  | choice (r1 r2 : RegEx α) : RegEx α
  | concat (r1 r2 : RegEx α) : RegEx α
  | star (r : RegEx α) : RegEx α

inductive Matches {α : Type} : RegEx α → List α → Prop where
  -- `epsilon` matches the empty word, i.e. empty list
  | epsilon : Matches .epsilon []
  -- `symbol a` matches the singleton list `[a]`
  | symbol (a : α) : Matches (.symbol a) [a]
  -- If `r1` matches a word `w`, then `choice r1 r2` matches `w`
  | choice_left {r1 r2 : RegEx α} {w : List α} :
      Matches r1 w → Matches (.choice r1 r2) w
  -- If `r2` matches a word `w`, then `choice r1 r2` matches `w`
  | choice_right {r1 r2 : RegEx α} {w : List α} :
      Matches r2 w → Matches (.choice r1 r2) w
  -- If `r1` and `r2` match the words `w1` and `w2`, respectively,
  -- then `concat r1 r2` matches `w1 ++ w2`
  | concat {r1 r2 : RegEx α} {w1 w2 : List α} :
      Matches r1 w1 → Matches r2 w2 → Matches (.concat r1 r2) (w1 ++ w2)
  -- Star base case: `star r` matches the empty word
  | star_nil (r : RegEx α) : Matches (.star r) []
  -- Star recursive case: If `r` matches `w1` and `star r` matches `w2`,
  -- then `star r` matches `w1 ++ w2`
  | star_more {r : RegEx α} {w1 w2 : List α} :
      Matches r w1 → Matches (.star r) w2 → Matches (.star r) (w1 ++ w2)

-- **(a)** Fill in the definition of the rename function, which should
-- replace every `a : α` by `f a : β`.
def rename {α β : Type} (f : α → β) : RegEx α → RegEx β
  | .epsilon => .epsilon
  | .symbol a => .symbol (f a)
  | .choice r1 r2 => .choice (rename f r1) (rename f r2)
  | .concat r1 r2 => .concat (rename f r1) (rename f r2)
  | .star r => .star (rename f r)


-- **(b)** Prove the following theorem.
theorem matches_rename {α β : Type} (f : α → β) {r : RegEx α} {w : List α}
    (h : Matches r w) : Matches (rename f r) (List.map f w) := by
  induction h
  all_goals rewrite [rename];
  case' epsilon => apply Matches.epsilon
  case' symbol => apply Matches.symbol
  case' choice_left => apply Matches.choice_left
  case' choice_right => apply Matches.choice_right
  case' concat => simp; apply Matches.concat
  case' star_nil => apply Matches.star_nil
  case' star_more => simp; apply Matches.star_more
  all_goals assumption


/-!
  **Exercise 2**

  Prove the following theorem by induction over the predicate.

  Hint: the `split` tactic is useful for if-else splits.
-/
inductive BinaryTree where
  | nil
  | node (value : ℕ) (left : BinaryTree) (right : BinaryTree)

def inorder : BinaryTree → List ℕ
  | .nil => []
  | .node value l r => inorder l ++ value :: inorder r

inductive IsBST : BinaryTree → Prop where
  | nil : IsBST .nil
  | node (value : ℕ) (l : BinaryTree) (r : BinaryTree)
      (bst_left : IsBST l) (bst_right : IsBST r)
      (hleft : ∀ x ∈ inorder l, x < value)
      (hright : ∀ x ∈ inorder r, value < x) :
      IsBST (.node value l r)

def lookup (q : ℕ) : BinaryTree → Bool
  | .nil => false
  | .node value l r =>
      if q < value then lookup q l
      else if value < q then lookup q r
      else true

theorem lookup_correct (q : ℕ) {t : BinaryTree} (ht : IsBST t) :
    lookup q t = true ↔ q ∈ inorder t := by
    induction ht with
    | nil =>
      rw [lookup, inorder]
      simp
    | node value l r bst_left bst_right hleft hright bst_left_ih bst_right_ih =>
      constructor <;> intro h
      · unfold lookup at h ; split at h <;> expose_names
        · unfold inorder
          simp
          left
          apply (bst_left_ih.mp h)
        · simp [h_1] at h
          cases h <;> expose_names <;> unfold inorder <;> simp
          · right
            left
            omega
          · right
            right
            apply (bst_right_ih.mp h)
      · unfold inorder at h; simp at h
        unfold lookup; split <;> expose_names
        · obtain hl | hm | hr := h
          · apply (bst_left_ih.mpr hl)
          · simp_all
          · have := hright q hr; omega
        · simp_all
          obtain hl | hm | hr := h
          · have := hleft q hl; omega
          · left; omega
          · right; assumption















/-!
  **Exercise 3**

  Prove the following two helper lemmas about `Sorted`.
-/
inductive Sorted : List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ) (t : List ℕ ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a : ℕ) (t : List ℕ) : a.MinOfList t → Sorted (t) →  Sorted (a :: t)

-- **(a)** Prove the following lemma.
lemma sorted_a_b (a b : ℕ) (l : List ℕ) (h : Sorted (a :: b :: l)) : a ≤ b := by
   cases h with
  | cons => trivial
  | cons_min _ _ hh _ =>
    unfold Nat.MinOfList at hh
    apply hh
    simp


-- **(b)** Prove the following lemma.
lemma sorted_append (x : ℕ) (l1 l2 : List ℕ) (h1 : Sorted l1) (h2 : Sorted l2)
  (h1' : x.MaxOfList l1) (h2' : x.MinOfList l2) : Sorted (l1 ++ x :: l2) := by
  induction h1 with
  | nil =>
    simp
    apply Sorted.cons_min <;> assumption
  | single a =>
    simp
    suffices h : a ≤ x from by
      have hxl : Sorted (x :: l2) := by
        apply Sorted.cons_min <;> assumption
      apply Sorted.cons <;> assumption
    simp at h1'
    assumption
  | cons a b t _ _ _ =>
    have hxbt : x.MaxOfList (b :: t) := by
      unfold Nat.MaxOfList at ⊢ h1'
      simp_all
    expose_names
    have a_ih := a_ih hxbt
    apply Sorted.cons <;> assumption
  | cons_min a t _ _ _ =>
    have hxt : x.MaxOfList (t) := by
      unfold Nat.MaxOfList at ⊢ h1'
      simp_all
    expose_names
    have a_ih := a_ih hxt
    rw [List.cons_append]
    induction t with
    | nil =>
      simp_all
      apply Sorted.cons <;> assumption
    | cons head tail ih =>
      rw [List.cons_append]
      apply Sorted.cons
      · unfold Nat.MinOfList at h
        apply h
        simp
      · rw [<-List.cons_append]
        assumption


theorem isBST_lr {v : ℕ} {l r : BinaryTree} (ht : IsBST (BinaryTree.node v l r)) : IsBST l ∧ IsBST r := by
  sorry

/-!
  **Exercise 4**

  For subtask (a), prove that the in-order traversal list of a BST is sorted.
  For subtask (b), construct a binary tree with sorted in-order traversal list
  that is not a BST (according to our definitions).

  You are allowed to use the lemmas from Exercise 3 even if you have not proven
  them.
-/
-- **(a)** Prove the following theorem.
theorem bst_has_sorted_inorder {t : BinaryTree} (ht : IsBST t) : Sorted (inorder t) := by
  unfold inorder
  split
  · exact Sorted.nil
  have (l : BinaryTree) : Sorted (inorder l) := by sorry
  expose_names
  have ⟨htl, htr⟩ := isBST_lr ht
  · apply sorted_append

    · simp_all
    · simp_all
    · unfold Nat.MaxOfList
      unfold inorder
      split
      · simp
      · intro y
        simp
        intro hy
        obtain hyl | hym | hyr := hy
        · rw [<-lookup_correct] at hyl
          unfold lookup at hyl


    · sorry

-- **(b)** Prove the following theorem.
lemma sorted_may_not_imply_bst : ∃ t : BinaryTree, Sorted (inorder t) ∧ ¬ IsBST t := by
  sorry


/-!
  **Exercise 5**

  Prove the theorems (a), (b), (c), and (d) about heaps.
-/

inductive IsHeap : BinaryTree → Prop where
  | nil : IsHeap .nil
  | node (value : ℕ) (l : BinaryTree) (r : BinaryTree)
      (heap_left : IsHeap l) (heap_right : IsHeap r)
      (hleft : ∀ x ∈ inorder l, x ≤ value)
      (hright : ∀ x ∈ inorder r, x ≤ value) :
      IsHeap (.node value l r)

def heapInsert (x : ℕ) : BinaryTree → BinaryTree
  | .nil => .node x .nil .nil
  | .node value l r =>
      if x ≤ value then .node value (heapInsert x r) l
      else .node x (heapInsert value r) l

def fromList : List ℕ → BinaryTree
  | [] => .nil
  | x :: xs => heapInsert x (fromList xs)

-- **(a)** Prove the following theorem.
lemma mem_heapInsert (y : ℕ) (t : BinaryTree) :
    ∀ x : ℕ, y ∈ inorder (heapInsert x t) ↔ y = x ∨ y ∈ inorder t := by
  sorry

-- **(b)** Prove the following theorem.
theorem heapInsert_isHeap {t : BinaryTree} (ht : IsHeap t) :
    ∀ x : ℕ, IsHeap (heapInsert x t) := by
  sorry

-- **(c)** Prove the following theorem.
theorem fromList_isHeap (xs : List ℕ) : IsHeap (fromList xs) := by
  sorry

-- **(d)** Prove the following theorem.
theorem mem_fromList (y : ℕ) (xs : List ℕ) : y ∈ inorder (fromList xs) ↔ y ∈ xs := by
  sorry

end HW5
