/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Olivier Fischer, Sorrachai Yingchareonthawornchai
-/
import Mathlib.Tactic

/-!
# Homework File for Week 1

There are 5 exercises. Each correctly solved exercise is worth 20 points.
-/

section Logic

variable (P Q R S : Prop)

/--
Exercise 1:

Prove the following proposition in **term**-mode.
-/
theorem Q1 (p : P) (q : Q) (pr : P → R) (qrs : Q ∧ R → S) : S := qrs ⟨q, pr p⟩

/--
Exercise 2:

Prove the following proposition.
You may only use the tactics `constructor`, `intro`, `apply`, and `exact`.
-/
theorem Q2 : (P → Q ∧ R) ↔ ((P → Q) ∧ (P → R)) := by
  constructor
  · intro h
    constructor
    · intro p
      apply h at p
      exact And.left p
    · intro p
      apply h at p
      exact And.right p
  · intro h p
    constructor
    · apply And.left at h
      apply h
      exact p
    · apply And.right at h
      apply h
      exact p

/--
Exercise 3:

Prove the following proposition. You may only use the tactics
`constructor`, `intro`, `apply`, `exact`, `by_contra`, `contradiction`, and `trivial`.
You may also introduce local definitions using `let`.
-/
theorem Q3 : ((P → Q) ∧ (P → ¬ Q)) ↔ ¬ P := by
  constructor
  · intro h p
    apply And.right h
    · exact p
    apply And.left h
    exact p
  intro np
  constructor
  · intro p
    contradiction
  intro p
  contradiction




end Logic

section Divisibility

/-
Consider the following recursive definition of the factorial function:
-/
def fac (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * fac n

/-
In the following exercises, you are *allowed* to use the following theorems:
-/
#check mul_assoc
#check mul_comm
#check dvd_mul_right
#check dvd_trans

/--
Exercise 4:

Show that any positive natural number `n + 1` divides its factorial.
You may only use the tactics `rw`, `rewrite`, `apply`, and `exact`.
-/
theorem Q4 (n : ℕ) : (n + 1) ∣ fac (n + 1) := by
  rw [fac]
  exact dvd_mul_right (n + 1) (fac n)

/--
Exercise 5:

Show that any divisor `k` of `n + 1` divides any `d` equal to `fac (n + 1)`.
You may only use the tactics `rw`, `rewrite`, `apply`, and `exact`.

Hint: you may want to use the theorem `Q4` that you have proven above.
You will still get the points for this exercise if you have not proven `Q4`.
-/
theorem Q5 (n k d : ℕ) (h : k ∣ (n + 1)) (h2 : fac (n + 1) = d) : k ∣ d := by
  rw [<-h2]
  apply dvd_trans h
  apply Q4


end Divisibility
