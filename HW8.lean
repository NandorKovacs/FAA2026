/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/
import Mathlib
import Cslib.Algorithms.Lean.TimeM

open Cslib.Algorithms.Lean

set_option autoImplicit false

/-!
# Homework 8

**Coloring a graph with `Δ(G) + 1` colors in linear time**

A *proper coloring* of a graph gives every vertex a color such that the two endpoints of every
edge get different colors. Every graph with maximum degree `Δ(G)` can be colored with
`Δ(G) + 1` colors, and the *greedy algorithm* finds such a coloring: it goes through the vertices
one after the other and gives each vertex the smallest color that none of its already colored
neighbors has. A vertex has at most `Δ(G)` neighbors, so one of the colors `0, ..., Δ(G)` is
always free. With the right data structures, the greedy algorithm runs in linear time
`O(n + m)`.

## Tasks

* Model the problem: what is a proper coloring, the maximum degree `Δ(G)`, and the size of the
  input?
* Implement the greedy algorithm in `TimeM`. `TimeM` only counts the ticks that you write, so
  choose a cost model that describes what your algorithm would cost on a real computer, and
  explain in a comment for every tick which operations it pays for.
* Test your algorithm on a few graphs.
* (Optional) Prove that your algorithm computes a proper coloring with `Δ(G) + 1` colors.
* (Optional) Prove that your algorithm runs in linear time.

Below is a proposal for how to represent graphs. You may use it, or define your own.
-/

namespace HW8

/-- An undirected graph without self-loops on the vertices `Fin n = {0, ..., n - 1}`,
given by its adjacency lists: `v ∈ G.adj u` means that `u` and `v` are adjacent. -/
structure Graph (n : ℕ) where
  /-- The adjacency list of every vertex. -/
  adj : Fin n → List (Fin n)
  /-- Edges are undirected. -/
  symm : ∀ u v, v ∈ adj u → u ∈ adj v
  /-- There are no self-loops. -/
  loopless : ∀ v, v ∉ adj v

namespace Graph

variable {n : ℕ}

/-- The graph with the edges `E`: every edge `(u, v)` is stored in the adjacency lists of both
`u` and `v`. For a concrete list `E`, Lean checks automatically that it has no self-loops.

For example, `Graph.ofEdges [(0, 1), (1, 2)] : Graph 3` is the path `0 - 1 - 2`. -/
def ofEdges (E : List (Fin n × Fin n)) (hE : ∀ e ∈ E, e.1 ≠ e.2 := by decide) : Graph n where
  adj v := (E.filter (·.1 = v)).map (·.2) ++ (E.filter (·.2 = v)).map (·.1)
  symm u v h := by
    simp at h ⊢
    exact h.symm
  loopless v h := by
    simp at h
    exact hE (v, v) h rfl

/-! ## Example graphs

Test your algorithm on these graphs, and on your own ones.
-/

def optToFin {n : ℕ} (f : Option (Fin n)) : Fin (n + 1) :=
  match f with
  | none => Fin.last n
  | some i => i.castSucc

-- def greedyColor {n : ℕ} (g : Graph n) (coloring : List (Fin (n + 1))) : Fin n → Fin (n + 1) :=
--   fun i => optToFin ((List.finRange (n)).find? (
--     fun k => (g.adj i).filter (
--       fun l =>
--         match coloring.length ≤ k with
--           | true => true
--           | false => coloring.get l ≠ k
--       )))
-- forget to check if already colored, instead checking index as a mistake

def Proper {n} (g : Graph n) (coloring : Fin n → ℕ) := ∀ u v, v ∈ g.adj u → coloring v ≠ coloring u
def Δ (g : Graph n) := (Finset.univ.image (fun k => (g.adj k).length)).max


def used_colors {n} (g : Graph n) (coloring : Array (Option ℕ)) (i : Fin n) : TimeM ℕ (List ℕ) := do
  TimeM.tick (g.adj i).length -- the filter reads coloring (g.adj i).length times

  return (g.adj i).filterMap (
    fun k =>
      coloring[k]?.join
    )

def mark_color (marks : Array Bool) (c : ℕ) : TimeM ℕ (Array Bool) := do
  ✓ -- O(1) function
  return marks.setIfInBounds c true

def select_color (used : List ℕ) : TimeM ℕ ℕ := do
  -- each mark_color is one tick; we count how many times foldl is executed, and mark_color is one comparison -> O(1)
  TimeM.tick (used.length + 1) -- The array.replicate takes this much time
  let marks ←  used.foldlM mark_color (Array.replicate (used.length + 1) false)
  TimeM.tick (used.length + 1) -- this find will look at at most this many different k's; each of them processed in O(1)
  let color := (List.range (used.length + 1)).find? (fun k => !marks.getD k true)

  return color.getD used.length

def color_vertex {n} (g : Graph n) (coloring : Array (Option ℕ)) (i : Fin n) : TimeM ℕ (Array (Option ℕ)) := do
  let used ← used_colors g coloring i
  let color ← select_color used

  ✓ -- we write to the array
  return coloring.set! i.val color

def greedyColor {n} (g : Graph n) : TimeM ℕ (Fin n → ℕ) := do
  TimeM.tick n -- Array.replicate costs this much
  let coloring ← (List.finRange n).foldlM (color_vertex g) (Array.replicate n none)
  return fun i => coloring[i]?.join.getD 0




/-- The graph without vertices. -/
def G1 : Graph 0 := .ofEdges []

/-- The path `0 - 1 - 2 - 3`. -/
def G2 : Graph 4 := .ofEdges [(0, 1), (1, 2), (2, 3)]

/-- The complete graph `K₄`. -/
def G3 : Graph 4 := .ofEdges [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The odd cycle `0 - 1 - 2 - 3 - 4 - 0`, which needs 3 colors. -/
def G4 : Graph 5 := .ofEdges [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

/-- The even cycle `0 - 3 - 4 - 1 - 2 - 5 - 0`. It only needs 2 colors, but in this vertex order
greedy uses all `Δ + 1 = 3` colors. -/
def G5 : Graph 6 := .ofEdges [(0, 3), (3, 4), (4, 1), (1, 2), (2, 5), (5, 0)]

#eval greedyColor G1
#eval greedyColor G2
#eval greedyColor G3
#eval greedyColor G4
#eval greedyColor G5

end Graph

end HW8
