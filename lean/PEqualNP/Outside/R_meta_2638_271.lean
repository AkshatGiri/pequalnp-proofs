import PEqualNP.Defs

open PEqualNP.MetaComplexity

-- The residual graph has exactly three degree-two vertices. Any route between
-- two of them uses at least five edges. Every other live vertex is cubic.
theorem PEqualNP.Outside.R_meta_2638_271
    (geometry : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n),
      (∀ u ∉ A, (G.neighborSet u).ncard = 3) →
      (∀ u : Fin n, ∀ w : G.Walk u u, w.IsCycle → 7 ≤ w.length) →
      (∀ a b, G.Adj a b → a ∉ A) → v ∉ A →
      let H := G.deleteEdges (G.incidenceSet v)
      let deg u := (H.neighborSet u).ncard
      (∀ u : Fin n, deg u = 0 ↔ u = v ∨ u ∈ A) ∧
      (∀ u : Fin n, deg u = 0 ∨ deg u = 2 ∨ deg u = 3) ∧
      (({u : Fin n | deg u = 2} : Set (Fin n)).ncard = 3) ∧
      (∀ a b : Fin n, a ≠ b → deg a = 2 → deg b = 2 →
        ∀ p : H.Walk a b, 5 ≤ p.length))
    (residual : ∀ (n k s : ℕ) (H : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n)
      (f : (Fin n → Bool) → Bool),
      let deg u := (H.neighborSet u).ncard
      v ∉ A →
      (∀ u : Fin n, deg u = 0 ↔ u = v ∨ u ∈ A) →
      (∀ u : Fin n, deg u = 0 ∨ deg u = 2 ∨ deg u = 3) →
      (({u : Fin n | deg u = 2} : Set (Fin n)).ncard = 3) →
      (∀ a b : Fin n, a ≠ b → deg a = 2 → deg b = 2 →
        ∀ p : H.Walk a b, 5 ≤ p.length) →
      (∀ u : Fin n, ∀ p : H.Walk u u, p.IsCycle → 7 ≤ p.length) →
      (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true) →
      (∀ T : Finset (Fin n), (∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T) → k ≤ T.card) →
      HasCircuitSize n f s → A.card + H.edgeSet.ncard + k ≤ s + 1) :
∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ) := by
  intro n k s G A v f regular girth outside _ notMarked values cover size
  let H := G.deleteEdges (G.incidenceSet v)
  obtain ⟨isolated,degree,three,distant⟩ := geometry n G A v regular girth outside notMarked
  have inherited (u : Fin n) (p : H.Walk u u) (isCycle : p.IsCycle) : 7 ≤ p.length := by
    have inclusion : H ≤ G := G.deleteEdges_le (G.incidenceSet v)
    have long := girth u (p.mapLe inclusion) (isCycle.mapLe inclusion)
    simpa only [SimpleGraph.Walk.length_mapLe] using long
  exact residual n k s H A v f notMarked isolated degree three distant inherited values cover size
