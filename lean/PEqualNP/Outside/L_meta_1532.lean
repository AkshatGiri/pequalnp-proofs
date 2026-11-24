import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1532 :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n), (∀ e ∈ U, x ∈ e) →
    ∀ (K'' : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K'' →
    ∀ (K : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
    K.card ≤ K''.card + 1
 := by
  intro n G U x hU K' hK' K hK
  have hcover : G.IsVertexCover (↑(insert x K') : Set (Fin n)) := by
    intro a b hab
    by_cases h : s(a, b) ∈ U
    · have hx : x = a ∨ x = b := by simpa using hU (s(a, b)) h
      rcases hx with rfl | rfl
      · exact Or.inl (Finset.mem_insert_self _ _)
      · exact Or.inr (Finset.mem_insert_self _ _)
    · have h' : (G.deleteEdges ↑U).Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨hab, h⟩
      rcases hK'.1 h' with ha | hb
      · exact Or.inl (Finset.mem_insert_of_mem ha)
      · exact Or.inr (Finset.mem_insert_of_mem hb)
  exact (hK.2 _ hcover).trans (Finset.card_insert_le _ _)
