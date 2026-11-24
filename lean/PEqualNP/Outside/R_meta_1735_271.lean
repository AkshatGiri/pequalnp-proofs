import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1735_271
    (frontier : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → ∀ (w : ℕ) (v : Fin n),
      4 ≤ (orIn n C w).card → v ∈ orIn n C w →
      ∃ (h : Fin C.gates.length) (b : Fin 2),
        orIn n C (n + h) ⊆ orIn n C w ∧ 4 ≤ (orIn n C (n + h)).card ∧
        v ∈ orIn n C (opnd C h b) ∧ (orIn n C (opnd C h b)).card ≤ 3)
    (remaining : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ (C : Circuit) (E : Finset (Sym2 (Fin n))), IsLeastAO G C → TopForm G C →
        E ⊆ Ustar G C →
        (∀ e ∈ E, ¬ ∃ (u v : Fin n) (j : Fin C.gates.length),
          e = s(u,v) ∧ u ∈ orIn n C (opnd C j 0) ∧ v ∈ orIn n C (opnd C j 1) ∧
          ((orIn n C (opnd C j 0)).filter (fun t => ¬ G.Adj v t)).card ≤ 1 ∧
          ((orIn n C (opnd C j 1)).filter (fun t => ¬ G.Adj u t)).card ≤ 1) →
        E.card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k, bound⟩ := remaining
  refine ⟨15 + k, ?_⟩
  intro n G _ girth edge C least top
  classical
  have noFour : NoFourCycle G := by
    intro a b hab
    by_contra! many
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp many
    obtain ⟨_, hax, hbx⟩ := Finset.mem_filter.mp hx
    obtain ⟨_, hay, hby⟩ := Finset.mem_filter.mp hy
    have ax := G.ne_of_adj hax
    have xb := G.ne_of_adj hbx.symm
    have by' := G.ne_of_adj hby
    have ya := G.ne_of_adj hay.symm
    have cycle : (SimpleGraph.Walk.cons hax (SimpleGraph.Walk.cons hbx.symm
        (SimpleGraph.Walk.cons hby (SimpleGraph.Walk.cons hay.symm SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      constructor
      · simp [SimpleGraph.Walk.cons_isPath_iff, xb, by', ya, hxy, Ne.symm ax, Ne.symm hab]
      · simp [ax, xb, hab, hxy, Ne.symm ax, Ne.symm ya]
    have impossible := girth a _ cycle
    simp at impossible
  let missed (W : Finset (Fin n)) (u : Fin n) : Finset (Fin n) :=
    W.filter (fun t => ¬ G.Adj u t)
  have unique (W : Finset (Fin n)) (large : 4 ≤ W.card) (u v : Fin n)
      (hu : (missed W u).card ≤ 1) (hv : (missed W v).card ≤ 1) : u = v := by
    by_contra unequal
    let common := Finset.univ.filter (fun t : Fin n => G.Adj u t ∧ G.Adj v t)
    have hc : common.card ≤ 1 := noFour u v unequal
    have cover : W ⊆ missed W u ∪ missed W v ∪ common := by
      intro t ht
      by_cases a : G.Adj u t
      · by_cases b : G.Adj v t
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, b⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, b⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, a⟩))
    have c1 := Finset.card_le_card cover
    have c2 := Finset.card_union_le (missed W u ∪ missed W v) common
    have c3 := Finset.card_union_le (missed W u) (missed W v)
    omega
  let U := Ustar G C
  let good (e : Sym2 (Fin n)) := ∃ (u v : Fin n) (j : Fin C.gates.length),
    e = s(u,v) ∧ u ∈ side C j 0 ∧ v ∈ side C j 1 ∧
    (missed (side C j 0) v).card ≤ 1 ∧ (missed (side C j 1) u).card ≤ 1
  let small (j : Fin C.gates.length) : Finset (Sym2 (Fin n)) :=
    if (side (n := n) C j 0).card ≤ 3 ∧ (side (n := n) C j 1).card ≤ 3 then
      (side C j 0 ×ˢ side C j 1).image (fun p => s(p.1,p.2))
    else ∅
  let wide (p : Fin C.gates.length × Fin 2) : Finset (Sym2 (Fin n)) :=
    U.filter (fun e => ∃ u v : Fin n, e = s(u,v) ∧ v ∈ side C p.1 p.2 ∧
      (side (n := n) C p.1 p.2).card ≤ 3 ∧ 4 ≤ (orIn n C (n + p.1)).card ∧
      (missed (orIn n C (n + p.1)) u).card ≤ 1)
  have smallCount (j) : (small j).card ≤ 9 := by
    dsimp only [small]
    split
    · rename_i both
      refine (Finset.card_image_le).trans ?_
      rw [Finset.card_product]
      exact (Nat.mul_le_mul both.1 both.2)
    · simp
  have wideCount (p) : (wide p).card ≤ 3 := by
    by_cases existsEdge : (wide p).Nonempty
    · obtain ⟨e, he⟩ := existsEdge
      obtain ⟨u, v, _, _, hsmall, hlarge, hu⟩ := (Finset.mem_filter.mp he).2
      have sub : wide p ⊆ (side C p.1 p.2).image (fun t => s(u,t)) := by
        intro f hf
        obtain ⟨a, b, h, hb, _, _, ha⟩ := (Finset.mem_filter.mp hf).2
        have ea := unique (orIn n C (n + p.1)) hlarge a u ha hu
        exact Finset.mem_image.mpr ⟨b, hb, by rw [h, ea]⟩
      exact (Finset.card_le_card sub).trans Finset.card_image_le |>.trans hsmall
    · rw [Finset.not_nonempty_iff_eq_empty.mp existsEdge]
      simp
  let S := Finset.univ.biUnion small
  let W := Finset.univ.biUnion wide
  have cover : U.filter good ⊆ S ∪ W := by
    intro e he
    obtain ⟨hit,u,v,j,r,hu,hv,r0,r1⟩ :=
      show e ∈ U ∧ good e from Finset.mem_filter.mp he
    have onWide (b : Fin 2) (a t : Fin n) (eq : e = s(a,t))
        (ht : t ∈ side C j b) (hbig : 4 ≤ (side (n := n) C j b).card)
        (ha : (missed (side C j b) a).card ≤ 1) : e ∈ W := by
      obtain ⟨h, c, sub, big, leaf, cap⟩ := frontier n C least.1 (opnd C j b) t hbig ht
      have misses : (missed (orIn n C (n + h)) a).card ≤ 1 :=
        (Finset.card_le_card (Finset.filter_subset_filter _ sub)).trans ha
      exact Finset.mem_biUnion.mpr ⟨(h,c), Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hit, a, t, eq, leaf, cap, big, misses⟩⟩
    by_cases h0 : 4 ≤ (side (n := n) C j 0).card
    · exact Finset.mem_union_right _ (onWide 0 v u (r.trans Sym2.eq_swap) hu h0 r0)
    by_cases h1 : 4 ≤ (side (n := n) C j 1).card
    · exact Finset.mem_union_right _ (onWide 1 u v r hv h1 r1)
    have small0 : (side (n := n) C j 0).card ≤ 3 := by omega
    have small1 : (side (n := n) C j 1).card ≤ 3 := by omega
    have hs : e ∈ small j := by
      dsimp only [small]
      rw [ite_eq_left ⟨small0, small1⟩]
      exact Finset.mem_image.mpr ⟨(u,v), Finset.mem_product.mpr ⟨hu,hv⟩, r.symm⟩
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hs⟩)
  have gateCount : C.size = C.gates.length := rfl
  have hS : S.card ≤ 9 * C.size := by
    refine (Finset.card_biUnion_le).trans ((Finset.sum_le_sum fun j _ => smallCount j).trans ?_)
    simp [gateCount, Nat.mul_comm]
  have hW : W.card ≤ 6 * C.size := by
    refine (Finset.card_biUnion_le).trans ((Finset.sum_le_sum fun p _ => wideCount p).trans ?_)
    simp [gateCount, Fintype.card_prod, Nat.mul_assoc, Nat.mul_comm]
  have bounded : (U.filter good).card ≤ 15 * C.size :=
    ((Finset.card_le_card cover).trans (Finset.card_union_le S W)).trans (by omega)
  have rest : (U.filter fun e => ¬ good e).card ≤ k * (C.size + 1) :=
    bound n G girth edge C _ least top (Finset.filter_subset _ _) (fun e he => (Finset.mem_filter.mp he).2)
  have split := Finset.card_filter_add_card_filter_not (s := U) good
  change U.card ≤ (15 + k) * (C.size + 1)
  rw [Nat.add_mul]
  omega
