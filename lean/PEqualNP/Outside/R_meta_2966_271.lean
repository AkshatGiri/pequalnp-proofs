import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2966_271
    (floor :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ (s : ℕ) (op : Fin s → Bool) (a b : Fin s → ℕ × Bool)
        (o : ℕ) (v : (Fin 9 → Bool) → ℕ → Bool), s ≤ 12 → (∀ j, (a j).1 < 10+j.val ∧ (b j).1 < 10+j.val) → o < 10+s →
        (∀ (x : Fin 9 → Bool) (i : Fin 9), v x i.val = x i) → (∀ x, v x 9 = false) →
        (∀ (x : Fin 9 → Bool) (j : Fin s),
          let e (i : ℕ × Bool) := v x i.1 ^^ i.2
          v x (10+j.val) = if op j then e (a j) && e (b j) else e (a j) || e (b j)) →
        ∃ x : Fin 9 → Bool, v x o ≠ f x)
    (few :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ (s : ℕ) (op : Fin s → Bool) (a b : Fin s → ℕ × Bool)
        (o : ℕ) (v : (Fin 9 → Bool) → ℕ → Bool), ∀ q : Finset ℕ, q.card ≤ 1 → s+q.card ≤ 14 → o < 10+s →
        (∀ j : Fin s,
          let ok (i : ℕ × Bool) := i.1 < 10+j.val ∧ (i.2 = true → i.1 = 0 ∨ i.1 = 9 ∨ i.1 ∈ q)
          ok (a j) ∧ ok (b j)) →
        (∀ (x : Fin 9 → Bool) (i : Fin 9), v x i.val = x i) → (∀ x, v x 9 = false) →
        (∀ (x : Fin 9 → Bool) (j : Fin s),
          let e (i : ℕ × Bool) := v x i.1 ^^ i.2
          v x (10+j.val) = if op j then e (a j) && e (b j) else e (a j) || e (b j)) →
        ∃ x : Fin 9 → Bool, v x o ≠ f x) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x6.card ≤ (3 : ℕ) →     x1 + x6.card ≤ (14 : ℕ) →       (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →         x5.1 < (10 : ℕ) + x1 →           x5.2 = Bool.false →             (have x13 : ℕ × Bool → Prop := fun (x13 : ℕ × Bool) => x13.2 = Bool.true → x13.1 = (0 : ℕ) ∨ x13.1 = (9 : ℕ) ∨ x13.1 ∈ x6;               x13 x5 ∧ ∀ (x14 : Fin x1), x13 (x3 x14) ∧ x13 (x4 x14)) →               (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin (9 : ℕ)), x7 x14 ↑x15 = x14 x15) →                 (∀ (x15 : Fin (9 : ℕ) → Bool), x7 x15 (9 : ℕ) = Bool.false) →                   (∀ (x16 : Fin (9 : ℕ) → Bool) (x17 : Fin x1),                       have x18 : ℕ × Bool → Bool := fun (x18 : ℕ × Bool) => x7 x16 x18.1 ^^ x18.2;                       x7 x16 ((10 : ℕ) + ↑x17) = if x2 x17 = Bool.true then x18 (x3 x17) && x18 (x4 x17) else x18 (x3 x17) || x18 (x4 x17)) →                     ∃ (x17 : Fin (9 : ℕ) → Bool), (x7 x17 x5.1 ^^ x5.2) ≠ (x17 (0 : Fin (9 : ℕ)) && x17 (1 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (2 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (3 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (4 : Fin (9 : ℕ)) || x17 (4 : Fin (9 : ℕ)) && x17 (0 : Fin (9 : ℕ)) || x17 (0 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (6 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (5 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (6 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (8 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ))) := by
  intro s op a b out q v q3 cost earlier outValid positive phases raw zero gate
  have ha : ∀ j : Fin s, (a j).2 = true → (a j).1 = 0 ∨ (a j).1 = 9 ∨ (a j).1 ∈ q :=
    fun j => (phases.2 j).1
  have hb : ∀ j : Fin s, (b j).2 = true → (b j).1 = 0 ∨ (b j).1 = 9 ∨ (b j).1 ∈ q :=
    fun j => (phases.2 j).2
  have test : ∃ x : Fin 9 → Bool, v x out.1 ≠ (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) x := by
    by_cases small : q.card ≤ 1
    · exact few s op a b out.1 v q small cost outValid
        (fun j => ⟨⟨(earlier j).1,ha j⟩,⟨(earlier j).2,hb j⟩⟩) raw zero gate
    · exact floor s op a b out.1 v (by omega) earlier outValid raw zero gate
  obtain ⟨x,hx⟩ := test
  refine ⟨x,?_⟩
  rw [positive,Bool.xor_false]
  simp only [List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] at hx ⊢
  exact hx
