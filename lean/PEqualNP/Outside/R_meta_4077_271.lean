import PEqualNP.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Order

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- At position 18, a wire depending on all ten inputs would unfold into a
-- ten-leaf formula. Three rejected independent sets rule out that leaf count.

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4077_271
    (threshold : let goal := fun x : Fin 10 → Bool => decide (∃ a b : Fin 10, a < b ∧
    (14321644013157 : ℕ).testBit (b.val*(b.val-1)/2+a.val) = true ∧ x a = true ∧ x b = true)
    let star := fun (k : Fin 5) (i : Fin 10) => (850517762974836 : ℕ).testBit (10*k.val+i.val)
    ∀ (flag : Bool) (C : Circuit) (o : ℕ), FanInTwo C →
      let f := fun x : Fin 10 → Bool => (C.wires (List.ofFn x ++ [x 0 || if flag = true then x 1 else x 2])).getD o false
      (∀ x, goal x = true → f x = true) →
      (∃ x, f x = false) → 14 ≤ o ∧
        ((∃ a b c : Fin 5, a < b ∧ b < c ∧ f (star a) = false ∧ f (star b) = false ∧ f (star c) = false) → 19 ≤ o ∧ ¬ HasLeafSize 10 f 10))
    (remaining : let goal := fun x : Fin 10 → Bool => decide (∃ a b : Fin 10, a < b ∧
    (14321644013157 : ℕ).testBit (b.val*(b.val-1)/2+a.val) = true ∧ x a = true ∧ x b = true)
    let star := fun (k : Fin 5) (i : Fin 10) => (850517762974836 : ℕ).testBit (10*k.val+i.val)
    ∀ (flag : Bool) (C : Circuit) (r s : Fin (11 + C.size)), FanInTwo C → C.size ≤ 17 →
      19 ≤ r.val → 14 ≤ s.val →
      let w := fun (x : Fin 10 → Bool) (o : ℕ) => (C.wires (List.ofFn x ++ [x 0 || if flag = true then x 1 else x 2])).getD o false
      let f := fun x => w x r
      let g := fun x => w x s
      (∃ a b c : Fin 5, a < b ∧ b < c ∧ f (star a) = false ∧ f (star b) = false ∧ f (star c) = false) →
      ¬ HasLeafSize 10 f 10 →
      (∃ x, f x = true ∧ g x = false) → (∃ x, f x = false ∧ g x = true) →
      ¬ (∀ x, (f x && g x) = goal x)) :
  ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) || if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true := by
  intro flag C u v fan cap F W uv vu on
  let goal := fun x : Fin 10 → Bool => decide (∃ a b : Fin 10, a < b ∧
    (14321644013157 : ℕ).testBit (b.val*(b.val-1)/2+a.val) = true ∧ x a = true ∧ x b = true)
  let star := fun (k : Fin 5) (i : Fin 10) => (850517762974836 : ℕ).testBit (10*k.val+i.val)
  have encoded : ∀ a b : Fin 10,
      (a < b ∧ (14321644013157 : ℕ).testBit (b.val*(b.val-1)/2+a.val) = true) ↔
        (a = 0 ∧ b = 1) ∨
        (a = 1 ∧ b = 2) ∨
        (a = 2 ∧ b = 3) ∨
        (a = 3 ∧ b = 4) ∨
        (a = 0 ∧ b = 4) ∨
        (a = 0 ∧ b = 5) ∨
        (a = 1 ∧ b = 6) ∨
        (a = 2 ∧ b = 7) ∨
        (a = 3 ∧ b = 8) ∨
        (a = 4 ∧ b = 9) ∨
        (a = 5 ∧ b = 7) ∨
        (a = 7 ∧ b = 9) ∨
        (a = 6 ∧ b = 9) ∨
        (a = 6 ∧ b = 8) ∨
        (a = 5 ∧ b = 8) := by decide +kernel
  have meaning (x) : goal x = F x := by
    apply Bool.eq_iff_iff.mpr
    simp only [goal, decide_eq_true_eq, F, Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨a,b,ordered,bit,ha,hb⟩
      rcases (encoded a b).mp ⟨ordered,bit⟩ with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨ha,hb⟩))))))))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ha,hb⟩)))))))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ha,hb⟩))))))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ha,hb⟩)))))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hb,ha⟩))))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ha,hb⟩)))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ha,hb⟩))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ha,hb⟩)))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ha,hb⟩))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ha,hb⟩)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ha,hb⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨ha,hb⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨hb,ha⟩))
      · exact Or.inl (Or.inr ⟨ha,hb⟩)
      · exact Or.inr ⟨hb,ha⟩
    · intro hx
      rcases hx with ((((((((((((((⟨hx,hy⟩ | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩)
      · exact ⟨0,1,by decide,by decide,hx,hy⟩
      · exact ⟨1,2,by decide,by decide,hx,hy⟩
      · exact ⟨2,3,by decide,by decide,hx,hy⟩
      · exact ⟨3,4,by decide,by decide,hx,hy⟩
      · exact ⟨0,4,by decide,by decide,hy,hx⟩
      · exact ⟨0,5,by decide,by decide,hx,hy⟩
      · exact ⟨1,6,by decide,by decide,hx,hy⟩
      · exact ⟨2,7,by decide,by decide,hx,hy⟩
      · exact ⟨3,8,by decide,by decide,hx,hy⟩
      · exact ⟨4,9,by decide,by decide,hx,hy⟩
      · exact ⟨5,7,by decide,by decide,hx,hy⟩
      · exact ⟨7,9,by decide,by decide,hx,hy⟩
      · exact ⟨6,9,by decide,by decide,hy,hx⟩
      · exact ⟨6,8,by decide,by decide,hx,hy⟩
      · exact ⟨5,8,by decide,by decide,hy,hx⟩
  have negative : ∀ a, goal (star a) = false := by decide +kernel
  let three (f : (Fin 10 → Bool) → Bool) := ∃ a b c : Fin 5, a < b ∧ b < c ∧ f (star a) = false ∧ f (star b) = false ∧ f (star c) = false
  have countSmall : ∀ a : Fin 5 → Bool,
      ¬ (∃ i j k : Fin 5, i < j ∧ j < k ∧ a i = false ∧ a j = false ∧ a k = false) →
      ((Finset.univ : Finset (Fin 5)).filter (fun j => a j = false)).card ≤ 2 := by
    decide +kernel
  have majority (a b : Fin 5 → Bool) (noBoth : ∀ j, (a j && b j) = false) :
      (∃ i j k : Fin 5, i < j ∧ j < k ∧ a i = false ∧ a j = false ∧ a k = false) ∨
      (∃ i j k : Fin 5, i < j ∧ j < k ∧ b i = false ∧ b j = false ∧ b k = false) := by
    by_contra neither
    let A := (Finset.univ : Finset (Fin 5)).filter (fun j => a j = false)
    let B := (Finset.univ : Finset (Fin 5)).filter (fun j => b j = false)
    have aSmall : A.card ≤ 2 := countSmall a (fun h => neither (Or.inl h))
    have bSmall : B.card ≤ 2 := countSmall b (fun h => neither (Or.inr h))
    have union : A ∪ B = Finset.univ := by
      ext j
      simp only [Finset.mem_union, A, B, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      by_cases ha : a j = false
      · exact Or.inl ha
      · have haTrue : a j = true := by
          cases hj : a j
          · exact (ha hj).elim
          · rfl
        exact Or.inr (by simpa [haTrue] using noBoth j)
    have large : 5 ≤ A.card + B.card := by simpa [union] using Finset.card_union_le A B
    omega
  by_contra no
  have prod (x) : (W x u && W x v) = goal x := by
    rw [meaning]
    cases hf : F x
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨hu,hv⟩ := Bool.and_eq_true_iff.mp h
      exact no ⟨x,hf,hu,hv⟩
    · exact Bool.and_eq_true_iff.mpr (on x hf)
  have cover (x) (hx : goal x = true) : W x u = true ∧ W x v = true :=
    Bool.and_eq_true_iff.mp ((prod x).trans hx)
  have markU := threshold flag C u fan (fun x hx => (cover x hx).1)
    (by obtain ⟨x,h,_⟩ := vu; exact ⟨x,h⟩)
  have markV := threshold flag C v fan (fun x hx => (cover x hx).2)
    (by obtain ⟨x,_,h⟩ := uv; exact ⟨x,h⟩)
  have isPresent (o : ℕ) (h : ∃ x, W x o = true) : o < 11 + C.size := by
    by_contra! missing
    obtain ⟨x, val⟩ := h
    let w := List.ofFn x ++ [x 0 || if flag = true then x 1 else x 2]
    let step (h : List Bool) (g : Gate) := h ++ [g.op.eval (g.inputs.map fun j => h.getD j false)]
    have len (gs : List Gate) (h : List Bool) : (gs.foldl step h).length = h.length + gs.length := by
      induction gs generalizing h with
      | nil => simp
      | cons g t ih =>
        rw [List.foldl_cons, ih]
        simp [step]
        omega
    have length : (C.wires w).length = 11 + C.size := by
      change (C.gates.foldl step w).length = 11 + C.gates.length
      rw [len]
      simp [w]
    change (C.wires w).getD o false = true at val
    rw [List.getD_eq_default _ _ (by rw [length]; exact missing)] at val
    contradiction
  have U := isPresent u (by obtain ⟨x,h,_⟩ := uv; exact ⟨x,h⟩)
  have V := isPresent v (by obtain ⟨x,_,h⟩ := vu; exact ⟨x,h⟩)
  have oneStrong : three (fun x => W x u) ∨ three (fun x => W x v) :=
    majority (fun a => W (star a) u) (fun a => W (star a) v)
      (fun a => (prod _).trans (negative a))
  rcases oneStrong with left | right
  · obtain ⟨early,leaf⟩ := markU.2 left
    exact (remaining flag C ⟨u,U⟩ ⟨v,V⟩ fan cap early markV.1 left leaf uv vu) prod
  · obtain ⟨early,leaf⟩ := markV.2 right
    have uv' : ∃ x, W x v = true ∧ W x u = false := by
      obtain ⟨x,hu,hv⟩ := vu
      exact ⟨x,hv,hu⟩
    have vu' : ∃ x, W x v = false ∧ W x u = true := by
      obtain ⟨x,hu,hv⟩ := uv
      exact ⟨x,hv,hu⟩
    have prod' (x) : (W x v && W x u) = goal x := (Bool.and_comm ..).trans (prod x)
    exact (remaining flag C ⟨v,V⟩ ⟨u,U⟩ fan cap early markU.1 right leaf uv' vu') prod'
