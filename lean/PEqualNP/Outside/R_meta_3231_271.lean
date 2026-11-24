import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_3231_271
    -- The six graph-symmetry representatives are bounded by L-meta-1667 through L-meta-1672.
    (firstAnd :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ (p r : Fin 9) (C : Circuit), p ≠ r → FanInTwo C →
        (∀ x, (C.wires (List.ofFn x)).getD 9 false = (x p && x r)) →
        (∀ x, C.eval (List.ofFn x) = f x) → 16 ≤ C.size)
    -- The remaining second-AND patterns feed a continuation ending at its output gate.
    (continuation :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ (gs : List Gate) (ps : List ℕ), gs.length ≤ 13 → gs ≠ [] →
        FanInTwo ⟨gs,0⟩ → ps.length ≤ 2 → ps ≤ ps.map (fun i => [1,0,5,8,6,2,4,7,3].getD i i) →
        (¬ ∃ p r : Fin 9, p ≠ r ∧ ps = [p.val,r.val]) →
        ∃ x : Fin 9 → Bool,
          let w := List.ofFn x ++ [x 4 || x 6]
          let b := GateOp.and.eval (ps.map fun i => w.getD i false)
          ((Circuit.mk gs 0).wires (w ++ [b])).getD (10 + gs.length) false ≠ f x) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5.inputs ≤ List.map (fun (x8 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x8 x8) x5.inputs → (16 : ℕ) ≤ x1.size
 := by
  intro C fan headWire computes g second kind order
  -- The wire-table invariants and gate simplification are adapted from L-meta-551.
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

  have wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    induction gs₁ generalizing w with
    | nil => rfl
    | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

  have wiresFrom_length (gs : List Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [wiresFrom]
    | cons g gs ih =>
      rw [wiresFrom_cons, ih]
      simp
      omega

  have getD_snoc_lt {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    simp [List.getD, List.getElem?_append_left hi]

  have getD_snoc_eq {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
      (l ++ [x]).getD i d = x := by
    subst hi
    simp [List.getD]

  have getD_snoc_ne {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    by_cases hlt : i < l.length
    · exact getD_snoc_lt l x d i hlt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (wiresFrom gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [wiresFrom_cons, ih _ (by simp; omega)]
      exact getD_snoc_lt _ _ _ _ hi

  let renameGate (map : ℕ → ℕ) (g : Gate) : Gate :=
    ⟨g.op,g.inputs.map map⟩

  have after_snoc (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    by_cases atEnd : i = w.length
    · rw [if_pos atEnd,getD_snoc_eq _ _ _ _ atEnd]
    · rw [if_neg atEnd,getD_snoc_ne _ _ _ _ atEnd]

  have rename_run (k : ℕ) (map : ℕ → ℕ)
      (below : ∀ i < k, map i < k) (past : ∀ i, k ≤ i → map i = i)
      (gs : List Gate) (a b : List Bool) (size : a.length = b.length) (limit : k ≤ a.length)
      (same : ∀ i, a.getD i false = b.getD (map i) false) :
      ∀ i, (wiresFrom gs a).getD i false = (wiresFrom (gs.map (renameGate map)) b).getD (map i) false := by
    induction gs generalizing a b with
    | nil => exact same
    | cons g gs ih =>
      let p := g.op.eval (g.inputs.map fun i => a.getD i false)
      let q := (renameGate map g).op.eval ((renameGate map g).inputs.map fun i => b.getD i false)
      have equal : p = q := by
        change g.op.eval (g.inputs.map fun i => a.getD i false) =
          g.op.eval ((g.inputs.map map).map fun i => b.getD i false)
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => same i)
      have endSame (i : ℕ) : (i = a.length) ↔ map i = b.length := by
        by_cases early : i < k
        · have h := below i early
          omega
        · rw [past i (by omega),size]
      rw [List.map_cons,wiresFrom_cons,wiresFrom_cons]
      apply ih _ _ (by simp [size]) (by simp; omega)
      intro i
      rw [after_snoc, after_snoc]
      change (if i = a.length then p else a.getD i false) = _
      by_cases atEnd : i = a.length
      · rw [if_pos atEnd, if_pos ((endSame i).mp atEnd), equal]
      · rw [if_neg atEnd, if_neg (fun h => atEnd ((endSame i).mpr h)), same]

  let swap (i : ℕ) : ℕ := if i = 9 then 10 else if i = 10 then 9 else i

  have swap_values (a : List Bool) (z w : Bool) (length : a.length = 9) :
      ∀ i, (a ++ [z,w]).getD i false = (a ++ [w,z]).getD (swap i) false := by
    intro i
    by_cases h9 : i = 9
    · subst i
      have left : (a ++ [z,w]).getD 9 false = z := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
        simp [length]
      have right : (a ++ [w,z]).getD 10 false = z := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
        simp [length]
      simpa only [swap,ite_true] using left.trans right.symm
    by_cases h10 : i = 10
    · subst i
      have left : (a ++ [z,w]).getD 10 false = w := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
        simp [length]
      have right : (a ++ [w,z]).getD 9 false = w := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
        simp [length]
      simpa [swap] using left.trans right.symm
    rw [show swap i = i by simp [swap,h9,h10]]
    by_cases early : i < 9
    · have lt : i < a.length := by omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left lt]
    · rw [List.getD_eq_default _ _ (by simp [length]; omega),
        List.getD_eq_default _ _ (by simp [length]; omega)]

  have input_bit (x : Fin 9 → Bool) (p : Fin 9) (w : List Bool) :
      (List.ofFn x ++ w).getD p.val false = x p := by
    have h : p.val < (List.ofFn x).length := by simpa using p.isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    rw [List.getElem?_eq_getElem h, List.getElem_ofFn]
    rfl

  have and_raw (x : Fin 9 → Bool) (p r : Fin 9) (w : List Bool) :
      GateOp.and.eval ([p.val,r.val].map fun i => (List.ofFn x ++ w).getD i false) = (x p && x r) := by
    change GateOp.and.eval [(List.ofFn x ++ w).getD p.val false, (List.ofFn x ++ w).getD r.val false] = _
    rw [input_bit, input_bit]
    cases x p <;> cases x r <;> rfl

  have swap_early_and : ∀ (C : Circuit) (g : Gate) (p r : Fin 9), FanInTwo C →
      C.gates[1]? = some g → g.op = .and → g.inputs = [p.val,r.val] →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ circuitFun 9 D = circuitFun 9 C ∧
        ∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x p && x r) := by
    intro C g p r fan second kind rawPins headWire
    obtain ⟨gates,out⟩ := C
    rcases gates with _ | ⟨h,_ | ⟨g',tail⟩⟩
    · simp at second
    · simp at second
    have which : g' = g := Option.some.inj second
    subst g'
    let first : Gate := ⟨.and,[p.val,r.val]⟩
    let secondOR : Gate := ⟨.or,[4,6]⟩
    let D : Circuit := ⟨first :: secondOR :: tail.map (renameGate swap),swap out⟩
    have oldFirst (x : Fin 9 → Bool) : h.op.eval (h.inputs.map fun i => (List.ofFn x).getD i false) =
        (x 4 || x 6) := by
      let start := List.ofFn x
      let bit := h.op.eval (h.inputs.map fun i => start.getD i false)
      have eq := headWire x
      change (wiresFrom (g :: tail) (start ++ [bit])).getD 9 false = _ at eq
      rw [wiresFrom_getD_lt _ _ _ (by simp [start]),getD_snoc_eq _ _ _ _ (by simp [start])] at eq
      exact eq
    have Dfan : FanInTwo D := by
      intro j hj
      change j ∈ first :: secondOR :: tail.map (renameGate swap) at hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨Or.inl rfl,by change 2 ≤ 2; omega⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨Or.inr (Or.inl rfl),by decide⟩
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hj
      simpa [renameGate] using fan v (by simp [hv])
    have sameSize : D.size = (Circuit.mk (h :: g :: tail) out).size := by
      change (first :: secondOR :: tail.map (renameGate swap)).length = (h :: g :: tail).length
      simp
    refine ⟨D,Dfan,sameSize,funext (fun x => ?_),fun x => ?_⟩
    · let raw := List.ofFn x
      let a := x p && x r
      let b := x 4 || x 6
      have firstValue : first.op.eval (first.inputs.map fun i => raw.getD i false) = a := by
        simpa only [List.append_nil] using and_raw x p r []
      have secondValue : secondOR.op.eval (secondOR.inputs.map fun i => (raw ++ [a]).getD i false) = b := by
        have at4 : (List.ofFn x ++ [a]).getD 4 false = x 4 := input_bit x 4 [a]
        have at6 : (List.ofFn x ++ [a]).getD 6 false = x 6 := input_bit x 6 [a]
        change GateOp.or.eval [(List.ofFn x ++ [a]).getD 4 false, (List.ofFn x ++ [a]).getD 6 false] = b
        rw [at4, at6]
        change GateOp.or.eval [x 4, x 6] = (x 4 || x 6)
        cases x 4 <;> cases x 6 <;> rfl
      have thirdValue : g.op.eval (g.inputs.map fun i => (raw ++ [b]).getD i false) = a := by
        rw [kind,rawPins]
        exact and_raw x p r [b]
      change (wiresFrom (first :: secondOR :: tail.map (renameGate swap)) raw).getD (swap out) false =
        (wiresFrom (h :: g :: tail) raw).getD out false
      rw [wiresFrom_cons, firstValue, wiresFrom_cons, secondValue, wiresFrom_cons]
      have hb : h.op.eval (h.inputs.map fun i => raw.getD i false) = b := oldFirst x
      rw [hb, wiresFrom_cons, thirdValue]
      simp only [List.append_assoc,List.singleton_append]
      have before : ∀ i < 11, swap i < 11 := by
        intro i hi
        by_cases h9 : i = 9 <;> by_cases h10 : i = 10 <;> simp [swap,h9,h10] <;> omega
      have after : ∀ i, 11 ≤ i → swap i = i := by intro i hi; simp [swap,show i ≠ 9 by omega,show i ≠ 10 by omega]
      have relation := swap_values raw b a (by simp [raw])
      exact (rename_run 11 swap before after tail (raw ++ [b,a]) (raw ++ [a,b])
        (by simp) (by simp [raw]) relation out).symm
    · let raw := List.ofFn x
      have firstValue : first.op.eval (first.inputs.map fun i => raw.getD i false) = (x p && x r) := by
        simpa only [List.append_nil] using and_raw x p r []
      change (wiresFrom (secondOR :: tail.map (renameGate swap)) (raw ++ [first.op.eval _])).getD 9 false = _
      rw [firstValue,wiresFrom_getD_lt _ _ _ (by simp [raw]),getD_snoc_eq _ _ _ _ (by simp [raw])]
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  have success : ∀ x, C.eval (List.ofFn x) = f x := by
    intro x
    have equal := congrFun computes x
    change C.eval (List.ofFn x) = _ at equal
    simp only [f,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] at equal ⊢
    exact equal
  by_cases raw : ∃ p r : Fin 9, p ≠ r ∧ g.inputs = [p.val,r.val]
  · obtain ⟨p,r,distinct,pins⟩ := raw
    obtain ⟨D,dfan,dsize,dfunction,dfirst⟩ := swap_early_and C g p r fan second kind pins headWire
    rw [← dsize]
    exact firstAnd p r D distinct dfan dfirst (fun x => (congrFun dfunction x).trans (success x))
  by_contra! small
  obtain ⟨gates,out⟩ := C
  rcases gates with _ | ⟨h,_ | ⟨g',tail⟩⟩
  · simp at second
  · simp at second
  have which : g' = g := Option.some.inj second
  subst g'
  have tailFan : FanInTwo ⟨tail,0⟩ := by
    intro j hj
    exact fan j (List.mem_cons_of_mem h (List.mem_cons_of_mem g hj))
  have cap : tail.length ≤ 13 := by
    change (h :: g :: tail).length < 16 at small
    simp only [List.length_cons] at small
    omega
  have pinLength : g.inputs.length ≤ 2 := (fan g (by simp)).2
  let w (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
  let bit (x : Fin 9 → Bool) := GateOp.and.eval (g.inputs.map fun i => (w x).getD i false)
  have headEval (x : Fin 9 → Bool) : h.op.eval (h.inputs.map (fun i => (List.ofFn x).getD i false)) = (x 4 || x 6) := by
    let start := List.ofFn x
    let value := h.op.eval (h.inputs.map fun i => start.getD i false)
    have equal := headWire x
    change (wiresFrom (g :: tail) (start ++ [value])).getD 9 false = _ at equal
    rw [wiresFrom_getD_lt _ _ _ (by simp [start]),getD_snoc_eq _ _ _ _ (by simp [start])] at equal
    exact equal
  have correct (x : Fin 9 → Bool) : (wiresFrom tail (w x ++ [bit x])).getD out false = f x := by
    have equal := success x
    change (wiresFrom (h :: g :: tail) (List.ofFn x)).getD out false = _ at equal
    rw [wiresFrom_cons, headEval, wiresFrom_cons, kind] at equal
    exact equal
  have length (x : Fin 9 → Bool) : (w x ++ [bit x]).length = 11 := by simp [w]
  have outBound : out < 11 + tail.length := by
    by_contra! outside
    let x : Fin 9 → Bool := fun _ => true
    have no : (wiresFrom tail (w x ++ [bit x])).getD out false = false := by
      apply List.getD_eq_default
      rw [wiresFrom_length,length]
      exact outside
    have yes : f x = true := rfl
    rw [correct,yes] at no
    cases no
  have outTail : 11 ≤ out := by
    by_contra! early
    have dropTail (x : Fin 9 → Bool) := wiresFrom_getD_lt tail (w x ++ [bit x]) out (by rw [length]; exact early)
    by_cases input : out < 9
    · let i : Fin 9 := ⟨out,input⟩
      let single (i j : Fin 9) := decide (i = j)
      have no : ∀ i : Fin 9, f (single i) = false := by decide +kernel
      have read : (w (single i) ++ [bit (single i)]).getD out false = true := by
        change ((List.ofFn (single i) ++ [_]) ++ [_]).getD i.val false = true
        rw [List.append_assoc,input_bit]
        exact decide_eq_true rfl
      have eq := correct (single i)
      rw [dropTail,read,no] at eq
      cases eq
    by_cases atSeed : out = 9
    · let x : Fin 9 → Bool := fun i => decide (i = 4)
      have no : f x = false := rfl
      have read : (w x ++ [bit x]).getD out false = true := by
        rw [atSeed,getD_snoc_lt _ _ _ _ (by simp [w]),getD_snoc_eq _ _ _ _ (by simp)]
        rfl
      have eq := correct x
      rw [dropTail,read,no] at eq
      cases eq
    have lastSeed : out = 10 := by omega
    -- Three disjoint edges avoid both pins of the second gate.
    let matching : List (ℕ × ℕ) := [(0,5),(1,2),(3,8)]
    have avoids : ∀ p r : Fin 11, ∃ e ∈ matching,
        e.1 ≠ p.val ∧ e.1 ≠ r.val ∧ e.2 ≠ p.val ∧ e.2 ≠ r.val := by
      decide +kernel
    let clip (i : ℕ) : Fin 11 := ⟨min i 10,by omega⟩
    have unclip (v i : ℕ) (inside : v < 10) (apart : v ≠ (clip i).val) : v ≠ i := by
      intro equal
      subst i
      apply apart
      exact (Nat.min_eq_left (by omega)).symm
    have smallEdges : ∀ e ∈ matching, e.1 < 10 ∧ e.2 < 10 := by
      intro e present
      simp only [matching,List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with rfl | rfl | rfl <;> decide
    have edgeFree : ∃ e ∈ matching, e.1 ∉ g.inputs ∧ e.2 ∉ g.inputs := by
      generalize hp : g.inputs = pins at pinLength ⊢
      rcases pins with _ | ⟨p,_ | ⟨r,_ | ⟨s,rest⟩⟩⟩
      · exact ⟨(0,5),by simp [matching],by simp,by simp⟩
      · obtain ⟨e,he,hp₁,_,hp₂,_⟩ := avoids (clip p) (clip p)
        obtain ⟨a,b⟩ := smallEdges e he
        exact ⟨e,he,by simpa using unclip e.1 p a hp₁,by simpa using unclip e.2 p b hp₂⟩
      · obtain ⟨e,he,hp₁,hr₁,hp₂,hr₂⟩ := avoids (clip p) (clip r)
        obtain ⟨a,b⟩ := smallEdges e he
        refine ⟨e,he,?_,?_⟩
        · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨unclip e.1 p a hp₁,unclip e.1 r a hr₁⟩
        · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨unclip e.2 p b hp₂,unclip e.2 r b hr₂⟩
      · simp at pinLength
    obtain ⟨e,selected,apartA,apartB⟩ := edgeFree
    let zero : Fin 9 → Bool := fun _ => false
    let edgeRow (e : ℕ × ℕ) (i : Fin 9) := decide (i.val = e.1 ∨ i.val = e.2)
    have no : f zero = false := rfl
    have yes : f (edgeRow e) = true := by
      simp only [matching,List.mem_cons,List.not_mem_nil,or_false] at selected
      rcases selected with rfl | rfl | rfl <;> rfl
    have firstZero : (edgeRow e 4 || edgeRow e 6) = false := by
      simp only [matching,List.mem_cons,List.not_mem_nil,or_false] at selected
      rcases selected with rfl | rfl | rfl <;> rfl
    have same : bit zero = bit (edgeRow e) := by
      unfold bit
      congr 1
      apply List.map_congr_left
      intro i present
      by_cases rawPin : i < 9
      · let j : Fin 9 := ⟨i,rawPin⟩
        change (List.ofFn zero ++ [_]).getD j.val false = (List.ofFn (edgeRow e) ++ [_]).getD j.val false
        rw [input_bit,input_bit]
        change false = decide (i = e.1 ∨ i = e.2)
        have neither : ¬ (i = e.1 ∨ i = e.2) := by
          rintro (rfl | rfl)
          · exact apartA present
          · exact apartB present
        rw [decide_eq_false neither]
      by_cases sameSeed : i = 9
      · rw [sameSeed]
        change (List.ofFn zero ++ [_]).getD 9 false = (List.ofFn (edgeRow e) ++ [_]).getD 9 false
        rw [getD_snoc_eq _ _ _ _ (by simp),getD_snoc_eq _ _ _ _ (by simp),firstZero]
        rfl
      · have large : 10 ≤ i := by omega
        rw [List.getD_eq_default _ _ (by simpa [w] using large),List.getD_eq_default _ _ (by simpa [w] using large)]
    have z := correct zero
    have y := correct (edgeRow e)
    rw [dropTail,lastSeed,getD_snoc_eq _ _ _ _ (by simp [w]), no] at z
    rw [dropTail,lastSeed,getD_snoc_eq _ _ _ _ (by simp [w]), yes, ← same, z] at y
    cases y
  let n := out - 10
  let trimmed := tail.take n
  have limit : n ≤ tail.length := by dsimp [n]; omega
  have trimmedLen : trimmed.length = n := by simp [trimmed,Nat.min_eq_left limit]
  have trimmedFan : FanInTwo ⟨trimmed,0⟩ := by
    intro j hj
    exact tailFan j (List.mem_of_mem_take hj)
  have notEmpty : trimmed ≠ [] := by
    intro empty
    rw [empty] at trimmedLen
    change 0 = n at trimmedLen
    dsimp [n] at trimmedLen
    omega
  obtain ⟨x,differs⟩ := continuation trimmed g.inputs (by omega) notEmpty trimmedFan pinLength order raw
  apply differs
  have reindex : 10 + trimmed.length = out := by rw [trimmedLen]; dsimp [n]; omega
  rw [reindex]
  have equality := correct x
  have split : trimmed ++ tail.drop n = tail := List.take_append_drop n tail
  rw [← split,wiresFrom_append,wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length,length,trimmedLen]; dsimp [n]; omega)] at equality
  exact equality
