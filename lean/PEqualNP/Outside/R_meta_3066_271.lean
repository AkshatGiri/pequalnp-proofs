import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3500000 in
theorem PEqualNP.Outside.R_meta_3066_271
    (minimum :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ C : Circuit, FanInTwo C → (∀ x, C.eval (List.ofFn x) = f x) → 15 ≤ C.size)
    (floor :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ C : Circuit, FanInTwo C → (∀ x, C.eval (List.ofFn x) = f x) →
        13 ≤ (C.gates.filter fun g => !(g.op.eval [false,false])).length)
    (readers :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let rd (v : ℕ) (g : Gate) := g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs
      ∀ C : Circuit, FanInTwo C →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
        (∀ x, C.eval (List.ofFn x) = f x) → C.size ≤ 15 →
        ∀ v ∈ ([4,6] : List ℕ), ∃! i : Fin (C.gates.drop 1).length, rd v ((C.gates.drop 1).get i))
    (few :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ (gs : List Gate) (ps : List (Fin 24)), gs.length = 13 → FanInTwo ⟨gs,0⟩ →
        (∀ g ∈ gs, ∀ i ∈ g.inputs, i ≤ 23) → ps.length = 2 → ps.Nodup →
        (∀ p ∈ ps, 10 ≤ p.val ∧ p.val < 23) →
        22 ∈ ps.map Fin.val →
        (∀ v ∈ ([4,6] : List ℕ), ∀ i j : Fin gs.length,
          let rd (g : Gate) := g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs
          rd (gs.get i) → rd (gs.get j) → i = j) →
        (gs.filter fun g => g.op.eval [false,false]).length ≤ 2 →
        ∃ x : Fin 9 → Bool,
          let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 4 || x 6])
          GateOp.or.eval (ps.map fun p => w.getD p.val false) ≠ f x) :
∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))
 := by
  intro gs ps size fan bound two
  by_contra! agreement
  let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  let eval (x : Fin 9 → Bool) :=
    let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 4 || x 6])
    GateOp.or.eval (ps.map fun p => w.getD p.val false)
  have orOne (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl
  have orTwo (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
  have agrees (x : Fin 9 → Bool) : eval x = f x := by
    have eq := not_not.mp (agreement x)
    change eval x = _ at eq
    unfold f
    simp only [List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] at eq ⊢
    exact eq
  have lookup {α : Type} (w : List α) (a b : α) (i : ℕ) (h : i < w.length) :
      (w ++ [a]).getD i b = w.getD i b := by
    simp [List.getD,List.getElem?_append_left h]
  have atEnd {α : Type} (w : List α) (a b : α) : (w ++ [a]).getD w.length b = a := by
    simp [List.getD]
  have retain (ls : List Gate) (w : List Bool) (i : ℕ) (inside : i < w.length) :
      ((Circuit.mk ls 0).wires w).getD i false = w.getD i false := by
    induction ls generalizing w with
    | nil => rfl
    | cons g ls ih =>
      let bit := g.op.eval (g.inputs.map (fun j => w.getD j false))
      change ((Circuit.mk ls 0).wires (w ++ [bit])).getD i false = _
      rw [ih _ (by simp; omega)]
      exact lookup w bit false i inside
  have wiresLen (ls : List Gate) (w : List Bool) : ((Circuit.mk ls 0).wires w).length = w.length + ls.length := by
    induction ls generalizing w with
    | nil => rfl
    | cons g ls ih =>
      let bit := g.op.eval (g.inputs.map (fun i => w.getD i false))
      change ((Circuit.mk ls 0).wires (w ++ [bit])).length = _
      rw [ih]
      simp
      omega
  let probe (i : Fin 10) (j : Fin 9) := decide (j.val = if i.val = 9 then 4 else i.val)
  have inputs : ∀ i : Fin 10,
      (List.ofFn (probe i) ++ [probe i 4 || probe i 6]).getD i.val false = true := by
    decide +kernel
  have notEdge : ∀ i : Fin 10, f (probe i) = false := by decide +kernel
  have realPin : ∀ p ∈ ps, 10 ≤ p.val := by
    intro p hp
    by_contra! early
    let i : Fin 10 := ⟨p.val,early⟩
    let w := List.ofFn (probe i) ++ [probe i 4 || probe i 6]
    have h : w.getD p.val false = true := inputs i
    have atPin : ((Circuit.mk gs 0).wires w).getD p.val false = true := by
      rw [retain gs w p.val (by simp [w]; omega),h]
    have yes : eval (probe i) = true := by
      change (ps.map fun p => ((Circuit.mk gs 0).wires w).getD p.val false).any id = true
      apply List.any_eq_true.mpr
      refine ⟨true,List.mem_map.mpr ⟨p,hp,atPin⟩,rfl⟩
    rw [agrees,notEdge] at yes
    cases yes
  let first : Gate := ⟨.or,[4,6]⟩
  let last : Gate := ⟨.or,ps.map Fin.val⟩
  let C : Circuit := ⟨first :: (gs ++ [last]),10+gs.length⟩
  have seed (x : Fin 9 → Bool) :
      first.op.eval (first.inputs.map (fun i => (List.ofFn x).getD i false)) = (x 4 || x 6) := by
    simp [first,orTwo,List.getD_eq_getElem?_getD]
  have legal : FanInTwo C := by
    intro g hg
    change g ∈ first :: (gs ++ [last]) at hg
    rcases List.mem_cons.mp hg with rfl | mid
    · exact ⟨Or.inr (Or.inl rfl),by decide⟩
    · rcases List.mem_append.mp mid with mid | lastMember
      · exact fan g mid
      · obtain rfl := List.mem_singleton.mp lastMember
        exact ⟨Or.inr (Or.inl rfl),by simpa [last] using two⟩
  have ends (ls : List Gate) (ts : List (Fin 24)) (x : Fin 9 → Bool) :
      (Circuit.mk (first :: (ls ++ [⟨.or,ts.map Fin.val⟩])) (10+ls.length)).eval (List.ofFn x) =
      GateOp.or.eval (ts.map fun p =>
        ((Circuit.mk ls 0).wires (List.ofFn x ++ [x 4 || x 6])).getD p.val false) := by
    let final : Gate := ⟨.or,ts.map Fin.val⟩
    let raw := List.ofFn x
    change ((first :: (ls ++ [final])).foldl (fun w g =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) raw).getD (10+ls.length) false = _
    rw [List.foldl_cons,seed x,List.foldl_append]
    let mid := (Circuit.mk ls 0).wires (raw ++ [x 4 || x 6])
    change (mid ++ [final.op.eval (final.inputs.map fun i => mid.getD i false)]).getD (10+ls.length) false = _
    have midLen : mid.length = 10+ls.length := by rw [wiresLen]; simp [raw]
    rw [← midLen,atEnd]
    simp only [final,List.map_map,Function.comp_def,mid,raw] <;> rfl
  have same (x : Fin 9 → Bool) : C.eval (List.ofFn x) = eval x := ends gs ps x
  have computes (x : Fin 9 → Bool) : C.eval (List.ofFn x) = f x := (same x).trans (agrees x)
  have length : gs.length = 13 := by
    have m := minimum C legal computes
    change 15 ≤ (first :: (gs ++ [last])).length at m
    simp at m
    omega
  let table (x : Fin 9 → Bool) := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 4 || x 6])
  have tableLength (x : Fin 9 → Bool) : (table x).length = 23 := by
    unfold table
    rw [wiresLen]
    simp [length]
  have noSingle (p : Fin 24) (only : ∀ x, eval x = (table x).getD p.val false) : False := by
    let prefixCircuit : Circuit := ⟨first :: gs,p.val⟩
    have ok : FanInTwo prefixCircuit := by
      intro g hg
      change g ∈ first :: gs at hg
      apply legal g
      change g ∈ first :: (gs ++ [last])
      rcases List.mem_cons.mp hg with head | member
      · exact List.mem_cons.mpr (Or.inl head)
      · exact List.mem_cons.mpr (Or.inr (List.mem_append_left _ member))
    have agreesPrefix (x : Fin 9 → Bool) : prefixCircuit.eval (List.ofFn x) = f x := by
      have result : prefixCircuit.eval (List.ofFn x) = (table x).getD p.val false := by
        change ((first :: gs).foldl (fun w g =>
          w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD p.val false = _
        rw [List.foldl_cons,seed x]
        rfl
      exact result.trans ((only x).symm.trans (agrees x))
    have tooSmall := minimum prefixCircuit ok agreesPrefix
    change 15 ≤ (first :: gs).length at tooSmall
    simp [length] at tooSmall
  have pins : ∃ p q : Fin 24, ps = [p,q] ∧ p ≠ q ∧ p.val < 23 ∧ q.val < 23 := by
    cases ps with
    | nil =>
      have h := agrees (fun i => decide (i = 0 ∨ i = 1))
      change false = true at h
      cases h
    | cons p rest =>
      cases rest with
      | nil =>
        exact (noSingle p (by intro x; simp [eval,table,orOne])).elim
      | cons q extra =>
        have empty : extra = [] := by
          cases extra with
          | nil => rfl
          | cons a as => simp at two <;> omega
        subst extra
        have diff : p ≠ q := by
          intro eq
          exact noSingle p (by intro x; simp [eval,table,orTwo,eq])
        have below (r : Fin 24) (missing : ¬ r.val < 23) (x : Fin 9 → Bool) :
            (table x).getD r.val false = false := by
          apply List.getD_eq_default
          rw [tableLength]
          omega
        have disjoin (x : Fin 9 → Bool) : eval x =
            ((table x).getD p.val false || (table x).getD q.val false) := by
          simp [eval,table,orTwo]
        have vp : p.val < 23 := by
          by_contra missing
          apply noSingle q
          intro x
          rw [disjoin x,below p missing] <;> simp
        have vq : q.val < 23 := by
          by_contra missing
          apply noSingle p
          intro x
          rw [disjoin x,below q missing] <;> simp
        exact ⟨p,q,rfl,diff,vp,vq⟩
  obtain ⟨a,b,eq,distinct,ha,hb⟩ := pins
  have properLength : ps.length = 2 := by simp [eq]
  have distinctPins : ps.Nodup := by simp [eq,distinct]
  have valid : ∀ p ∈ ps, 10 ≤ p.val ∧ p.val < 23 := by
    intro p hp
    refine ⟨realPin p hp, ?_⟩
    rw [eq] at hp
    rcases List.mem_cons.mp hp with rfl | later
    · exact ha
    · obtain rfl := List.mem_singleton.mp later
      exact hb
  have hasLast : 22 ∈ ps.map Fin.val := by
    by_contra missing
    have early (p : Fin 24) (hp : p ∈ ps) : p.val < 22 := by
      have proper := (valid p hp).2
      have different : p.val ≠ 22 := fun eq => missing (List.mem_map.mpr ⟨p,hp,eq⟩)
      omega
    have nonempty : gs ≠ [] := by intro h; simp [h] at length
    have lastGate : ∃ ls g, gs = ls ++ [g] := by
      cases h : gs.reverse with
      | nil => exact (nonempty (by simpa using congrArg List.reverse h)).elim
      | cons g rev => exact ⟨rev.reverse,g,by simpa using congrArg List.reverse h⟩
    obtain ⟨ls,g,split⟩ := lastGate
    have len : ls.length = 12 := by rw [split] at length; simp at length; omega
    let small : Circuit := ⟨first :: (ls ++ [last]),10+ls.length⟩
    have ok : FanInTwo small := by
      intro h hh
      change h ∈ first :: (ls ++ [last]) at hh
      apply legal h
      change h ∈ first :: (gs ++ [last])
      rcases List.mem_cons.mp hh with head | inside
      · exact List.mem_cons.mpr (Or.inl head)
      · apply List.mem_cons.mpr
        right
        rcases List.mem_append.mp inside with mid | fin
        · exact List.mem_append_left _ (by rw [split]; exact List.mem_append_left _ mid)
        · exact List.mem_append_right _ fin
    have smallComputes (x : Fin 9 → Bool) : small.eval (List.ofFn x) = f x := by
      have result := ends ls ps x
      change small.eval (List.ofFn x) = _ at result
      rw [result,← agrees x]
      change GateOp.or.eval _ = GateOp.or.eval _
      congr 1
      apply List.map_congr_left
      intro p hp
      let start := List.ofFn x ++ [x 4 || x 6]
      let w := (Circuit.mk ls 0).wires start
      have wLen : w.length = 22 := by rw [wiresLen]; simp [start,len]
      have inside : p.val < w.length := by rw [wLen]; exact early p hp
      change w.getD p.val false = ((Circuit.mk gs 0).wires start).getD p.val false
      rw [split]
      change w.getD p.val false = ((ls ++ [g]).foldl
        (fun z h => z ++ [h.op.eval (h.inputs.map fun j => z.getD j false)]) start).getD p.val false
      rw [List.foldl_append]
      change w.getD p.val false = (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD p.val false
      rw [lookup _ _ _ _ inside]
    have tooSmall := minimum small ok smallComputes
    change 15 ≤ (first :: (ls ++ [last])).length at tooSmall
    simp [len] at tooSmall
  have headWire (x : Fin 9 → Bool) : (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6) := by
    let raw := List.ofFn x
    change ((Circuit.mk (gs ++ [last]) 0).wires
      (raw ++ [first.op.eval (first.inputs.map fun j => raw.getD j false)])).getD 9 false = _
    rw [seed x,retain _ _ _ (by simp [raw])]
    have n : raw.length = 9 := by simp [raw]
    simpa only [n] using atEnd raw (x 4 || x 6) false
  have wholeSize : C.size ≤ 15 := by
    change (first :: (gs ++ [last])).length ≤ 15
    simp [length]
  have unique (v : ℕ) (hv : v ∈ ([4,6] : List ℕ)) (i j : Fin gs.length) :
      let rd (g : Gate) := g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs
      rd (gs.get i) → rd (gs.get j) → i = j := by
    intro rd hi hj
    obtain ⟨w,_,alone⟩ := readers C legal headWire computes wholeSize v hv
    let lift (a : Fin gs.length) : Fin (C.gates.drop 1).length :=
      ⟨a.val,by change a.val < (gs ++ [last]).length; simp⟩
    have atGate (a : Fin gs.length) : (C.gates.drop 1).get (lift a) = gs.get a := by
      change (gs ++ [last]).get _ = gs.get a
      simp only [List.get_eq_getElem]
      exact List.getElem_append_left a.isLt
    have hI := alone (lift i) (by simpa only [atGate] using hi)
    have hJ := alone (lift j) (by simpa only [atGate] using hj)
    have places := congrArg (fun u : Fin (C.gates.drop 1).length => u.val) (hI.trans hJ.symm)
    exact Fin.val_injective places
  have complete := floor C legal computes
  let isNot (g : Gate) : Bool := g.op.eval [false,false]
  have book (ls : List Gate) : (ls.filter fun g => !isNot g).length + (ls.filter isNot).length = ls.length := by
    induction ls with
    | nil => rfl
    | cons g ls ih =>
      cases b : isNot g <;> simp [b] <;> omega
  change 13 ≤ ((first :: (gs ++ [last])).filter fun g => !isNot g).length at complete
  have atFirst : (!isNot first) = true := rfl
  have atLast : (!isNot last) = true := rfl
  have total : ((first :: (gs ++ [last])).filter fun g => !isNot g).length =
      (gs.filter fun g => !isNot g).length + 2 := by
    simp [List.filter_append,atFirst,atLast]
  rw [total] at complete
  have fewer : (gs.filter isNot).length ≤ 2 := by
    have sum := book gs
    omega
  obtain ⟨x,miss⟩ := few gs ps length fan bound properLength distinctPins valid hasLast unique fewer
  exact miss (agrees x)
