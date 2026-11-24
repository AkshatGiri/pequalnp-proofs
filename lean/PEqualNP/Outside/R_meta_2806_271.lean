import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2700000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_2806_271
    (rawBound :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ C : Circuit, FanInTwo C → (∀ x, C.eval (List.ofFn x) = f x) →
        ∀ (p r : Fin 9), p ≠ r → (Gate.mk GateOp.and [p.val,r.val]) ∈ C.gates → 16 ≤ C.size)
    (insert :
      let row (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6]
      let isNot (g : Gate) := g.op.eval [false,false]
      ∀ (v : Fin 9) (C : Circuit) (q : ℕ) (g : Gate), FanInTwo C → 10 ≤ q → q ≤ 10+C.size →
        (g.op = .and ∨ g.op = .or ∨ g.op = .not) → g.inputs.length ≤ 2 →
        (∀ h ∈ C.gates.take (q-10), v.val ∉ h.inputs) →
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size+2 ∧
          D.output = (if C.output = v.val then q else if q ≤ C.output then C.output+1 else C.output) ∧
          (D.gates.filter isNot).length = (C.gates.filter isNot).length + (if isNot g then 1 else 0) ∧
          g ∈ D.gates ∧ (∀ h ∈ C.gates, (∀ i ∈ h.inputs, i < 9 ∧ i ≠ v.val) → h ∈ D.gates) ∧
          ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = C.eval ((row x).set v.val
            (g.op.eval (g.inputs.map fun i => if i < q then (C.wires (row x)).getD i false else false))))
    (lower :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ C : Circuit, FanInTwo C → (∀ x, C.eval (List.ofFn x) = f x) →
        15 ≤ C.size ∧ 13 ≤ (C.gates.filter fun g => !(g.op.eval [false,false])).length)
    (search :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let w (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6]
      let inv (g : Gate) := g.op.eval [false,false]
      ∀ (v : Fin 9) (C : Circuit) (q : ℕ) (g : Gate), v ≠ 0 → v ≠ 6 → FanInTwo C → C.size = 13 →
        10 ≤ q → q ≤ 22 → C.output = 22 →
        (g.op = .and ∨ g.op = .or ∨ g.op = .not) → g.inputs.length ≤ 2 → v.val ∈ g.inputs →
        (∀ h ∈ C.gates.take (q-10), v.val ∉ h.inputs) →
        (C.gates.filter inv).length + (if inv g then 1 else 0) ≤ 2 →
        (∀ p r : Fin 9, p ≠ r →
          g ≠ ⟨.and,[p.val,r.val]⟩ ∧ (p ≠ v → r ≠ v → (Gate.mk .and [p.val,r.val]) ∉ C.gates)) →
        ∃ x : Fin 9 → Bool, C.eval ((w x).set v.val
          (g.op.eval (g.inputs.map fun i => if i < q then (C.wires (w x)).getD i false else false))) ≠ f x) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate),   x3 ≠ (0 : Fin (9 : ℕ)) →     x3 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 ≤ (10 : ℕ) + x4.size →               x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.not →                 x6.inputs.length ≤ (2 : ℕ) →                   ↑x3 ∈ x6.inputs →                     (∀ x16 ∈ List.take (x5 - (10 : ℕ)) x4.gates, ↑x3 ∉ x16.inputs) →                       ∃ (x17 : Fin (9 : ℕ) → Bool),                         have x18 : List Bool := x2 x17;                         x4.eval (x18.set (↑x3) (x6.op.eval (List.map (fun (x19 : ℕ) => if x19 < x5 then (x4.wires x18).getD x19 Bool.false else Bool.false) x6.inputs))) ≠ x1 x17 := by
  intro target row v C q g v0 v6 fan budget base limit mode arity reads avoids
  by_contra! all
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  obtain ⟨D,legal,sz,out,profile,there,preserves,compute⟩ := insert v C q g fan base limit mode arity avoids
  have correct (x : Fin 9 → Bool) : D.eval (List.ofFn x) = f x := by
    rw [compute x]
    have agrees := not_not.mp (all x)
    simp only [f,target,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] at agrees ⊢
    exact agrees
  have costs := lower D legal correct
  have full : C.size = 13 := by have := costs.1; omega
  have dsize : D.size = 15 := by omega
  let run (ls : List Gate) (x : List Bool) := (Circuit.mk ls 0).wires x
  have lengthRun (ls : List Gate) (x : List Bool) : (run ls x).length = x.length+ls.length := by
    induction ls generalizing x with
    | nil => rfl
    | cons g ls ih =>
      let bit := g.op.eval (g.inputs.map fun i => x.getD i false)
      change (run ls (x ++ [bit])).length = _
      rw [ih]
      simp
      omega
  have keep (ls : List Gate) (x : List Bool) (i : ℕ) (inside : i < x.length) :
      (run ls x).getD i false = x.getD i false := by
    induction ls generalizing x with
    | nil => rfl
    | cons h ls ih =>
      let bit := h.op.eval (h.inputs.map fun j => x.getD j false)
      change (run ls (x ++ [bit])).getD i false = _
      rw [ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ inside
  have appendRun (ls ts : List Gate) (x : List Bool) : run (ls++ts) x = run ts (run ls x) := by
    change List.foldl _ x (ls ++ ts) = List.foldl _ (List.foldl _ x ls) ts
    rw [List.foldl_append]
  have inside : D.output < 24 := by
    by_contra! tooHigh
    let x : Fin 9 → Bool := fun _ => true
    have no : (run D.gates (List.ofFn x)).getD D.output false = false := by
      apply List.getD_eq_default
      rw [lengthRun,List.length_ofFn]
      change 9+D.size ≤ _
      omega
    have yes : f x = true := rfl
    have result := correct x
    change (run D.gates (List.ofFn x)).getD D.output false = f x at result
    rw [no,yes] at result
    cases result
  have final : D.output = 23 := by
    by_contra! not23
    let n := D.output+1-9
    let init := D.gates.take n
    let E : Circuit := ⟨init,D.output⟩
    have enough : n ≤ D.gates.length := by change n ≤ D.size; dsimp [n]; omega
    have len : init.length = n := by simp [init,Nat.min_eq_left enough]
    have Elegal : FanInTwo E := fun g hg => legal g (List.mem_of_mem_take hg)
    have Ecompute (x : Fin 9 → Bool) : E.eval (List.ofFn x) = f x := by
      have h := correct x
      change (run D.gates (List.ofFn x)).getD D.output false = f x at h
      have split : init ++ D.gates.drop n = D.gates := List.take_append_drop _ _
      rw [← split,appendRun,keep _ _ _ (by rw [lengthRun,List.length_ofFn,len]; dsimp [n]; omega)] at h
      exact h
    have small := (lower E Elegal Ecompute).1
    change 15 ≤ init.length at small
    rw [len] at small
    dsimp [n] at small
    omega
  have endCases : q ≤ 22 ∧ C.output = 22 ∨ q = 23 ∧ C.output = v.val := by
    have rewritten := final
    rw [out] at rewritten
    by_cases atInput : C.output = v.val
    · rw [if_pos atInput] at rewritten
      exact Or.inr ⟨rewritten,atInput⟩
    rw [if_neg atInput] at rewritten
    by_cases later : q ≤ C.output
    · rw [if_pos later] at rewritten
      exact Or.inl ⟨by omega,by omega⟩
    · rw [if_neg later] at rewritten
      omega
  have notRaw : ¬ (q = 23 ∧ C.output = v.val) := by
    rintro ⟨qEq,rawOutput⟩
    let value (x : Fin 9 → Bool) (i : ℕ) := if i < q then (C.wires (row x)).getD i false else false
    let mask (x : Fin 9 → Bool) := g.op.eval (g.inputs.map (value x))
    have rowLen (x : Fin 9 → Bool) : (row x).length = 10 := by simp [row]
    have within (x : Fin 9 → Bool) : v.val < (row x).length := by rw [rowLen]; have := v.isLt; omega
    have correctMask (x : Fin 9 → Bool) : mask x = f x := by
      have yes := not_not.mp (all x)
      change (run C.gates ((row x).set v.val (mask x))).getD C.output false = target x at yes
      rw [rawOutput,keep _ _ _ (by simpa using within x),List.getD_eq_getElem?_getD,
        List.getElem?_set_self (within x)] at yes
      simp only [Option.getD_some,f,target,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] at yes ⊢
      exact yes
    have atV (x : Fin 9 → Bool) : value x v.val = x v := by
      have inside : v.val < q := by have := v.isLt; omega
      have rawLoc : v.val < (List.ofFn x).length := by simpa using v.isLt
      change (if v.val < q then (run C.gates (row x)).getD v.val false else false) = x v
      rw [if_pos inside,keep _ _ _ (within x)]
      change (List.ofFn x ++ [_]).getD v.val false = x v
      rw [List.getD_append _ _ _ _ rawLoc,List.getD_eq_getElem _ _ rawLoc,List.getElem_ofFn]
    rcases mode with isAnd | isOr | isNot
    · let x : Fin 9 → Bool := fun j => decide (j ≠ v)
      have yes : ∀ r : Fin 9, f (fun j => decide (j ≠ r)) = true := by decide +kernel
      have wrong := correctMask x
      rw [yes v] at wrong
      change g.op.eval (g.inputs.map (value x)) = true at wrong
      rw [isAnd] at wrong
      change (g.inputs.map (value x)).all id = true at wrong
      have no := (List.all_eq_true.mp wrong) _ (List.mem_map.mpr ⟨v.val,reads,rfl⟩)
      rw [atV] at no
      have notThere : x v = false := by simp [x]
      rw [notThere] at no
      cases no
    · let x : Fin 9 → Bool := fun j => decide (j = v)
      have no : ∀ r : Fin 9, f (fun j => decide (j = r)) = false := by decide +kernel
      have yes : mask x = true := by
        change g.op.eval (g.inputs.map (value x)) = true
        rw [isOr]
        change (g.inputs.map (value x)).any id = true
        have active : value x v.val = true := by rw [atV]; simp [x]
        exact List.any_eq_true.mpr ⟨true,List.mem_map.mpr ⟨v.val,reads,active⟩,rfl⟩
      exact Bool.noConfusion (yes.symm.trans ((correctMask x).trans (no v)))
    cases pinList : g.inputs with
    | nil => rw [pinList] at reads; cases reads
    | cons first remaining =>
      have formula (x : Fin 9 → Bool) : mask x = !(value x first) := by
        change g.op.eval (g.inputs.map (value x)) = _
        rw [isNot,pinList]
        rfl
      by_cases use : first = v.val
      · let x : Fin 9 → Bool := fun _ => true
        have yes : f x = true := rfl
        have wrong := correctMask x
        rw [formula,use,atV,yes] at wrong
        exact Bool.noConfusion wrong
      have entire : ∀ h ∈ C.gates, v.val ∉ h.inputs := by
        have len : C.gates.length = 13 := full
        have h := avoids
        rw [qEq,show 23-10 = 13 by rfl,List.take_of_length_le (by omega : C.gates.length ≤ 13)] at h
        exact h
      have runSet (ls : List Gate) (r : List Bool) (b : Bool) (safe : ∀ h ∈ ls, v.val ∉ h.inputs)
          (inside : v.val < r.length) : run ls (r.set v.val b) = (run ls r).set v.val b := by
        induction ls generalizing r with
        | nil => rfl
        | cons h ls ih =>
          have equal : h.inputs.map (fun i => (r.set v.val b).getD i false) =
              h.inputs.map (fun i => r.getD i false) := by
            apply List.map_congr_left
            intro i hm
            have ne : i ≠ v.val := by intro eq; exact safe h List.mem_cons_self (eq ▸ hm)
            rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm ne)]
          let val := h.op.eval (h.inputs.map fun i => r.getD i false)
          change run ls ((r.set v.val b) ++ [h.op.eval _]) = (run ls (r ++ [val])).set v.val b
          rw [equal,← List.set_append_left _ _ inside]
          apply ih _ (fun j hj => safe j (List.mem_cons_of_mem _ hj))
          simp
          omega
      let mate : Fin 9 → Fin 9 := ![1,0,1,2,3,0,1,2,3]
      let low (r : Fin 9) (i : Fin 9) := decide (i = mate r)
      let high (r : Fin 9) (i : Fin 9) := decide (i = mate r ∨ i = r)
      have probes : ∀ r : Fin 9, r ≠ 0 → r ≠ 6 →
          row (high r) = (row (low r)).set r.val true ∧ f (low r) = false ∧ f (high r) = true := by
        decide +kernel
      obtain ⟨linked,lowNo,highYes⟩ := probes v v0 v6
      have same : value (high v) first = value (low v) first := by
        change (if first < q then (run C.gates (row (high v))).getD first false else false) =
          (if first < q then (run C.gates (row (low v))).getD first false else false)
        by_cases inside : first < q
        · rw [if_pos inside,if_pos inside,linked,runSet _ _ _ entire (within _),
            List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm use)]
        · rw [if_neg inside,if_neg inside]
      have impossible := (correctMask (high v)).symm.trans ((formula (high v)).trans
        ((congrArg (fun b : Bool => !b) same).trans ((formula (low v)).symm.trans (correctMask (low v)))))
      rw [highYes,lowNo] at impossible
      cases impossible
  have outputForm : q ≤ 22 ∧ C.output = 22 := endCases.resolve_right notRaw
  let inv (h : Gate) := h.op.eval [false,false]
  have partition (ls : List Gate) : (ls.filter fun h => !inv h).length + (ls.filter inv).length = ls.length := by
    induction ls with
    | nil => rfl
    | cons g ls ih => cases yes : inv g <;> simp [yes] <;> omega
  have few : (C.gates.filter inv).length + (if inv g then 1 else 0) ≤ 2 := by
    have many := costs.2
    change 13 ≤ (D.gates.filter fun h => !inv h).length at many
    have book := partition D.gates
    change (D.gates.filter fun h => !inv h).length + (D.gates.filter inv).length = D.size at book
    have same : (D.gates.filter inv).length = (C.gates.filter inv).length + (if inv g then 1 else 0) := profile
    rw [same,dsize] at book
    omega
  have noRaw (p r : Fin 9) (different : p ≠ r) :
      g ≠ ⟨.and,[p.val,r.val]⟩ ∧ (p ≠ v → r ≠ v → (Gate.mk .and [p.val,r.val]) ∉ C.gates) := by
    have banned : (Gate.mk .and [p.val,r.val]) ∉ D.gates := by
      intro yes
      have tooBig := rawBound D legal correct p r different yes
      omega
    refine ⟨?_,?_⟩
    · intro equal
      apply banned
      rw [← equal]
      exact there
    · intro hp hr yes
      apply banned
      apply preserves _ yes
      intro i hi
      change i ∈ [p.val,r.val] at hi
      rcases (show i = p.val ∨ i = r.val from by simpa using hi) with rfl | rfl
      · exact ⟨p.isLt,fun e => hp (Fin.val_injective e)⟩
      · exact ⟨r.isLt,fun e => hr (Fin.val_injective e)⟩
  obtain ⟨x,counter⟩ := search v C q g v0 v6 fan full base outputForm.1 outputForm.2 mode arity reads avoids few noRaw
  apply counter
  have agrees := not_not.mp (all x)
  simp only [f,target,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] at agrees ⊢
  exact agrees
