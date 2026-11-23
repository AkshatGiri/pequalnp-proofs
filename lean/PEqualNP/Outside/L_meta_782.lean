import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds Relation

-- The list evaluation lemmas generalize the wire evaluation argument from L-meta-718.
private def appendValue {α : Type*} (run : GateOp → List α → α) (d : α)
    (w : List α) (g : Gate) : List α :=
  w ++ [run g.op (g.inputs.map fun i => w.getD i d)]

private def evaluateList {α : Type*} (run : GateOp → List α → α) (d : α)
    (gs : List Gate) (w : List α) : List α := gs.foldl (appendValue run d) w

private def wire {α : Type*} (run : GateOp → List α → α) (d : α)
    (C : Circuit) (w : List α) (i : ℕ) : α :=
  (evaluateList run d C.gates w).getD i d

-- The fold recurrence also applies to the lists of syntactic line degrees.
private theorem evaluate_prefix {α : Type*} (run : GateOp → List α → α) (d : α)
    (gs : List Gate) (w : List α) :
    ∃ s : List α, evaluateList run d gs w = w ++ s ∧ s.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [evaluateList], rfl⟩
  | cons g rest ih =>
    obtain ⟨s, he, hl⟩ := ih (appendValue run d w g)
    refine ⟨run g.op (g.inputs.map fun i => w.getD i d) :: s, ?_, by simp [hl]⟩
    change evaluateList run d rest (appendValue run d w g) = _
    rw [he]
    simp [appendValue]

private theorem evaluate_length {α : Type*} (run : GateOp → List α → α) (d : α)
    (gs : List Gate) (w : List α) : (evaluateList run d gs w).length = w.length + gs.length := by
  obtain ⟨extra, h, hl⟩ := evaluate_prefix run d gs w
  rw [h]
  simp [hl]

private theorem evaluate_get_prefix {α : Type*} (run : GateOp → List α → α) (d : α)
    (gs : List Gate) (w : List α) (i : ℕ) (hi : i < w.length) :
    (evaluateList run d gs w).getD i d = w.getD i d := by
  obtain ⟨extra, h, _⟩ := evaluate_prefix run d gs w
  rw [h, List.getD_append _ _ _ _ hi]

private theorem wire_gate {α : Type*} (run : GateOp → List α → α) (d : α)
    (C : Circuit) (w : List α) {j : ℕ} {g : Gate} (hg : C.gates[j]? = some g) :
    wire run d C w (w.length + j) = run g.op (g.inputs.map
      (fun i => if i < w.length + j then wire run d C w i else d)) := by
  obtain ⟨hj, heq⟩ := List.getElem?_eq_some_iff.mp hg
  have split : C.gates = (C.gates.take j ++ [g]) ++ C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) C.gates]
    rw [List.take_succ_eq_append_getElem hj, heq]
  let before := evaluateList run d (C.gates.take j) w
  have hlen : before.length = w.length + j := by
    simp [before, evaluate_length, List.length_take, Nat.min_eq_left hj.le]
  have hread (i : ℕ) : before.getD i d =
      (if i < w.length + j then wire run d C w i else d) := by
    by_cases hi : i < w.length + j
    · rw [ite_eq_left hi]
      unfold wire evaluateList
      conv_rhs => rw [split, List.append_assoc, List.foldl_append]
      exact (evaluate_get_prefix run d (g :: C.gates.drop (j + 1)) before i (hlen.symm ▸ hi)).symm
    · rw [ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have hm : (g.inputs.map fun i => before.getD i d) = g.inputs.map
      (fun i => if i < w.length + j then wire run d C w i else d) :=
    List.map_congr_left fun i _ => hread i
  unfold wire evaluateList
  conv_lhs => rw [split, List.append_assoc, List.foldl_append]
  change (evaluateList run d (C.gates.drop (j + 1))
    (before ++ [run g.op (g.inputs.map fun i => before.getD i d)])).getD (w.length + j) d = _
  rw [evaluate_get_prefix _ _ _ _ _ (by simp [hlen]), ← hlen, hm]
  simp [hlen, wire, evaluateList]

private theorem wire_at {α : Type*} (run : GateOp → List α → α) (d : α)
    (C : Circuit) (w : List α) (j : Fin C.gates.length) :
    wire run d C w (w.length + j.val) = run (C.gates.get j).op ((C.gates.get j).inputs.map
      (fun i => if i < w.length + j.val then wire run d C w i else d)) :=
  wire_gate run d C w (List.getElem?_eq_some_iff.mpr ⟨j.isLt, rfl⟩)

private theorem wire_missing {α : Type*} (run : GateOp → List α → α) (d : α) (C : Circuit)
    (w : List α) {i : ℕ} (h : w.length + C.gates.length ≤ i) : wire run d C w i = d := by
  apply List.getD_eq_default
  rwa [evaluate_length]

private theorem monotone_gate_value (op : GateOp) (ops : op = GateOp.and ∨ op = GateOp.or)
    (inputs : List ℕ) (f g : ℕ → Bool) (agree : ∀ i ∈ inputs, f i = true → g i = true)
    (trueOnF : op.eval (inputs.map f) = true) : op.eval (inputs.map g) = true := by
  rcases ops with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at trueOnF ⊢
    rintro _ ⟨i, hi, rfl⟩
    exact agree i hi (trueOnF (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at trueOnF ⊢
    obtain ⟨_, ⟨i, hi, rfl⟩, he⟩ := trueOnF
    exact ⟨g i, ⟨i, hi, rfl⟩, agree i hi he⟩

private def hot {n : ℕ} (i : Fin n) (j : Fin n) : Bool := decide (j = i)

private theorem getD_ofFn_at {α : Type*} {n : ℕ} (x : Fin n → α) (d : α) (i : Fin n) :
    (List.ofFn x).getD i.val d = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  wire GateOp.eval false C (List.ofFn x) w

private def inputValue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (dst w : ℕ) : Bool :=
  if w < dst then value C x w else false

private theorem value_at {n : ℕ} (C : Circuit) (x : Fin n → Bool) {j : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) : value C x (n + j) = g.op.eval (g.inputs.map (inputValue C x (n + j))) := by
  dsimp only [value, inputValue]
  have h := wire_gate GateOp.eval false C (List.ofFn x) hg
  rw [List.length_ofFn] at h
  exact h

private theorem value_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : Fin n) :
    value C x w.val = x w := by
  unfold value wire
  rw [evaluate_get_prefix _ _ _ _ _ (by simp)]
  exact getD_ofFn_at x false w

private def hits (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => value C (hot p) w = true

private theorem mem_hits {n : ℕ} {C : Circuit} {w : ℕ} {p : Fin n} :
    p ∈ hits n C w ↔ value C (hot p) w = true := by simp [hits]

private theorem hits_input (n : ℕ) (C : Circuit) (i : Fin n) : hits n C i.val = {i} := by
  ext p
  simp [hits, value_input, hot, eq_comm]

private theorem hits_missing (n : ℕ) (C : Circuit) (i : ℕ) (h : n + C.size ≤ i) : hits n C i = ∅ := by
  ext p
  rw [mem_hits]
  have h' : (List.ofFn (hot p)).length + C.gates.length ≤ i := by simpa [Circuit.size] using h
  simp [value, wire_missing _ _ C _ h']

private def owned (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (j : ℕ) : Prop :=
  j < C.size ∧ hits n C (n + j) ⊆ S ∧ 2 ≤ (hits n C (n + j)).card

private def nextOwned (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (a b : ℕ) : Prop :=
  owned n C S a ∧ owned n C S b ∧ a < b ∧
    ∃ g, C.gates[b]? = some g ∧ n + a ∈ g.inputs

private noncomputable def closure (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun j => owned n C S j ∧ ReflTransGen (nextOwned n C S) j r

private theorem mem_closure {n : ℕ} {C : Circuit} {S : Finset (Fin n)} {r j : ℕ} :
    j ∈ closure n C S r ↔ owned n C S j ∧ ReflTransGen (nextOwned n C S) j r := by
  classical
  unfold closure
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩

private theorem closure_parent {n : ℕ} {C : Circuit} {S : Finset (Fin n)} {r j : ℕ}
    (h : j ∈ closure n C S r) (hne : j ≠ r) :
    ∃ u ∈ closure n C S r, j < u ∧ ∃ g, C.gates[u]? = some g ∧ n + j ∈ g.inputs := by
  rcases (mem_closure.mp h).2.cases_head with same | ⟨u, edge, path⟩
  · exact (hne same).elim
  · exact ⟨u, mem_closure.mpr ⟨edge.2.1, path⟩, edge.2.2.1, edge.2.2.2⟩

private theorem closure_child {n : ℕ} {C : Circuit} {S : Finset (Fin n)} {r j a : ℕ} {g : Gate}
    (h : j ∈ closure n C S r) (hg : C.gates[j]? = some g) (ha : a < j)
    (read : n + a ∈ g.inputs) (hOwned : owned n C S a) : a ∈ closure n C S r := by
  obtain ⟨hj, hpath⟩ := mem_closure.mp h
  exact mem_closure.mpr ⟨hOwned, (ReflTransGen.single ⟨hOwned, hj, ha, g, hg, read⟩).trans hpath⟩

private def label (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (Q : Finset ℕ) (w : ℕ) : Bool :=
  if n ≤ w ∧ w - n ∈ Q then
    let g := C.gates[w - n]?.getD ⟨GateOp.or, []⟩
    g.op.eval (g.inputs.map fun a => if _h : a < w then label n C S Q a else false)
  else decide (¬ hits n C w ⊆ S)
termination_by w

private theorem label_gate {n : ℕ} {C : Circuit} {S : Finset (Fin n)} {Q : Finset ℕ} {j : ℕ}
    (hj : j ∈ Q) {g : Gate} (hg : C.gates[j]? = some g) :
    label n C S Q (n + j) = g.op.eval (g.inputs.map fun a =>
      if a < n + j then label n C S Q a else false) := by
  rw [label]
  simp [hj, hg]

private def outside (n : ℕ) (Q : Finset ℕ) (w : ℕ) : Prop := ∀ j ∈ Q, w ≠ n + j

private theorem label_outside {n : ℕ} {C : Circuit} {S : Finset (Fin n)} {Q : Finset ℕ} {w : ℕ}
    (h : outside n Q w) : label n C S Q w = true ↔ ¬ hits n C w ⊆ S := by
  have h' : ¬ (n ≤ w ∧ w - n ∈ Q) := by
    rintro ⟨hl, hr⟩
    exact h (w - n) hr (by omega)
  rw [label, ite_eq_right h']
  simp

private def references (C : Circuit) (Q : Finset ℕ) : Finset ℕ :=
  Q.biUnion fun j => (C.gates[j]?.getD ⟨GateOp.or, []⟩).inputs.toFinset

private theorem references_le (C : Circuit) (Q : Finset ℕ)
    (fan : ∀ g ∈ C.gates, g.inputs.length = 2) : (references C Q).card ≤ 2 * Q.card := by
  classical
  unfold references
  refine Finset.card_biUnion_le.trans ?_
  calc
    _ ≤ ∑ _ ∈ Q, 2 := by
      apply Finset.sum_le_sum
      intro j _
      cases hg : C.gates[j]? with
      | none => simp
      | some g =>
        have hw : g ∈ C.gates := List.mem_of_getElem? hg
        simp only [Option.getD_some]
        have le := List.toFinset_card_le g.inputs
        exact le.trans (fan g hw).le
    _ = _ := by simp [Nat.mul_comm]

private theorem mem_references {C : Circuit} {Q : Finset ℕ} {j w : ℕ} {g : Gate}
    (hj : j ∈ Q) (hg : C.gates[j]? = some g) (hw : w ∈ g.inputs) : w ∈ references C Q := by
  exact Finset.mem_biUnion.mpr ⟨j, hj, by simp [hg, hw]⟩

private noncomputable def exits (n : ℕ) (C : Circuit) (Q : Finset ℕ) : Finset ℕ := by
  classical
  exact (references C Q).filter (outside n Q)

private theorem mem_exits {n : ℕ} {C : Circuit} {Q : Finset ℕ} {w : ℕ} :
    w ∈ exits n C Q ↔ w ∈ references C Q ∧ outside n Q w := by
  classical
  simp [exits]

private theorem exits_le {n : ℕ} {C : Circuit} {S : Finset (Fin n)} {r : ℕ}
    (hr : owned n C S r) (fan : ∀ g ∈ C.gates, g.inputs.length = 2) :
    (exits n C (closure n C S r)).card ≤ (closure n C S r).card + 1 := by
  classical
  let Q := closure n C S r
  have hRoot : r ∈ Q := mem_closure.mpr ⟨hr, ReflTransGen.refl⟩
  let inside := (Q.erase r).image (fun j => n + j)
  have hInside : inside ⊆ references C Q := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨parent, hp, _, g, hg, hread⟩ := closure_parent (Finset.mem_erase.mp hj).2
      (Finset.mem_erase.mp hj).1
    exact mem_references hp hg hread
  have houtside : exits n C Q ⊆ references C Q := fun _ h => (mem_exits.mp h).1
  have hDisjoint : Disjoint inside (exits n C Q) := by
    apply Finset.disjoint_left.mpr
    intro a hInside hOutside
    obtain ⟨j, hj, hj'⟩ := Finset.mem_image.mp hInside
    exact (mem_exits.mp hOutside).2 j (Finset.mem_erase.mp hj).2 hj'.symm
  have hInsideCard : inside.card = Q.card - 1 := by
    change ((Q.erase r).image (fun j => n + j)).card = _
    rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_erase_of_mem hRoot]
  have hTotal := (Finset.card_le_card (Finset.union_subset hInside houtside)).trans
    (references_le C Q fan)
  rw [Finset.card_union_of_disjoint hDisjoint, hInsideCard] at hTotal
  change (exits n C Q).card ≤ Q.card + 1
  omega

private theorem value_mono {n : ℕ} (C : Circuit) (mono : ∀ g ∈ C.gates,
    g.op = GateOp.and ∨ g.op = GateOp.or) (x y : Fin n → Bool)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) (hx : value C x w = true) :
    value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases before : w < n
    · let p : Fin n := ⟨w, before⟩
      change value C x p.val = true at hx
      change value C y p.val = true
      rw [value_input] at hx ⊢
      exact hxy p hx
    by_cases within : w < n + C.gates.length
    · let j : Fin C.gates.length := ⟨w - n, by omega⟩
      have hidx : w = n + j.val := by simp [j]; omega
      have hg : C.gates[j.val]? = some (C.gates.get j) := List.getElem?_eq_some_iff.mpr ⟨j.isLt, rfl⟩
      rw [hidx, value_at C x hg] at hx
      rw [hidx, value_at C y hg]
      apply monotone_gate_value _ (mono _ (List.get_mem _ _)) _ _ _ ?_ hx
      intro a _ ha
      by_cases h : a < n + j.val
      · simp only [inputValue, ite_eq_left h] at ha ⊢
        exact ih a (hidx ▸ h) ha
      · simp [inputValue, h] at ha
    · have h := wire_missing GateOp.eval false C (List.ofFn x) (by simp; omega :
          (List.ofFn x).length + C.gates.length ≤ w)
      change value C x w = false at h
      rw [h] at hx
      cases hx

private def promised {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (k r : ℕ) : Prop :=
  ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ k →
    (∀ p ∈ S, x p = false) → value C x (n + r) = false

private theorem count_when_true {n k r : ℕ} {C : Circuit} {S : Finset (Fin n)}
    (valid : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hr : owned n C S r) (promise : promised C S k r)
    (rootTrue : label n C S (closure n C S r) (n + r) = true) :
    k ≤ (closure n C S r).card := by
  classical
  let Q := closure n C S r
  let chosenExits := (exits n C Q).filter fun w => label n C S Q w = true
  have hWitness (w : chosenExits) : ∃ p ∈ hits n C w.val, p ∉ S := by
    obtain ⟨hExit, hTrue⟩ := Finset.mem_filter.mp w.property
    exact Finset.not_subset.mp ((label_outside (C := C) (S := S) (mem_exits.mp hExit).2).mp hTrue)
  choose witness hit off using hWitness
  let support := chosenExits.attach.image witness
  have cardBound : support.card ≤ Q.card + 1 := by
    have ha : support.card ≤ chosenExits.card := by
      simpa [support] using (Finset.card_image_le (s := chosenExits.attach) (f := witness))
    exact ha.trans ((Finset.card_filter_le _ _).trans (exits_le hr (fun g h => (valid g h).2)))
  by_contra! tooFew
  change Q.card < k at tooFew
  let x : Fin n → Bool := fun p => decide (p ∈ support)
  have small : (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ k := by
    have eq : (Finset.univ.filter (fun p : Fin n => x p = true)) = support := by
      ext p
      simp [x]
    rw [eq]
    omega
  have misses (p : Fin n) (hp : p ∈ S) : x p = false := by
    apply decide_eq_false
    rintro h
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h
    exact off w hp
  have mono := fun g h => (valid g h).1
  have atGate (j : ℕ) (hj : j ∈ Q) (hl : label n C S Q (n + j) = true) : value C x (n + j) = true := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      have bound := (mem_closure.mp hj).1.1
      let g := C.gates[j]'bound
      have hg : C.gates[j]? = some g := List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
      rw [value_at C x hg]
      rw [label_gate hj hg] at hl
      apply monotone_gate_value _ (mono _ (List.mem_of_getElem? hg)) _ _ _ ?_ hl
      intro a ha hTrue
      by_cases earlier : a < n + j
      · simp only [ite_eq_left earlier] at hTrue
        simp only [inputValue, ite_eq_left earlier]
        by_cases outer : outside n Q a
        · let exit : chosenExits := ⟨a, Finset.mem_filter.mpr
              ⟨mem_exits.mpr ⟨mem_references hj hg ha, outer⟩, hTrue⟩⟩
          have accepted := mem_hits.mp (hit exit)
          apply value_mono C mono (hot (witness exit)) x ?_ a accepted
          intro p hp
          have e : p = witness exit := by simpa [hot] using hp
          subst p
          have hx : witness exit ∈ support := Finset.mem_image.mpr ⟨exit, Finset.mem_attach .., rfl⟩
          simp [x, hx]
        · unfold outside at outer
          push Not at outer
          obtain ⟨b, hb, hab⟩ := outer
          subst a
          exact ih b (by omega) hb hTrue
      · simp [earlier] at hTrue
  have root := atGate r (mem_closure.mpr ⟨hr, ReflTransGen.refl⟩) rootTrue
  rw [promise x small misses] at root
  cases root

private theorem different_gate_input (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (inputs : List ℕ) (f g : ℕ → Bool) (hF : op.eval (inputs.map f) = true)
    (hG : op.eval (inputs.map g) = false) :
    ∃ a ∈ inputs, f a = true ∧ g a = false := by
  classical
  by_contra no
  have good (a : ℕ) (ha : a ∈ inputs) (hf : f a = true) : g a = true := by
    cases h : g a
    · exact (no ⟨a, ha, hf, h⟩).elim
    · rfl
  have ht := monotone_gate_value op hop inputs f g good hF
  rw [hG] at ht
  cases ht

private theorem trace_when_false {n r : ℕ} {C : Circuit} {S : Finset (Fin n)}
    (valid : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (p : Fin n) (j : ℕ) (hj : j ∈ closure n C S r) (trueAtP : value C (hot p) (n + j) = true)
    (falseLabel : label n C S (closure n C S r) (n + j) = false) :
    ∃ a ∈ exits n C (closure n C S r), p ∈ hits n C a ∧ (hits n C a).card ≤ 1 := by
  classical
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have bound := (mem_closure.mp hj).1.1
    let g := C.gates[j]'bound
    have hg : C.gates[j]? = some g := List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
    rw [value_at C (hot p) hg] at trueAtP
    rw [label_gate hj hg] at falseLabel
    obtain ⟨a, ha, hit, bit⟩ := different_gate_input _ (valid _ (List.mem_of_getElem? hg)).1
      _ _ _ trueAtP falseLabel
    have before : a < n + j := by
      by_contra he
      simp [inputValue, he] at hit
    simp only [inputValue, ite_eq_left before] at hit
    rw [ite_eq_left before] at bit
    by_cases outer : outside n (closure n C S r) a
    · have edge := mem_references hj hg ha
      refine ⟨a, mem_exits.mpr ⟨edge, outer⟩, mem_hits.mpr hit, ?_⟩
      by_cases input : a < n
      · let i : Fin n := ⟨a, input⟩
        change (hits n C i.val).card ≤ 1
        simp [hits_input]
      by_contra! many
      have contained : hits n C a ⊆ S := by
        by_contra h
        have e := (label_outside (C := C) (S := S) outer).mpr h
        rw [bit] at e
        cases e
      have eq : a = n + (a - n) := by omega
      have smaller : a - n < j := by omega
      have own : owned n C S (a - n) := ⟨by omega, eq ▸ contained, eq ▸ many⟩
      have smallInside := closure_child hj hg smaller (eq ▸ ha) own
      exact outer _ smallInside eq
    · unfold outside at outer
      push Not at outer
      obtain ⟨b, hb, rfl⟩ := outer
      exact ih b (by omega) hb hit bit

private theorem count_when_false {n r : ℕ} {C : Circuit} {S : Finset (Fin n)}
    (valid : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hr : owned n C S r) (rootFalse : label n C S (closure n C S r) (n + r) = false) :
    (hits n C (n + r)).card ≤ (closure n C S r).card + 1 := by
  classical
  let R := hits n C (n + r)
  let Q := closure n C S r
  have hRoot : r ∈ Q := mem_closure.mpr ⟨hr, ReflTransGen.refl⟩
  have route (p : R) : ∃ a ∈ exits n C Q, p.val ∈ hits n C a ∧ (hits n C a).card ≤ 1 :=
    trace_when_false valid p.val r hRoot (mem_hits.mp p.property) rootFalse
  choose f hf hHit hSmall using route
  let embed : R → exits n C Q := fun p => ⟨f p, hf p⟩
  have injective : Function.Injective embed := by
    intro a b h
    apply Subtype.ext
    have he : f a = f b := congrArg Subtype.val h
    exact Finset.card_le_one.mp (hSmall a) a.val (hHit a) b.val (he.symm ▸ hHit b)
  have hcard : R.card ≤ (exits n C Q).card := by
    simpa using Fintype.card_le_of_injective embed injective
  exact hcard.trans (exits_le hr (fun g hg => (valid g hg).2))

private theorem one_output {n k o c : ℕ} (C : Circuit) (S : Finset (Fin n))
    (valid : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hTwo : 2 ≤ (hits n C o).card) (contained : hits n C o ⊆ S)
    (promise : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ k →
      (∀ p ∈ S, x p = false) → value C x o = false)
    (hk : c ≤ k) (hc : c + 1 ≤ (hits n C o).card) :
    ∃ Q : Finset ℕ, c ≤ Q.card ∧ ∀ j ∈ Q, owned n C S j := by
  have hLow : n ≤ o := by
    by_contra! h
    let i : Fin n := ⟨o, h⟩
    have he := hits_input n C i
    change hits n C o = {i} at he
    rw [he, Finset.card_singleton] at hTwo
    omega
  have hHigh : o < n + C.size := by
    by_contra! h
    rw [hits_missing n C o h, Finset.card_empty] at hTwo
    omega
  let r := o - n
  have eq : o = n + r := by dsimp [r]; omega
  have hrValid : r < C.size := by omega
  rw [eq] at hTwo contained hc promise
  have hr : owned n C S r := ⟨hrValid, contained, hTwo⟩
  let Q := closure n C S r
  refine ⟨Q, ?_, fun j hj => (mem_closure.mp hj).1⟩
  cases e : label n C S Q (n + r)
  · have h := count_when_false valid hr e
    change (hits n C (n + r)).card ≤ Q.card + 1 at h
    omega
  · exact hk.trans (count_when_true valid hr promise e)

end PEqualNP.Outside.L_meta_782

open PEqualNP.Outside.L_meta_782 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c inter atLeastTwo gateTypes inside onSmall belowK belowCard
  have byOutput (i : Fin m) : ∃ Q : Finset ℕ, c i ≤ Q.card ∧ ∀ j ∈ Q, owned n C (S i) j := by
    refine one_output C (S i) gateTypes (atLeastTwo i) ?_ (onSmall i) (belowK i) (belowCard i)
    intro p hp
    exact inside i p (mem_hits.mp hp)
  choose Q hCard hOwned using byOutput
  have disjoint : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint Q := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro a hi hj
    have ia := hOwned i a hi
    have ja := hOwned j a hj
    have subset : hits n C (n + a) ⊆ S i ∩ S j :=
      fun p hp => Finset.mem_inter.mpr ⟨ia.2.1 hp, ja.2.1 hp⟩
    have bound := (Finset.card_le_card subset).trans (inter i j hij)
    have hTwo := ia.2.2
    omega
  have hUnion : (Finset.univ.biUnion Q) ⊆ Finset.range C.size := by
    intro a ha
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_range.mpr (hOwned i a hi).1
  calc
    ∑ i, c i ≤ ∑ i, (Q i).card := Finset.sum_le_sum (fun i _ => hCard i)
    _ = (Finset.univ.biUnion Q).card := (Finset.card_biUnion disjoint).symm
    _ ≤ C.size := by simpa using Finset.card_le_card hUnion
