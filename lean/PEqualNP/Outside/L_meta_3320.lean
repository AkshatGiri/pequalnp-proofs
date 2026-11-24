import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3320_aux

-- Starting at wire 5, the six initial gates compute the edges of a double star.
-- The other four gates add one edge while both signals feeding the cut remain live.
private def C : Circuit := ⟨[
  ⟨.or,[0,1]⟩, ⟨.or,[2,3]⟩, ⟨.and,[5,6]⟩, ⟨.and,[7,0]⟩, ⟨.and,[7,2]⟩,
  ⟨.or,[8,9]⟩, ⟨.or,[6,1]⟩, ⟨.and,[5,4]⟩, ⟨.or,[12,10]⟩, ⟨.and,[11,13]⟩],14⟩

private abbrev E (p : Fin 2) (l : Fin 3) : Prop :=
  (p = 0 ∧ l ≠ 2) ∨ (p = 1 ∧ (l = 0 ∨ l = 2))


private abbrev goal (x : Fin 5 → Bool) : Prop :=
  ∃ (p : Fin 2) (l : Fin 3), E p l ∧ x (Fin.castAdd 3 p) = true ∧ x (Fin.natAdd 2 l) = true


private def gate (k : Fin 10) : Gate := C.gates.getD k.val ⟨.and,[]⟩

private theorem exact_function : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = true ↔ goal x := by
  decide +kernel

private theorem noFour : ∀ (p p' : Fin 2) (l l' : Fin 3), p ≠ p' → l ≠ l' →
    E p l → E p l' → E p' l → ¬ E p' l' := by
  intro p p' l l'
  fin_cases p <;> fin_cases p' <;> fin_cases l <;> fin_cases l' <;> unfold E <;> decide +kernel

private theorem gate_in_C (k : ℕ) (g : Gate) (atGate : C.gates[k]? = some g) :
    ∃ t : Fin 10, t.val = k ∧ g = gate t := by
  have small : k < 10 := by
    by_contra! outside
    have none : C.gates[k]? = none := List.getElem?_eq_none (by exact outside)
    rw [none] at atGate
    cases atGate
  refine ⟨⟨k,small⟩,rfl,?_⟩
  unfold gate
  rw [List.getD_eq_getElem?_getD,atGate]
  rfl

private theorem topo (k : ℕ) (g : Gate) (hg : C.gates[k]? = some g) :
    (g.op = .and ∨ g.op = .or) ∧ ∃ u v : ℕ, g.inputs = [u,v] ∧ u ≠ v ∧ u < 5+k ∧ v < 5+k := by
  obtain ⟨t,rfl,rfl⟩ := gate_in_C k g hg
  fin_cases t <;> first
  | (refine ⟨Or.inl rfl,_,_,rfl,by decide,by decide,by decide⟩)
  | (refine ⟨Or.inr rfl,_,_,rfl,by decide,by decide,by decide⟩)

private def copy (k : Fin 10) (p : Fin 2) : Gate :=
  ⟨.and,[(gate k).inputs.getD p.val 0]⟩

private def absorb (k : Fin 10) : Gate :=
  if (gate k).op.eval [false,true] then ⟨.and,[]⟩ else ⟨.or,[]⟩

private theorem copy_breaks : ∀ (k : Fin 10) (pin : Fin 2), ∃ x : Fin 5 → Bool,
    ¬ ((Circuit.mk (C.gates.set k.val (copy k pin)) 14).eval (List.ofFn x) = true ↔ goal x) := by
  decide +kernel

private theorem absorb_breaks : ∀ k : Fin 10, ∃ x : Fin 5 → Bool,
    ¬ ((Circuit.mk (C.gates.set k.val (absorb k)) 14).eval (List.ofFn x) = true ↔ goal x) := by
  decide +kernel

private theorem rigid (k u v : ℕ) (g g' : Gate) (hg : C.gates[k]? = some g)
    (pins : g.inputs = [u,v])
    (replace : g' = ⟨.and,[u]⟩ ∨ g' = ⟨.and,[v]⟩ ∨
      (g.op = .and ∧ g' = ⟨.or,[]⟩) ∨ (g.op = .or ∧ g' = ⟨.and,[]⟩)) :
    ¬ ∀ x : Fin 5 → Bool, (Circuit.mk (C.gates.set k g') 14).eval (List.ofFn x) = true ↔ goal x := by
  obtain ⟨i,rfl,rfl⟩ := gate_in_C k g hg
  have copyLeft : copy i 0 = ⟨.and,[u]⟩ := by simp [copy,pins]
  have copyRight : copy i 1 = ⟨.and,[v]⟩ := by simp [copy,pins]
  intro correct
  rcases replace with same | same | ⟨kind,same⟩ | ⟨kind,same⟩
  · have eq := same.trans copyLeft.symm
    obtain ⟨x,bad⟩ := copy_breaks i 0
    have yes := correct x
    rw [eq] at yes
    exact bad yes
  · have eq := same.trans copyRight.symm
    obtain ⟨x,bad⟩ := copy_breaks i 1
    have yes := correct x
    rw [eq] at yes
    exact bad yes
  · have eq : g' = absorb i := by rw [same]; simp [absorb,kind,GateOp.eval]
    obtain ⟨x,bad⟩ := absorb_breaks i
    have yes := correct x
    rw [eq] at yes
    exact bad yes
  · have eq : g' = absorb i := by rw [same]; simp [absorb,kind,GateOp.eval]
    obtain ⟨x,bad⟩ := absorb_breaks i
    have yes := correct x
    rw [eq] at yes
    exact bad yes

private theorem onehots : ∀ i : Fin 5,
    (C.wires (List.ofFn (fun t : Fin 5 => decide (t = i)))).getD 7 false = false := by
  decide +kernel

private theorem nonedge_accepted : ∃ x : Fin 5 → Bool,
    (C.wires (List.ofFn x)).getD 7 false = true ∧ ¬ goal x := by
  refine ⟨fun t => decide (t = 1 ∨ t = 3),?_⟩
  decide +kernel

private theorem only_and_readers : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → 7 ∈ g.inputs → g.op = .and := by
  intro k g hg member
  obtain ⟨i,rfl,rfl⟩ := gate_in_C k g hg
  fin_cases i <;> simp [gate,C] at member ⊢

private def Readers : Set ℕ := { k | ∃ g : Gate, C.gates[k]? = some g ∧ 7 ∈ g.inputs }
private def AndReaders : Set ℕ := { k | ∃ g : Gate, C.gates[k]? = some g ∧ g.op = .and ∧ 7 ∈ g.inputs }

private theorem reader_card : Readers.ncard = 2 := by
  have eq : Readers = {3,4} := by
    ext k
    constructor
    · rintro ⟨g,hg,mem⟩
      obtain ⟨i,rfl,rfl⟩ := gate_in_C k g hg
      fin_cases i <;> simp [gate,C] at mem ⊢
    · intro member
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at member
      rcases member with rfl | rfl
      · exact ⟨⟨.and,[7,0]⟩,rfl,by simp⟩
      · exact ⟨⟨.and,[7,2]⟩,rfl,by simp⟩
  rw [eq,Set.ncard_pair (by decide)]

private theorem and_reader_card : AndReaders.ncard = 2 := by
  have eq : AndReaders = Readers := by
    ext k
    constructor
    · rintro ⟨g,hg,_,hm⟩
      exact ⟨g,hg,hm⟩
    · rintro ⟨g,hg,hm⟩
      exact ⟨g,hg,only_and_readers k g hg hm,hm⟩
  rw [eq,reader_card]

private def C0 : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op,g.inputs.map (fun i => if i = 7 then 15 else i)⟩),14⟩

private def Z (i : ℕ) : Prop := ∀ x : Fin 5 → Bool, (C0.wires (List.ofFn x)).getD i false = false

private def step (u v : ℕ) : Prop :=
  ∃ (k : ℕ) (g : Gate), C0.gates[k]? = some g ∧ u ∈ g.inputs ∧ v = 5+k ∧ ¬ Z v

private def Live : Set ℕ := { k | ∃ g : Gate, C0.gates[k]? = some g ∧
  (∀ i ∈ g.inputs, ¬ Z i) ∧ Relation.ReflTransGen step (5+k) C0.output }

private def Lost : Set (Fin 2 × Fin 3) := { e | E e.1 e.2 ∧
  C0.eval (List.ofFn (fun t : Fin 5 => decide (t = Fin.castAdd 3 e.1) ||
    decide (t = Fin.natAdd 2 e.2))) = false }

private theorem not_zero (i : ℕ) (cert : (C0.wires (List.ofFn (fun _ : Fin 5 => true))).getD i false = true) : ¬ Z i := by
  intro allZero
  have impossible := allZero (fun _ => true)
  rw [cert] at impossible
  cases impossible

private theorem live_card : 5 ≤ Live.ncard := by
  have h0 : ¬ Z 0 := not_zero 0 rfl
  have h1 : ¬ Z 1 := not_zero 1 rfl
  have h2 : ¬ Z 2 := not_zero 2 rfl
  have h3 : ¬ Z 3 := not_zero 3 rfl
  have h4 : ¬ Z 4 := not_zero 4 rfl
  have h5 : ¬ Z 5 := not_zero 5 rfl
  have h6 : ¬ Z 6 := not_zero 6 rfl
  have h11 : ¬ Z 11 := not_zero 11 rfl
  have h12 : ¬ Z 12 := not_zero 12 rfl
  have h13 : ¬ Z 13 := not_zero 13 rfl
  have h14 : ¬ Z 14 := not_zero 14 rfl
  have s5 : step 5 12 := ⟨7,⟨.and,[5,4]⟩,rfl,by simp,rfl,h12⟩
  have s6 : step 6 11 := ⟨6,⟨.or,[6,1]⟩,rfl,by simp,rfl,h11⟩
  have s11 : step 11 14 := ⟨9,⟨.and,[11,13]⟩,rfl,by simp,rfl,h14⟩
  have s12 : step 12 13 := ⟨8,⟨.or,[12,10]⟩,rfl,by simp,rfl,h13⟩
  have s13 : step 13 14 := ⟨9,⟨.and,[11,13]⟩,rfl,by simp,rfl,h14⟩
  have r12 := Relation.ReflTransGen.head s12 (Relation.ReflTransGen.single s13)
  have r6 := Relation.ReflTransGen.head s6 (Relation.ReflTransGen.single s11)
  let witnesses : Finset ℕ := {0,1,6,7,9}
  have included : (witnesses : Set ℕ) ⊆ Live := by
    intro k hk
    have which : k = 0 ∨ k = 1 ∨ k = 6 ∨ k = 7 ∨ k = 9 := by simpa [witnesses] using hk
    rcases which with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨.or,[0,1]⟩,rfl,by simpa using And.intro h0 h1,Relation.ReflTransGen.head s5 r12⟩
    · exact ⟨⟨.or,[2,3]⟩,rfl,by simpa using And.intro h2 h3,r6⟩
    · exact ⟨⟨.or,[6,1]⟩,rfl,by simpa using And.intro h6 h1,Relation.ReflTransGen.single s11⟩
    · exact ⟨⟨.and,[5,4]⟩,rfl,by simpa using And.intro h5 h4,r12⟩
    · exact ⟨⟨.and,[11,13]⟩,rfl,by simpa using And.intro h11 h13,Relation.ReflTransGen.refl⟩
  have finite : Live.Finite := by
    apply (Finset.range 10).finite_toSet.subset
    rintro k ⟨g,hg,_,_⟩
    apply Finset.mem_range.mpr
    by_contra! outside
    have none : C0.gates[k]? = none := List.getElem?_eq_none (by exact outside)
    rw [none] at hg
    cases hg
  have bound := Set.ncard_le_ncard included finite
  rw [Set.ncard_coe_finset] at bound
  exact bound

private theorem lost01 : (0,1) ∈ Lost := by
  change E 0 1 ∧ _ = false
  exact ⟨Or.inl ⟨rfl,by decide⟩,rfl⟩

private theorem lost10 : (1,0) ∈ Lost := by
  change E 1 0 ∧ _ = false
  exact ⟨Or.inr ⟨rfl,Or.inl rfl⟩,rfl⟩

private theorem loss_card : 3 ≤ Lost.ncard := by
  let witnesses : Finset (Fin 2 × Fin 3) := {(0,0),(0,1),(1,0)}
  have included : (witnesses : Set (Fin 2 × Fin 3)) ⊆ Lost := by
    intro e he
    have sep : e = (0,0) ∨ e = (0,1) ∨ e = (1,0) := by simpa [witnesses] using he
    rcases sep with rfl | rfl | rfl
    · change E 0 0 ∧ _ = false
      exact ⟨Or.inl ⟨rfl,by decide⟩,rfl⟩
    · exact lost01
    · exact lost10
  have h := Set.ncard_le_ncard included
  rw [Set.ncard_coe_finset] at h
  exact h

private theorem two_members {α : Type} [DecidableEq α] (K : Finset α) (x y : α) (hx : x ∈ K) (hy : y ∈ K) (different : x ≠ y) :
    2 ≤ K.card := by
  have subset : ({x,y} : Finset α) ⊆ K := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · obtain rfl := Finset.mem_singleton.mp hz
      exact hy
  have h := Finset.card_le_card subset
  rwa [Finset.card_pair different] at h

private theorem cover_card (K : Finset (Fin 2 ⊕ Fin 3))
    (covers : ∀ p l, (p,l) ∈ Lost → Sum.inl p ∈ K ∨ Sum.inr l ∈ K) : 2 ≤ K.card := by
  rcases covers 0 1 lost01 with a | a <;> rcases covers 1 0 lost10 with b | b <;>
    exact two_members K _ _ a b (by decide)

end PEqualNP.Outside.L_meta_3320_aux

open PEqualNP.Outside.L_meta_3320_aux

theorem PEqualNP.Outside.L_meta_3320 :
¬ (∀ (a b : ℕ) (E : Fin a → Fin b → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), (∀ (p p' : Fin a) (l l' : Fin b), p ≠ p' → l ≠ l' → E p l → E p l' → E p' l → ¬ E p' l') → (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ u v : ℕ, g.inputs = [u, v] ∧ u ≠ v ∧ u < a + b + k ∧ v < a + b + k) → C.output + 1 = a + b + C.size → (∀ x : Fin (a + b) → Bool, C.eval (List.ofFn x) = true ↔ ∃ (p : Fin a) (l : Fin b), E p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true) → (∀ (k u v : ℕ) (g g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → g.inputs = [u, v] → (g' = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [u] } ∨ g' = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [v] } ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g' = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g' = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] })) → ¬ ∀ x : Fin (a + b) → Bool, (({ gates := C.gates.set k g', output := C.output } : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = true ↔ ∃ (p : Fin a) (l : Fin b), E p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true)) → j < C.size → (∀ i : Fin (a + b), (C.wires (List.ofFn (fun t0 : Fin (a + b) => decide (t0 = i)))).getD (a + b + j) false = false) → (∃ x : Fin (a + b) → Bool, (C.wires (List.ofFn x)).getD (a + b + j) false = true ∧ ¬ ∃ (p : Fin a) (l : Fin b), E p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true) → 2 ≤ {k : ℕ | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[k]? = some g ∧ a + b + j ∈ g.inputs}.ncard → (¬ ∃ (k k' w : ℕ) (g g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (g.inputs = [a + b + j, w] ∨ g.inputs = [w, a + b + j]) ∧ (∀ x : Fin (a + b) → Bool, (C.wires (List.ofFn x)).getD w false = true → ∃ (p : Fin a) (l : Fin b), E p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true) ∧ C.gates[k']? = some g' ∧ g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ a + b + k ∈ g'.inputs) → ∀ C0 : PEqualNP.CircuitLowerBounds.Circuit, C0 = { gates := C.gates.map (fun h0 : PEqualNP.CircuitLowerBounds.Gate => ({ op := h0.op, inputs := h0.inputs.map (fun s0 : ℕ => if s0 = a + b + j then a + b + C.size else s0) } : PEqualNP.CircuitLowerBounds.Gate)), output := C.output } → ∀ Z : ℕ → Prop, (∀ i : ℕ, Z i ↔ ∀ x : Fin (a + b) → Bool, (C0.wires (List.ofFn x)).getD i false = false) → ∃ K : Finset (Fin a ⊕ Fin b), (∀ (p : Fin a) (l : Fin b), E p l → C0.eval (List.ofFn (fun t1 : Fin (a + b) => decide (t1 = Fin.castAdd b p) || decide (t1 = Fin.natAdd a l))) = false → Sum.inl p ∈ K ∨ Sum.inr l ∈ K) ∧ {k : ℕ | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C0.gates[k]? = some g ∧ (∀ s1 ∈ g.inputs, ¬ Z s1) ∧ Relation.ReflTransGen (fun y z : ℕ => ∃ (k1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C0.gates[k1]? = some g1 ∧ y ∈ g1.inputs ∧ z = a + b + k1 ∧ ¬ Z z) (a + b + k) C0.output}.ncard + {e : Fin a × Fin b | E e.1 e.2 ∧ C0.eval (List.ofFn (fun t2 : Fin (a + b) => decide (t2 = Fin.castAdd b e.1) || decide (t2 = Fin.natAdd a e.2))) = false}.ncard + K.card + {k : ℕ | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[k]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ a + b + j ∈ g.inputs}.ncard ≤ C.size + 1) := by
  intro proposed
  have readers : 2 ≤ Readers.ncard := by rw [reader_card]
  have result := proposed 2 3 E C 2 noFour topo rfl exact_function rigid (by decide) onehots nonedge_accepted readers
    (by
      rintro ⟨k,_,w,g,_,atGate,yes,input,_,_,_,_⟩
      have member : 7 ∈ g.inputs := by rcases input with h | h <;> simp [h]
      exact GateOp.noConfusion (yes.symm.trans (only_and_readers k g atGate member)))
    C0 rfl Z (fun _ => Iff.rfl)
  obtain ⟨K,covers,bound⟩ := result
  change Live.ncard + Lost.ncard + K.card + AndReaders.ncard ≤ C.size + 1 at bound
  have Csz : C.size = 10 := rfl
  have cover := cover_card K (by intro p l h; exact covers p l h.1 h.2)
  rw [and_reader_card,Csz] at bound
  have live := live_card
  have loss := loss_card
  omega
