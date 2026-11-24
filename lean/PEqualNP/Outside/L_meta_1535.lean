import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.ByContra
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1535

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (Monotone2)
open scoped BigOperators

-- Adapted from the wire evaluation lemmas used in the low-merge inequality.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]; simp [hl]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem fold_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (gs.foldl step w).getD i false = false := by
  rw [List.getD_eq_default]; rw [fold_length]; exact h


def rd (C : Circuit) (x : List Bool) (g i : ℕ) : Bool :=
  if i < g then (C.wires x).getD i false else false

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false := fold_getD_lt _ _ _ h

theorem wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  set A := (C.gates.take j).foldl step x with hA
  have hAl : A.length = x.length + j := by
    rw [hA, fold_length]; simp; omega
  have hw : C.wires x = (C.gates.drop (j + 1)).foldl step (step A C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hreadA : ∀ i, A.getD i false = rd C x (x.length + j) i := by
    intro i
    unfold rd
    by_cases hi : i < x.length + j
    · rw [ite_eq_left hi, hw, fold_getD_lt _ (step A C.gates[j]) i (by simp [step]; omega), step,
        List.getD_append _ _ _ _ (by omega)]
    · rw [ite_eq_right hi, List.getD_eq_default]; omega
  rw [hw, fold_getD_lt _ _ _ (by simp [step]; omega), step,
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hAl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  exact List.map_congr_left (fun i _ => hreadA i)




def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi

theorem wires_mono (C : Circuit) (hC : IsMonotoneCircuit C) (a b : List Bool)
    (hl : a.length = b.length) (h : LeL a b) : LeL (C.wires a) (C.wires b) :=
  fold_mono C.gates hC a b hl h

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

variable {n : ℕ}

def point (u : Fin n) : Fin n → Bool := fun v => decide (v = u)

def alive (C : Circuit) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => value C (point u) r = true

def Contained (C : Circuit) (S : Finset (Fin n)) (r : ℕ) : Prop :=
  ∀ u, value C (point u) r = true → u ∈ S

theorem contained_iff (C : Circuit) (S : Finset (Fin n)) (r : ℕ) :
    Contained C S r ↔ alive C r ⊆ S := by
  simp only [Contained, Finset.subset_iff, alive, Finset.mem_filter, Finset.mem_univ, true_and]

def Core (C : Circuit) (S : Finset (Fin n)) (o k : ℕ) : Prop :=
  ∀ K : Set ℕ,
    (∀ a : ℕ, a < C.gates.length → o = n + a → Contained C S (n + a) → a ∈ K) →
    (∀ a ∈ K, ∀ (g : Gate) (b : ℕ), C.gates[a]? = some g →
      n + b ∈ g.inputs → b < a → Contained C S (n + b) → b ∈ K) →
    k ∈ K

theorem core_root (C : Circuit) (S : Finset (Fin n)) (o k : ℕ) (hk : k < C.gates.length)
    (ho : o = n + k) (hS : Contained C S (n + k)) : Core C S o k :=
  fun _ hroot _ => hroot k hk ho hS

theorem core_child (C : Circuit) (S : Finset (Fin n)) (o a b : ℕ) (g : Gate)
    (ha : Core C S o a) (hg : C.gates[a]? = some g) (hin : n + b ∈ g.inputs)
    (hba : b < a) (hS : Contained C S (n + b)) : Core C S o b :=
  fun K hr hc => hc a (ha K hr hc) g b hg hin hba hS

def GoodWire (C : Circuit) (S : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool) (r : ℕ) : Prop :=
  value C y r = false ∧ Contained C S r ∧ (n ≤ r → Core C S o (r - n))

def HitsExternal (C : Circuit) (S : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool) : Prop :=
  ∀ r, (∃ (a : ℕ) (g : Gate), Core C S o a ∧ C.gates[a]? = some g ∧
    g.op = .and ∧ r ∈ g.inputs ∧ r < n + a ∧ ¬ Contained C S r) →
    ∃ u, value C (point u) r = true ∧ y u = true

theorem value_mono (C : Circuit) (hm : IsMonotoneCircuit C) (x y : Fin n → Bool)
    (hxy : ∀ u, x u = true → y u = true) :
    ∀ r, value C x r = true → value C y r = true := by
  have h : LeL (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases hlt : i < n
    · have hxi : (List.ofFn x).getD i false = x ⟨i, hlt⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn]
      have hyi : (List.ofFn y).getD i false = y ⟨i, hlt⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn]
      rw [hyi]
      exact hxy ⟨i, hlt⟩ (hxi ▸ hi)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt)] at hi
      contradiction
  exact wires_mono C hm (List.ofFn x) (List.ofFn y) (by simp) h

theorem value_input (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < n) :
    value C x r = x ⟨r, hr⟩ := by
  unfold value
  have hl : r < (List.ofFn x).length := by simpa using hr
  rw [wires_input C _ r hl, List.getD_eq_getElem _ _ hl, List.getElem_ofFn]

theorem value_missing (C : Circuit) (x : Fin n → Bool) (r : ℕ)
    (hr : n + C.gates.length ≤ r) : value C x r = false := by
  unfold value
  apply List.getD_eq_default
  rw [wires_length, List.length_ofFn]
  exact hr

theorem alive_input (C : Circuit) (r : ℕ) (hr : r < n) :
    (alive (n := n) C r).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have hva := (Finset.mem_filter.mp ha).2
  have hvb := (Finset.mem_filter.mp hb).2
  rw [value_input C _ r hr] at hva hvb
  exact (of_decide_eq_true hva).symm.trans (of_decide_eq_true hvb)

def readWire (C : Circuit) (x : Fin n → Bool) (r i : ℕ) : Bool :=
  if i < r then value C x i else false

theorem value_gate (C : Circuit) (x : Fin n → Bool) (a : ℕ) (ha : a < C.gates.length) :
    value C x (n + a) = C.gates[a].op.eval (C.gates[a].inputs.map (fun r => readWire C x (n + a) r)) := by
  simpa only [value, rd, readWire, List.length_ofFn] using wires_gate C (List.ofFn x) a ha

theorem good_child (C : Circuit) (S : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool)
    (a r : ℕ) (g : Gate) (hg : C.gates[a]? = some g) (hin : r ∈ g.inputs)
    (hr : r < n + a) (hcurrent : GoodWire C S o y (n + a)) (hlow : value C y r = false)
    (hcon : Contained C S r) : GoodWire C S o y r := by
  refine ⟨hlow, hcon, fun hn => ?_⟩
  have heq : n + (r - n) = r := by omega
  exact core_child C S o a (r - n) g
    (by simpa only [Nat.add_sub_cancel_left] using hcurrent.2.2 (by omega))
    hg (heq.symm ▸ hin) (by omega) (heq.symm ▸ hcon)

theorem descend (C : Circuit) (S : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool)
    (hm : Monotone2 C) (hX : HitsExternal C S o y) (a : ℕ) (ha : a < C.gates.length)
    (hcurrent : GoodWire C S o y (n + a)) (hlarge : 2 ≤ (alive (n := n) C (n + a)).card) :
    ∃ W : Finset ℕ, W.card ≤ 2 ∧ (∀ r ∈ W, r < n + a ∧ GoodWire C S o y r) ∧
      alive (n := n) C (n + a) ⊆ W.biUnion (alive (n := n) C) := by
  classical
  let g := C.gates[a]
  have hg : C.gates[a]? = some g := List.getElem?_eq_getElem ha
  obtain ⟨hop, hfanin⟩ := hm g (List.getElem_mem ha)
  have hval (x : Fin n → Bool) : value C x (n + a) = g.op.eval (g.inputs.map (readWire C x (n + a))) :=
    value_gate C x a ha
  obtain ⟨hlow, hcon, hcore⟩ := hcurrent
  rcases hop with hAnd | hOr
  · have hf : ∃ r ∈ g.inputs, readWire C y (n + a) r = false := by
      rw [hval, hAnd] at hlow
      simp only [GateOp.eval, List.all_eq_false, List.mem_map, id] at hlow
      obtain ⟨v, ⟨r, hr, rfl⟩, hv⟩ := hlow
      exact ⟨r, hr, Bool.eq_false_of_not_eq_true hv⟩
    obtain ⟨r, hr, hfalse⟩ := hf
    have himp (u : Fin n) (hu : value C (point u) (n + a) = true) :
        readWire C (point u) (n + a) r = true := by
      rw [hval, hAnd] at hu
      exact List.all_eq_true.mp hu _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
    have hlt : r < n + a := by
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (alive (n := n) C (n + a)).card)
      have h := himp u (Finset.mem_filter.mp hu).2
      by_contra hra
      simp [readWire, hra] at h
    have hlr : value C y r = false := by simpa only [readWire, ite_eq_left hlt] using hfalse
    have hcr : Contained C S r := by
      by_contra hn
      obtain ⟨u, hu, hy⟩ := hX r ⟨a, g,
        by simpa only [Nat.add_sub_cancel_left] using hcore (by omega), hg, hAnd, hr, hlt, hn⟩
      have ht := value_mono C (fun g hg => (hm g hg).1) (point u) y (fun v hv => (of_decide_eq_true hv).symm ▸ hy) r hu
      rw [hlr] at ht
      contradiction
    refine ⟨{r}, by simp, ?_, ?_⟩
    · intro i hi
      have he := Finset.mem_singleton.mp hi
      subst i
      exact ⟨hlt, good_child C S o y a r g hg hr hlt ⟨hlow, hcon, hcore⟩ hlr hcr⟩
    · intro u hu
      apply Finset.mem_biUnion.mpr
      refine ⟨r, by simp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      simpa only [readWire, ite_eq_left hlt] using himp u (Finset.mem_filter.mp hu).2
  · let W := g.inputs.toFinset.filter (fun r => r < n + a)
    have or_intro (x : Fin n → Bool) (r : ℕ) (hr : r ∈ g.inputs) (hlt : r < n + a)
        (ht : value C x r = true) : value C x (n + a) = true := by
      rw [hval, hOr]
      exact List.any_eq_true.mpr ⟨readWire C x (n + a) r, List.mem_map.mpr ⟨r, hr, rfl⟩,
        by simpa only [id, readWire, ite_eq_left hlt] using ht⟩
    have hW : W.card ≤ 2 :=
      (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hfanin)
    refine ⟨W, hW, ?_, ?_⟩
    · intro r hr
      obtain ⟨hread, hlt⟩ := Finset.mem_filter.mp hr
      have hinput := List.mem_toFinset.mp hread
      have hlr : value C y r = false := by
        apply Bool.eq_false_of_not_eq_true
        intro ht
        exact Bool.false_ne_true (hlow ▸ or_intro y r hinput hlt ht)
      have hcr : Contained C S r := fun u hu => hcon u (or_intro (point u) r hinput hlt hu)
      exact ⟨hlt, good_child C S o y a r g hg hinput hlt ⟨hlow, hcon, hcore⟩ hlr hcr⟩
    · intro u hu
      have h := (Finset.mem_filter.mp hu).2
      rw [hval, hOr] at h
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at h
      obtain ⟨v, ⟨r, hr, rfl⟩, hv⟩ := h
      have hlt : r < n + a := by
        by_contra hn
        simp [readWire, hn] at hv
      exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hlt⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [readWire, ite_eq_left hlt] using hv⟩⟩

noncomputable def pool (C : Circuit) (S : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun a =>
    GoodWire C S o y (n + a) ∧ 2 ≤ (alive (n := n) C (n + a)).card

theorem range_count (C : Circuit) (S : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool)
    (hm : Monotone2 C) (hX : HitsExternal C S o y) :
    ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ,
      (∀ r ∈ W, r < n + k ∧ GoodWire C S o y r) →
      (W.biUnion (alive (n := n) C)).card ≤ W.card +
        (pool C S o y ∩ Finset.range k).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro _ W hW
    have hc := Finset.card_biUnion_le_card_mul W (alive (n := n) C) 1
      (fun r hr => alive_input C r (by simpa using (hW r hr).1))
    simpa using hc
  | succ k ih =>
    intro hk W hW
    let r := n + k
    let U := W.erase r
    have hsub (w : ℕ) (hw : w ∈ U) : w < n + k ∧ GoodWire C S o y w := by
      obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
      obtain ⟨hlt, hgood⟩ := hW w hw
      dsimp [r] at hne
      exact ⟨by omega, hgood⟩
    have hcharge : (pool C S o y ∩ Finset.range k).card ≤
        (pool C S o y ∩ Finset.range (k + 1)).card :=
      Finset.card_le_card fun i hi =>
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1, Finset.mem_range.mpr
          (Nat.lt_succ_of_lt (Finset.mem_range.mp (Finset.mem_inter.mp hi).2))⟩
    by_cases hr : r ∈ W
    swap
    · have hU : U = W := Finset.erase_eq_of_notMem hr
      exact (ih (by omega) W (hU ▸ hsub)).trans (Nat.add_le_add_left hcharge _)
    have hUC : U.card + 1 = W.card := by
      rw [show W = insert r U from (Finset.insert_erase hr).symm]
      exact (Finset.card_insert_of_notMem (Finset.notMem_erase _ _)).symm
    have hUW : W = insert r U := (Finset.insert_erase hr).symm
    by_cases hl : (alive (n := n) C r).card ≤ 1
    · have hsum := ih (by omega) U hsub
      calc
        (W.biUnion (alive (n := n) C)).card =
            (alive (n := n) C r ∪ U.biUnion (alive (n := n) C)).card := by
          rw [hUW, Finset.biUnion_insert]
        _ ≤ (alive (n := n) C r).card + (U.biUnion (alive (n := n) C)).card :=
          Finset.card_union_le _ _
        _ ≤ _ := by omega
    · change ¬ (alive (n := n) C (n + k)).card ≤ 1 at hl
      have hlarge : 2 ≤ (alive (n := n) C (n + k)).card := by omega
      have hg := (hW r hr).2
      have hp : k ∈ pool C S o y :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hg, hlarge⟩
      have hcount : (pool C S o y ∩ Finset.range (k + 1)).card =
          (pool C S o y ∩ Finset.range k).card + 1 := by
        have heq : pool C S o y ∩ Finset.range (k + 1) =
            insert k (pool C S o y ∩ Finset.range k) := by
          ext i
          by_cases he : i = k
          · subst i; simp [hp]
          · simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_insert, he, false_or]
            constructor <;> intro h <;> exact ⟨h.1, by omega⟩
        rw [heq, Finset.card_insert_of_notMem (by simp)]
      obtain ⟨A, hA, ha, haCover⟩ := descend C S o y hm hX k (by omega) hg hlarge
      let V := U ∪ A
      have hV (i : ℕ) (hi : i ∈ V) : i < n + k ∧ GoodWire C S o y i := by
        rcases Finset.mem_union.mp hi with hu | hA
        · exact hsub i hu
        · exact ha i hA
      have hcV := Finset.card_union_le U A
      have hc := ih (by omega) V hV
      have hs : W.biUnion (alive (n := n) C) ⊆ V.biUnion (alive (n := n) C) := by
        intro u hu
        obtain ⟨i, hi, hu⟩ := Finset.mem_biUnion.mp hu
        rw [hUW] at hi
        rcases Finset.mem_insert.mp hi with he | hi
        · subst i
          obtain ⟨j, hj, hjU⟩ := Finset.mem_biUnion.mp (haCover hu)
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_union_right _ hj, hjU⟩
        · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_union_left _ hi, hu⟩
      have he := Finset.card_le_card hs
      change V.card ≤ U.card + A.card at hcV
      omega

theorem one_output (C : Circuit) (S : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool)
    (hm : Monotone2 C) (hS : ∀ u, value C (point u) o = true ↔ u ∈ S)
    (hzero : value C y o = false) (hX : HitsExternal C S o y) :
    S.card ≤ (pool C S o y).card + (if S.Nonempty then 1 else 0) := by
  classical
  by_cases hne : S.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  have hsup : alive C o = S := by
    ext u
    simpa only [alive, Finset.mem_filter, Finset.mem_univ, true_and] using hS u
  have ho : o < n + C.gates.length := by
    obtain ⟨u, hu⟩ := hne
    by_contra! hn
    have hfalse := value_missing C (point u) o hn
    have hh := (hS u).mpr hu
    rw [hfalse] at hh
    contradiction
  have hcont : Contained C S o := fun u hu => (hS u).mp hu
  have hg : GoodWire C S o y o := by
    refine ⟨hzero, hcont, fun hn => ?_⟩
    have he : o = n + (o - n) := by omega
    exact core_root C S o (o - n) (by omega) he (he ▸ hcont)
  have hW (w : ℕ) (hw : w ∈ ({o} : Finset ℕ)) : w < n + C.gates.length ∧ GoodWire C S o y w := by
    have he := Finset.mem_singleton.mp hw
    subst w
    exact ⟨ho, hg⟩
  have hCount := range_count C S o y hm hX C.gates.length le_rfl {o} hW
  have hp : pool C S o y ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
  simpa only [Finset.singleton_biUnion, Finset.card_singleton, hsup,
    Finset.inter_eq_left.mpr hp, ite_eq_left hne, Nat.add_comm] using hCount

end PEqualNP.Outside.L_meta_1535

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1535
open scoped BigOperators

theorem PEqualNP.Outside.L_meta_1535 :
∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ ak : ℕ, ak < gates.length → (Finset.univ.filter (fun au : Fin n => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun auk : Fin n => decide (auk = au)))).getD (n + ak) false = true)).card ≤ 1 → ∀ ax : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn ax)).getD (n + ak) false = decide (∃ av : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun avk : Fin n => decide (avk = av)))).getD (n + ak) false = true ∧ ax av = true)) → (∀ (w : Fin m) (u : Fin n), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun uk : Fin n => decide (uk = u)))).getD (out w) false = true ↔ u ∈ S w) → (∀ w0 : Fin m, ∃ y : Fin n → Bool, (∀ u3 ∈ S w0, y u3 = false) ∧ (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn y)).getD (out w0) false = false ∧ ∀ bw : ℕ, (∃ (bk : ℕ) (bg : PEqualNP.CircuitLowerBounds.Gate), (∀ bK : Set ℕ, (∀ bk0 : ℕ, bk0 < gates.length → out w0 = n + bk0 → (∀ bu0 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu0k : Fin n => decide (bu0k = bu0)))).getD (n + bk0) false = true → bu0 ∈ S w0) → bk0 ∈ bK) → (∀ bk1 ∈ bK, ∀ (bg1 : PEqualNP.CircuitLowerBounds.Gate) (bk2 : ℕ), gates[bk1]? = some bg1 → n + bk2 ∈ bg1.inputs → bk2 < bk1 → (∀ bu1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu1k : Fin n => decide (bu1k = bu1)))).getD (n + bk2) false = true → bu1 ∈ S w0) → bk2 ∈ bK) → bk ∈ bK) ∧ gates[bk]? = some bg ∧ bg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ bw ∈ bg.inputs ∧ bw < n + bk ∧ ¬ (∀ bu2 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu2k : Fin n => decide (bu2k = bu2)))).getD (bw) false = true → bu2 ∈ S w0)) → ∃ u4 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u4k : Fin n => decide (u4k = u4)))).getD (bw) false = true ∧ y u4 = true) → ∑ w1 : Fin m, (S w1).card ≤ gates.length + (Finset.univ.filter (fun w5 : Fin m => (S w5).Nonempty)).card
 := by
  classical
  intro n m S gates out hthin hm _hnorm hsingle hex
  let C : Circuit := ⟨gates, 0⟩
  have hx (w : Fin m) : ∃ y : Fin n → Bool, value C y (out w) = false ∧ HitsExternal C (S w) (out w) y := by
    obtain ⟨y, _, h0, hhit⟩ := hex w
    exact ⟨y, h0, hhit⟩
  choose y hy using hx
  let paid (w : Fin m) : Finset ℕ := pool C (S w) (out w) (y w)
  have hb (w : Fin m) : (S w).card ≤ (paid w).card + (if (S w).Nonempty then 1 else 0) :=
    one_output C (S w) (out w) (y w) hm (hsingle w) (hy w).1 (hy w).2
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint paid := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro k hi hj
    obtain ⟨_, hi, hlarge⟩ := Finset.mem_filter.mp hi
    obtain ⟨_, hj, _⟩ := Finset.mem_filter.mp hj
    have hi' := (contained_iff C (S i) (n + k)).mp hi.2.1
    have hj' := (contained_iff C (S j) (n + k)).mp hj.2.1
    have hsub : alive (n := n) C (n + k) ⊆ S i ∩ S j :=
      fun u hu => Finset.mem_inter.mpr ⟨hi' hu, hj' hu⟩
    have hz := (Finset.card_le_card hsub).trans (hthin i j hij)
    omega
  have hpool : (∑ w : Fin m, (paid w).card) ≤ gates.length := by
    rw [← Finset.card_biUnion hd]
    exact (Finset.card_le_card (t := Finset.range gates.length) (by
      intro k hk
      obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hk
      exact (Finset.mem_filter.mp hw).1)).trans (by simp)
  have hones : (∑ w : Fin m, if (S w).Nonempty then (1 : ℕ) else 0) =
      (Finset.univ.filter (fun w : Fin m => (S w).Nonempty)).card := by
    rw [← Finset.sum_filter]
    simp
  calc
    _ ≤ ∑ w : Fin m, ((paid w).card + if (S w).Nonempty then 1 else 0) :=
      Finset.sum_le_sum (fun w _ => hb w)
    _ ≤ _ := by rw [Finset.sum_add_distrib, hones]; omega
