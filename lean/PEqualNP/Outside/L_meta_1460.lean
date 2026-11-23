import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1460

open PEqualNP.CircuitLowerBounds

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

def outside {n : ℕ} (S : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∉ S)

def query {n : ℕ} (R : Fin n → Finset (Fin n)) (p v : Fin n) : Bool := decide (v ∈ R p)

def Low {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  value C (outside S) w = false

def active {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (R : Fin n → Finset (Fin n)) (w : ℕ) :
    Finset (Fin n) := S.filter fun p => value C (query R p) w = true

theorem active_mem {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (R : Fin n → Finset (Fin n))
    (w : ℕ) (p : Fin n) : p ∈ active C S R w ↔ p ∈ S ∧ value C (query R p) w = true :=
  Finset.mem_filter

def Paid {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (R : Fin n → Finset (Fin n)) (w : ℕ) : Prop :=
  Low C S w ∧ 2 ≤ (active C S R w).card ∧ ∃ g : Fin C.gates.length,
    w = n + g.val ∧ (C.gates.get g).op = GateOp.or ∧ (C.gates.get g).inputs.length = 2 ∧
      ∀ r ∈ (C.gates.get g).inputs, (active C S R r).Nonempty

noncomputable def paidWires {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.gates.length)).filter (Paid C S R)

theorem paid_mem {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (R : Fin n → Finset (Fin n))
    (w : ℕ) : w ∈ paidWires C S R ↔ Paid C S R w := by
  classical
  unfold paidWires
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨_, _, g, rfl, _, _, _⟩ := h
  have := g.isLt
  omega

theorem value_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p.val = x p := by
  unfold value
  have hp : p.val < (List.ofFn x).length := by simp
  rw [wires_input _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

theorem value_mono {n : ℕ} (C : Circuit) (hC : IsMonotoneCircuit C) (x y : Fin n → Bool)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  apply wires_mono C hC _ _ (by simp)
  intro i hi
  by_cases hn : i < n
  · have hnx : i < (List.ofFn x).length := by simp [hn]
    have hny : i < (List.ofFn y).length := by simp [hn]
    rw [List.getD_eq_getElem _ _ hnx] at hi
    rw [List.getD_eq_getElem _ _ hny]
    simpa using hxy ⟨i, hn⟩ (by simpa using hi)
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction

theorem active_before_gate {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (R : Fin n → Finset (Fin n))
    (hR : ∀ p ∈ S, R p ∩ S = {p}) {w : ℕ} (hw : w < n) (hlow : Low C S w) :
    (active C S R w).card ≤ 1 := by
  let v : Fin n := ⟨w, hw⟩
  have hv : v ∈ S := by
    change value C (outside S) v.val = false at hlow
    rw [value_input] at hlow
    simpa [outside] using hlow
  apply Finset.card_le_one.mpr
  intro p hp r hr
  have eq (a : Fin n) (ha : a ∈ active C S R w) : v = a := by
    obtain ⟨haS, hav⟩ := (active_mem C S R w a).mp ha
    change value C (query R a) v.val = true at hav
    rw [value_input] at hav
    have he : v ∈ R a ∩ S := Finset.mem_inter.mpr ⟨of_decide_eq_true hav, hv⟩
    rwa [hR a haS, Finset.mem_singleton] at he
  exact (eq p hp).symm.trans (eq r hr)

theorem expand_active {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (R : Fin n → Finset (Fin n))
    (hR : ∀ p ∈ S, R p ∩ S = {p})
    (hbasis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hlow : Low C S w) (hcard : 2 ≤ (active C S R w).card) :
    ∃ P : Finset ℕ, (∀ r ∈ P, r < w ∧ Low C S r) ∧
      active C S R w ⊆ P.biUnion (active C S R) ∧
      (P.card ≤ 1 ∨ P.card ≤ 2 ∧ Paid C S R w) := by
  classical
  let base := outside S
  let test := query R
  let A := active C S R
  have hex : (A w).Nonempty := Finset.card_pos.mp (by change 0 < (active C S R w).card; omega)
  have hw₁ : n ≤ w := by
    by_contra! hn
    have := active_before_gate C S R hR hn hlow
    omega
  have hw₂ : w < n + C.gates.length := by
    by_contra! hn
    obtain ⟨p, hp⟩ := hex
    have ha := (active_mem C S R w p).mp hp |>.2
    change (C.gates.foldl step (List.ofFn (test p))).getD w false = true at ha
    rw [fold_getD_ge _ _ _ (by simpa using hn)] at ha
    contradiction
  let j : Fin C.gates.length := ⟨w - n, by omega⟩
  have hw : n + j.val = w := by dsimp [j]; omega
  let g := C.gates.get j
  obtain ⟨hop, hlen⟩ := hbasis g (List.get_mem _ _)
  let read (x : Fin n → Bool) (r : ℕ) := if r < w then value C x r else false
  have hg (x : Fin n → Bool) : value C x w = g.op.eval (g.inputs.map (read x)) := by
    have h := wires_gate C (List.ofFn x) j.val j.isLt
    simpa [List.length_ofFn, hw, read, rd, value, g] using h
  have one (a : ℕ) (ha : read base a = false) (ht : ∀ p ∈ A w, read (test p) a = true) :
      ∃ P : Finset ℕ, (∀ r ∈ P, r < w ∧ Low C S r) ∧ A w ⊆ P.biUnion A ∧
        (P.card ≤ 1 ∨ P.card ≤ 2 ∧ Paid C S R w) := by
    have hlt : a < w := by
      obtain ⟨p, hp⟩ := hex
      by_contra hn
      simpa [read, hn] using ht p hp
    refine ⟨{a}, ?_, ?_, Or.inl (by simp)⟩
    · intro r hr
      obtain rfl := Finset.mem_singleton.mp hr
      exact ⟨hlt, by simpa [read, hlt, Low, base] using ha⟩
    · intro p hp
      apply Finset.mem_biUnion.mpr
      exact ⟨a, Finset.mem_singleton_self _, (active_mem C S R a p).2
        ⟨((active_mem C S R w p).mp hp).1, by simpa [read, hlt] using ht p hp⟩⟩
  have ha (p : Fin n) (hp : p ∈ A w) := ((active_mem C S R w p).mp hp).2
  have hb : g.op.eval (g.inputs.map (read base)) = false := (hg base).symm.trans hlow
  cases hs : g.inputs with
  | nil =>
    rcases hop with hop | hop
    · simp [hop, hs, GateOp.eval] at hb
    · obtain ⟨p, hp⟩ := hex
      have ht := (hg (test p)).symm.trans (ha p hp)
      simp [hop, hs, GateOp.eval] at ht
  | cons a tail =>
    cases tail with
    | nil =>
      apply one a
      · rcases hop with hop | hop <;> simpa [hop, hs, GateOp.eval] using hb
      · intro p hp
        have ht := (hg (test p)).symm.trans (ha p hp)
        rcases hop with hop | hop <;> simpa [hop, hs, GateOp.eval] using ht
    | cons b tail =>
      have he : tail = [] := by
        have hl := (hbasis g (List.get_mem _ _)).2
        rw [hs] at hl
        simp only [List.length_cons] at hl
        exact List.length_eq_zero_iff.mp (by omega)
      subst tail
      rcases hop with hop | hop
      · have hbase : read base a = false ∨ read base b = false := by
          cases ha' : read base a with
          | false => exact Or.inl rfl
          | true => exact Or.inr (by simpa [hs, hop, GateOp.eval, ha'] using hb)
        have htest (p : Fin n) (hp : p ∈ A w) :
            read (test p) a = true ∧ read (test p) b = true := by
          simpa [hs, hop, GateOp.eval, Bool.and_eq_true] using (hg (test p)).symm.trans (ha p hp)
        exact hbase.elim (fun h => one a h (fun p hp => (htest p hp).1))
          (fun h => one b h (fun p hp => (htest p hp).2))
      · have hbase : read base a = false ∧ read base b = false := by
          simpa [hs, hop, GateOp.eval, Bool.or_eq_false_iff] using hb
        have htest (p : Fin n) (hp : p ∈ A w) :
            read (test p) a = true ∨ read (test p) b = true := by
          simpa [hs, hop, GateOp.eval, Bool.or_eq_true] using (hg (test p)).symm.trans (ha p hp)
        by_cases hA : ∃ p ∈ A w, read (test p) a = true
        · by_cases hB : ∃ p ∈ A w, read (test p) b = true
          · obtain ⟨u, hu, htu⟩ := hA
            obtain ⟨v, hv, htv⟩ := hB
            have hlt (r : ℕ) (p : Fin n) (hp : read (test p) r = true) : r < w := by
              by_contra hn
              simp [read, hn] at hp
            have hla := hlt a u htu
            have hlb := hlt b v htv
            have hmem (r : ℕ) (p : Fin n) (hp : p ∈ A w) (hrt : read (test p) r = true) :
                p ∈ A r := (active_mem C S R r p).2
              ⟨((active_mem C S R w p).1 hp).1, by simpa [read, hlt r p hrt] using hrt⟩
            refine ⟨{a, b}, ?_, ?_, Or.inr ⟨Finset.card_le_two, hlow, hcard, j, hw.symm, hop, ?_, ?_⟩⟩
            · intro r hr
              rcases Finset.mem_insert.mp hr with rfl | hr
              · exact ⟨hla, by simpa [read, hla, Low, base] using hbase.1⟩
              · obtain rfl := Finset.mem_singleton.mp hr
                exact ⟨hlb, by simpa [read, hlb, Low, base] using hbase.2⟩
            · intro p hp
              rcases htest p hp with h | h
              · exact Finset.mem_biUnion.mpr ⟨a, by simp, hmem a p hp h⟩
              · exact Finset.mem_biUnion.mpr ⟨b, by simp, hmem b p hp h⟩
            · change g.inputs.length = 2
              simp [hs]
            · intro r hr
              change r ∈ g.inputs at hr
              rw [hs] at hr
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with ha' | hb'
              · rw [ha']; exact ⟨u, hmem a u hu htu⟩
              · rw [hb']; exact ⟨v, hmem b v hv htv⟩
          · exact one a hbase.1 (fun p hp => (htest p hp).resolve_right (fun h => hB ⟨p, hp, h⟩))
        · exact one b hbase.2 (fun p hp => (htest p hp).resolve_left (fun h => hA ⟨p, hp, h⟩))

theorem count_active {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (R : Fin n → Finset (Fin n))
    (hR : ∀ p ∈ S, R p ∩ S = {p})
    (hbasis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ r ∈ F, r < t ∧ Low C S r) :
    (F.biUnion (active C S R)).card ≤ F.card + ((paidWires C S R).filter (· < t)).card := by
  let G := paidWires C S R
  let A := active C S R
  change (F.biUnion A).card ≤ F.card + (G.filter (· < t)).card
  induction t generalizing F with
  | zero =>
    have hnil : F = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun r hr => by have := (hF r hr).1; omega)
    simp [hnil]
  | succ t ih =>
    have hmono : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card := by
      apply Finset.card_le_card
      intro r hr
      have hp := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hp.1, by omega⟩
    by_cases ht : t ∈ F
    · let rest := F.erase t
      have hrest (r : ℕ) (hr : r ∈ rest) : r < t ∧ Low C S r := by
        obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hr
        exact ⟨by have := (hF r hb).1; omega, (hF r hb).2⟩
      have hrest_card : rest.card + 1 = F.card := Finset.card_erase_add_one ht
      by_cases hsmall : (A t).card ≤ 1
      · have hsub : F.biUnion A ⊆ rest.biUnion A ∪ A t := by
          intro p hp
          obtain ⟨r, hr, hpr⟩ := Finset.mem_biUnion.mp hp
          by_cases hr' : r = t
          · subst r; exact Finset.mem_union_right _ hpr
          · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_erase.mpr ⟨hr', hr⟩, hpr⟩)
        have hbound := ih rest hrest
        have hsubcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        omega
      · have hbig : 2 ≤ (A t).card := by omega
        obtain ⟨P, hp, hcover, hsize⟩ := expand_active C S R hR hbasis t (hF t ht).2 hbig
        let F' := rest ∪ P
        have hF' (r : ℕ) (hr : r ∈ F') : r < t ∧ Low C S r :=
          (Finset.mem_union.mp hr).elim (hrest r) (hp r)
        have hs : F.biUnion A ⊆ F'.biUnion A := by
          intro p hm
          obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp hm
          by_cases he : r = t
          · subst r
            obtain ⟨k, hk, hak⟩ := Finset.mem_biUnion.mp (hcover har)
            exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_union_right _ hk, hak⟩
          · exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hr⟩), har⟩
        have hout := (Finset.card_le_card hs).trans (ih F' hF')
        have hfront : F'.card ≤ rest.card + P.card := Finset.card_union_le _ _
        rcases hsize with hsmall' | ⟨hlarge, hpaid⟩
        · omega
        · have htG : t ∈ G := (paid_mem C S R t).2 hpaid
          have hEq : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
            ext r
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hr, hlt⟩
              by_cases he : r = t
              · exact Or.inl he
              · exact Or.inr ⟨hr, by omega⟩
            · rintro (rfl | ⟨hr, hlt⟩)
              · exact ⟨htG, by omega⟩
              · exact ⟨hr, by omega⟩
          rw [hEq, Finset.card_insert_of_notMem (by simp)]
          omega
    · have hcut (r : ℕ) (hr : r ∈ F) : r < t ∧ Low C S r := by
        have h := hF r hr
        have hne : r ≠ t := fun e => ht (e ▸ hr)
        exact ⟨by omega, h.2⟩
      have h := ih F hcut
      omega

theorem pointing {n : ℕ} (C : Circuit) (hmono : IsMonotoneCircuit C)
    (S T : Finset (Fin n)) (R : Fin n → Finset (Fin n)) (w : ℕ)
    (hinter : (S ∩ T).card ≤ 1) (hactive : 2 ≤ (active C S R w).card) (hlow : Low C T w) :
    ∃ p ∈ S \ T, (R p ∩ T).Nonempty := by
  classical
  have hn : ¬ active C S R w ⊆ T := by
    intro h
    have hs : active C S R w ⊆ S ∩ T := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨((active_mem C S R w p).mp hp).1, h hp⟩
    have := Finset.card_le_card hs
    omega
  obtain ⟨p, hp, hpT⟩ := Finset.not_subset.mp hn
  obtain ⟨hpS, hval⟩ := (active_mem C S R w p).mp hp
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hpS, hpT⟩, ?_⟩
  by_contra hmiss
  have hxy (r : Fin n) (hr : query R p r = true) : outside T r = true := by
    apply decide_eq_true
    intro hT
    exact hmiss ⟨r, Finset.mem_inter.mpr ⟨of_decide_eq_true hr, hT⟩⟩
  have ht := value_mono C hmono (query R p) (outside T) hxy w hval
  exact Bool.false_ne_true (hlow.symm.trans ht)

theorem bound (q n m : ℕ) (S : Fin m → Finset (Fin n)) (R : Fin m → Fin n → Finset (Fin n))
    (hcard : ∀ i, (S i).card = q + 1) (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hR : ∀ i p, p ∈ S i → R i p ∩ S i = {p})
    (hnopoint : ∀ i j, i ≠ j → ¬ ((∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty)))
    (gates : List Gate) (out : Fin m → ℕ)
    (hbasis : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hneg : ∀ w : Fin m, Circuit.eval ⟨gates, out w⟩ (List.ofFn (outside (S w))) = false)
    (hpos : ∀ (w : Fin m) (p : Fin n), p ∈ S w →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn (query (R w) p)) = true)
    (I : Finset (Fin gates.length))
    (hI : ∀ g : Fin gates.length, ((gates.get g).op = GateOp.or ∧ (gates.get g).inputs.length = 2 ∧
      (∃ i : Fin m, Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (outside (S i))) = false) ∧
      ∀ w ∈ (gates.get g).inputs, ∃ (i : Fin m) (p : Fin n), p ∈ S i ∧
        Circuit.eval ⟨gates, w⟩ (List.ofFn (query (R i) p)) = true) → g ∈ I) :
    m * q ≤ I.card := by
  classical
  let C : Circuit := ⟨gates, 0⟩
  let G (i : Fin m) := paidWires C (S i) (R i)
  have hmono : IsMonotoneCircuit C := fun g hg => (hbasis g hg).1
  have hcount (i : Fin m) : q ≤ (G i).card := by
    have hlow : Low C (S i) (out i) := hneg i
    have hA : active C (S i) (R i) (out i) = S i := by
      ext p
      exact ⟨fun hp => ((active_mem C (S i) (R i) (out i) p).mp hp).1,
        fun hp => (active_mem C (S i) (R i) (out i) p).mpr ⟨hp, hpos i p hp⟩⟩
    have h := count_active C (S i) (R i) (hR i) hbasis (out i + 1) {out i} (by
      intro r hr
      obtain rfl := Finset.mem_singleton.mp hr
      exact ⟨by omega, hlow⟩)
    simp only [Finset.singleton_biUnion, hA, hcard, Finset.card_singleton] at h
    change q + 1 ≤ 1 + ((G i).filter (· < out i + 1)).card at h
    have hle := Finset.card_filter_le (G i) (· < out i + 1)
    omega
  have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    obtain ⟨hloi, haci, _⟩ := (paid_mem C (S i) (R i) w).mp hi
    obtain ⟨hloj, hacj, _⟩ := (paid_mem C (S j) (R j) w).mp hj
    have hc : (S j ∩ S i).card ≤ 1 := by simpa [Finset.inter_comm] using hinter i j hij
    exact hnopoint i j hij ⟨pointing C hmono (S i) (S j) (R i) w (hinter i j hij) haci hloj,
      pointing C hmono (S j) (S i) (R j) w hc hacj hloi⟩
  let f : Fin gates.length → ℕ := fun g => n + g.val
  have hall : Finset.univ.biUnion G ⊆ I.image f := by
    intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hl, _, g, rfl, hor, hlen, hins⟩ := (paid_mem C (S i) (R i) w).mp hi
    refine Finset.mem_image.mpr ⟨g, hI g ⟨hor, hlen, ⟨i, hl⟩, ?_⟩, rfl⟩
    intro r hr
    obtain ⟨p, hp⟩ := hins r hr
    exact ⟨i, p, (active_mem C (S i) (R i) r p).mp hp⟩
  calc
    m * q = ∑ _ : Fin m, q := by simp
    _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ => hcount i
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (I.image f).card := Finset.card_le_card hall
    _ ≤ I.card := Finset.card_image_le

end PEqualNP.Outside.L_meta_1460

theorem PEqualNP.Outside.L_meta_1460 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)),
    1 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i → R i p ∩ S i = {p}) →
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length ≤ 2) →
    (∀ w : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S w))) = false) →
    (∀ (w : Fin m) (p : Fin n), p ∈ S w →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R w p))) = true) →
    ∀ I : Finset (Fin gates.length), (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (gates.get g).inputs.length = 2 ∧
      (∃ i : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = false) ∧
      ∀ w ∈ (gates.get g).inputs, ∃ (i : Fin m) (p : Fin n), p ∈ S i ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R i p))) = true) → g ∈ I) → m * q ≤ I.card := by
  intro q n m S R _ hcard hinter hR hpoint gates out hbasis hneg hpos I hI
  exact PEqualNP.Outside.L_meta_1460.bound q n m S R hcard hinter hR hpoint gates out hbasis hneg hpos I hI
