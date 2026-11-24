import PEqualNP.Defs

namespace PEqualNP.Outside.SemanticDedup4356

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Constant propagation and prefix evaluation from PEqualNP's checked gate-elimination proof.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

private lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

private lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

abbrev Stat := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

private lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

private lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

private lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

private lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

private lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

abbrev Signal (n : ℕ) := (Fin n → Bool) → Bool

private def rawSignals (n : ℕ) (i : Fin (n+2)) : Signal n :=
  fun x => (false :: true :: List.ofFn x).getD i.val false

private def isBasic (n : ℕ) (s : Signal n) : Prop :=
  ∃ i : Fin (n+2), s = rawSignals n i

private def available (n : ℕ) (gs : List Gate) (s : Signal n) : Prop :=
  ∃ r : Stat, r.Valid (n+gs.length) ∧
    ∀ x : Fin n → Bool, r.val (wiresFrom gs (List.ofFn x)) = s x

private lemma basic_available (n : ℕ) (gs : List Gate) (s : Signal n) (base : isBasic n s) :
    available n gs s := by
  obtain ⟨⟨i,hi⟩,rfl⟩ := base
  cases i with
  | zero => exact ⟨.inl false,trivial,fun _ => rfl⟩
  | succ i =>
    cases i with
    | zero => exact ⟨.inl true,trivial,fun _ => rfl⟩
    | succ i =>
      have oldBound : i < n := by omega
      refine ⟨.inr i,by change i < n+gs.length; omega,?_⟩
      intro x
      change (wiresFrom gs (List.ofFn x)).getD i false = (List.ofFn x).getD i false
      exact getD_wiresFrom _ _ _ (by simpa using oldBound)

private lemma available_append (n : ℕ) (gs more : List Gate) (s : Signal n)
    (known : available n gs s) : available n (gs ++ more) s := by
  obtain ⟨r,hBound,agrees⟩ := known
  refine ⟨r,Stat.valid_mono (by simp) _ hBound,?_⟩
  intro x
  rw [wiresFrom_append]
  obtain ⟨rest,eq,_⟩ := wiresFrom_prefix more (wiresFrom gs (List.ofFn x))
  rw [eq, Stat.val_append _ _ _ (by simpa [length_wiresFrom] using hBound)]
  exact agrees x

private def signalAt {n : ℕ} (row : (Fin n → Bool) → List Bool) (gs : List Gate)
    (i : ℕ) : Signal n :=
  fun x => (wiresFrom gs (row x)).getD ((row x).length+i) false

private lemma sameSignal_append {n : ℕ} (row : (Fin n → Bool) → List Bool)
    (gs more : List Gate) (i : ℕ) (earlier : i < gs.length) :
    signalAt row (gs++more) i = signalAt row gs i := by
  funext x
  unfold signalAt
  rw [wiresFrom_append,getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; omega)]

private lemma gate_signal_snoc {n : ℕ} (row : (Fin n → Bool) → List Bool)
    (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    signalAt row (gs++[g]) gs.length x =
      g.op.eval (g.inputs.map fun i => (wiresFrom gs (row x)).getD i false) := by
  unfold signalAt
  rw [wiresFrom_append,← length_wiresFrom]
  exact getD_snoc_eq _ _ _

private lemma append_alias_inv
    {n : ℕ} (x : Fin n → Bool) (w : List Bool) (acc : List Stat × List Gate)
    (s : Stat) (known : s.Valid (n+acc.2.length)) (b : Bool)
    (same : s.val (wiresFrom acc.2 (List.ofFn x)) = b)
    (inv : Inv n (List.ofFn x) w acc) :
    Inv n (List.ofFn x) (w++[b]) (acc.1++[s],acc.2) := by
  refine ⟨by simp [inv.1],?_⟩
  intro i
  by_cases atEnd : i = acc.1.length
  · subst i
    change ((acc.1++[s]).getD acc.1.length (.inl false)).Valid (n+acc.2.length) ∧
      ((acc.1++[s]).getD acc.1.length (.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        (w++[b]).getD acc.1.length false
    rw [getD_snoc_eq,inv.1,getD_snoc_eq]
    exact ⟨known,same⟩
  · change ((acc.1++[s]).getD i (.inl false)).Valid (n+acc.2.length) ∧
      ((acc.1++[s]).getD i (.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        (w++[b]).getD i false
    rw [getD_snoc_ne _ _ _ _ atEnd, getD_snoc_ne _ _ _ _ (by rwa [← inv.1])]
    exact inv.2 i

private lemma expandInv {n : ℕ} (row : (Fin n → Bool) → List Bool) (r : ℕ)
    (rowLen : ∀ x, (row x).length = r)
    (pre : List Gate) (g : Gate) (acc : List Stat × List Gate) (ok : Ok g)
    (inv : ∀ x, Inv n (List.ofFn x) (wiresFrom pre (row x)) acc) :
    (∀ x, Inv n (List.ofFn x) (wiresFrom (pre++[g]) (row x)) (elimStep n acc g)) ∧
      available n (elimStep n acc g).2 (signalAt row (pre++[g]) pre.length) := by
  have next (x : Fin n → Bool) :
      Inv n (List.ofFn x) (wiresFrom (pre++[g]) (row x)) (elimStep n acc g) := by
    rw [wiresFrom_append]
    exact inv_elim n _ (by simp) [g] _ acc (by simpa) (inv x)
  refine ⟨next,?_⟩
  let new := elimStep n acc g
  let lookup := new.1.getD (r+pre.length) (.inl false)
  have lookupValid := ((next (fun _ => false)).2 (r+pre.length)).1
  refine ⟨lookup,lookupValid,?_⟩
  intro x
  have val := ((next x).2 (r+pre.length)).2
  simpa only [signalAt,rowLen] using val

end PEqualNP.Outside.SemanticDedup4356

namespace PEqualNP.Outside.SemanticDedup4356

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma deduplicate_prefix
    {n : ℕ} (row : (Fin n → Bool) → List Bool) (r : ℕ)
    (rowLen : ∀ x, (row x).length = r) (initial : List Stat)
    (init : ∀ x, Inv n (List.ofFn x) (row x) (initial,[]))
    (gs : List Gate) (valid : ∀ g ∈ gs, Ok g) :
    ∃ (acc : List Stat × List Gate) (kept : Finset (Signal n)),
      (∀ x, Inv n (List.ofFn x) (wiresFrom gs (row x)) acc) ∧
      (∀ g ∈ acc.2, Ok g) ∧ acc.2.length ≤ kept.card ∧
      (∀ f ∈ kept, available n acc.2 f) ∧
      ∀ f ∈ kept, ¬ isBasic n f ∧ ∃ j < gs.length, f = signalAt row gs j := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨(initial,[]),∅,?_,by simp,by simp,by simp,by simp⟩
    exact init
  | append_singleton pre g ih =>
    obtain ⟨acc,kept,inv,good,cap,avail,fromOld⟩ :=
      ih (fun q mem => valid q (List.mem_append_left _ mem))
    let f := signalAt row (pre++[g]) pre.length
    have keepOld (h : Signal n) (inOld : h ∈ kept) :
        ¬ isBasic n h ∧ ∃ j < (pre++[g]).length, h = signalAt row (pre++[g]) j := by
      obtain ⟨notBasic,j,real,eq⟩ := fromOld h inOld
      refine ⟨notBasic,j,by simp; omega,?_⟩
      exact eq.trans (sameSignal_append row pre [g] j real).symm
    by_cases known : available n acc.2 f
    · obtain ⟨status,hstatus,correct⟩ := known
      refine ⟨(acc.1++[status],acc.2),kept,?_,good,cap,avail,keepOld⟩
      intro x
      rw [wiresFrom_append]
      exact append_alias_inv x _ acc status hstatus _ ((correct x).trans (gate_signal_snoc row pre g x))
        (inv x)
    · have notBase : ¬ isBasic n f := fun basic => known (basic_available n _ f basic)
      have unseen : f ∉ kept := fun hm => known (avail f hm)
      let next := elimStep n acc g
      have gOK : Ok g := valid g (by simp)
      obtain ⟨nextInv,newAvail⟩ := expandInv row r rowLen pre g acc gOK inv
      have emitCount : next.2.length ≤ acc.2.length+1 := by
        exact elim_len n [g] acc
      have nextGates : ∀ q ∈ next.2, Ok q := elim_ok n [g] acc good
      refine ⟨next,insert f kept,nextInv,nextGates,?_,?_,?_⟩
      · simpa [unseen] using emitCount.trans (Nat.add_le_add_right cap 1)
      · intro h mem
        rcases Finset.mem_insert.mp mem with rfl | old
        · exact newAvail
        · exact available_append n acc.2 _ h (avail h old)
      · intro h mem
        rcases Finset.mem_insert.mp mem with rfl | old
        · exact ⟨notBase,pre.length,by simp,rfl⟩
        · exact keepOld h old

private def pinnedRow (x : Fin 6 → Bool) : List Bool :=
  [x 0,x 1,false,x 2,x 3,x 4,x 5]

private def pinnedStatuses : List Stat :=
  [.inr 0,.inr 1,.inl false,.inr 2,.inr 3,.inr 4,.inr 5]

private lemma pinned_start (x : Fin 6 → Bool) :
    Inv 6 (List.ofFn x) (pinnedRow x) (pinnedStatuses,[]) := by
  refine ⟨rfl, ?_⟩
  intro i
  by_cases bound : i < 7
  · interval_cases i <;> simp [pinnedStatuses,pinnedRow,Stat.Valid,Stat.val,wiresFrom]
  · have hi : 7 ≤ i := by omega
    change (pinnedStatuses.getD i (.inl false)).Valid 6 ∧
      (pinnedStatuses.getD i (.inl false)).val (List.ofFn x) = (pinnedRow x).getD i false
    rw [List.getD_eq_default _ _ (by simpa [pinnedStatuses] using hi),
      List.getD_eq_default _ _ (by simpa [pinnedRow] using hi)]
    exact ⟨trivial,rfl⟩

end PEqualNP.Outside.SemanticDedup4356

namespace PEqualNP.Outside.SemanticDedup4356

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma outputSmall (D : Circuit) (acc : List Stat × List Gate)
    (iv : ∀ x, Inv 6 (List.ofFn x) (wiresFrom D.gates (pinnedRow x)) acc)
    (legal : ∀ g ∈ acc.2, Ok g) (size : acc.2.length ≤ 7) :
    HasCircuitSize 6 (fun x => D.eval (pinnedRow x)) 7 := by
  let out := acc.1.getD D.output (.inl false)
  have eq (x : Fin 6 → Bool) :
      out.val (wiresFrom acc.2 (List.ofFn x)) = D.eval (pinnedRow x) :=
    ((iv x).2 D.output).2
  cases h : out with
  | inr j =>
    refine ⟨⟨acc.2,j⟩,fun g mem => ?_,size,?_⟩
    · have hg := legal g mem
      exact ⟨by simpa using hg.1,hg.2⟩
    · intro x
      have known := eq x
      rw [h] at known
      exact known
  | inl b =>
    cases b with
    | false =>
      refine ⟨⟨[],6⟩,by simp [FanInTwo],by simp [Circuit.size],?_⟩
      intro x
      have known := eq x
      rw [h] at known
      change (List.ofFn x).getD 6 false = _
      exact (List.getD_eq_default _ _ (by simp)).trans known
    | true =>
      refine ⟨⟨[⟨.and,[]⟩],6⟩,by simp [FanInTwo],by simp [Circuit.size],?_⟩
      intro x
      have known := eq x
      rw [h] at known
      change (List.ofFn x ++ [true]).getD 6 false = _
      have asNew : (List.ofFn x ++ [true]).getD 6 false = true := by
        simpa only [List.length_ofFn] using (getD_snoc_eq (List.ofFn x) true false)
      exact asNew.trans known

private lemma differSomewhere {n : ℕ} {f g : Signal n} (h : f ≠ g) :
    ∃ x : Fin n → Bool, f x ≠ g x := by
  classical
  exact not_forall.mp (fun same => h (funext same))

private lemma main (D : Circuit) (legal : FanInTwo D) (size : D.size = 11) :
    HasCircuitSize 6 (fun x => D.eval (pinnedRow x)) 7 ∨
      ∃ sequence : Fin 8 → Fin 11,
        (∀ i j : Fin 8, i ≠ j →
          ∃ x : Fin 6 → Bool,
            (D.wires (pinnedRow x)).getD (7+(sequence i).val) false ≠
              (D.wires (pinnedRow x)).getD (7+(sequence j).val) false) ∧
        ∀ i j : Fin 8, ∃ x : Fin 6 → Bool,
          (D.wires (pinnedRow x)).getD (7+(sequence i).val) false ≠
            (false::true::List.ofFn x).getD j.val false := by
  classical
  have ok (g : Gate) (mem : g ∈ D.gates) : Ok g := by
    obtain ⟨hop,hlen⟩ := legal g mem
    exact ⟨by simpa using hop,hlen⟩
  obtain ⟨acc,kept,inv,legalAcc,cap,_,fromSource⟩ :=
    deduplicate_prefix pinnedRow 7 (fun _ => rfl) pinnedStatuses pinned_start D.gates ok
  by_cases small : kept.card ≤ 7
  · exact Or.inl (outputSmall D acc inv legalAcc (cap.trans small))
  · right
    let take : Fin 8 ↪ kept :=
      (Fin.castLEEmb (by omega : 8 ≤ kept.card)).trans (Finset.equivFin kept).symm.toEmbedding
    have source (i : Fin 8) : ∃ j < D.gates.length,
        (take i).val = signalAt pinnedRow D.gates j :=
      (fromSource _ (take i).property).2
    let pos (i : Fin 8) : ℕ := Classical.choose (source i)
    have indexValid (i : Fin 8) : pos i < 11 := by
      change D.gates.length = 11 at size
      rw [← size]
      exact (Classical.choose_spec (source i)).1
    have atIndex (i : Fin 8) : (take i).val = signalAt pinnedRow D.gates (pos i) :=
      (Classical.choose_spec (source i)).2
    let sequence (i : Fin 8) : Fin 11 := ⟨pos i,indexValid i⟩
    have formula (i : Fin 8) (x : Fin 6 → Bool) :
        (take i).val x = (D.wires (pinnedRow x)).getD (7+(sequence i).val) false := by
      rw [atIndex]
      rfl
    refine ⟨sequence,?_,?_⟩
    · intro i j distinct
      have diff : (take i).val ≠ (take j).val :=
        fun eq => distinct (take.injective (Subtype.ext eq))
      obtain ⟨x,whereX⟩ := differSomewhere diff
      exact ⟨x,by simpa only [formula] using whereX⟩
    · intro i j
      have diff : (take i).val ≠ rawSignals 6 j := by
        intro eq
        exact (fromSource _ (take i).property).1 ⟨j,eq⟩
      obtain ⟨x,whereX⟩ := differSomewhere diff
      exact ⟨x,by simpa only [formula,rawSignals] using whereX⟩

end PEqualNP.Outside.SemanticDedup4356

theorem PEqualNP.Outside.L_meta_4356 :
  have x1 : (Fin (6 : ℕ) → Bool) → List Bool := fun (x1 : Fin (6 : ℕ) → Bool) => [x1 (0 : Fin (6 : ℕ)), x1 (1 : Fin (6 : ℕ)), Bool.false, x1 (2 : Fin (6 : ℕ)), x1 (3 : Fin (6 : ℕ)), x1 (4 : Fin (6 : ℕ)), x1 (5 : Fin (6 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size = (11 : ℕ) →       PEqualNP.MetaComplexity.HasCircuitSize (6 : ℕ) (fun (x5 : Fin (6 : ℕ) → Bool) => x2.eval (x1 x5)) (7 : ℕ) ∨         have x5 : Fin (11 : ℕ) → (Fin (6 : ℕ) → Bool) → Bool := fun (x5 : Fin (11 : ℕ)) (x6 : Fin (6 : ℕ) → Bool) => (x2.wires (x1 x6)).getD ((7 : ℕ) + ↑x5) Bool.false;         ∃ (x6 : Fin (8 : ℕ) → Fin (11 : ℕ)), (∀ (x7 x8 : Fin (8 : ℕ)), x7 ≠ x8 → ∃ (x10 : Fin (6 : ℕ) → Bool), x5 (x6 x7) x10 ≠ x5 (x6 x8) x10) ∧ ∀ (x7 x8 : Fin (8 : ℕ)), ∃ (x9 : Fin (6 : ℕ) → Bool), x5 (x6 x7) x9 ≠ (Bool.false :: Bool.true :: List.ofFn x9).getD (↑x8) Bool.false :=
  PEqualNP.Outside.SemanticDedup4356.main
