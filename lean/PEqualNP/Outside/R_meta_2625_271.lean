import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_2625_271
    (clean :
      let reps : List (ℕ × ℕ) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
      let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
        let bit := fun (a b : ℕ) (i : Fin 13) =>
          if dual then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
        Fin.append (bit z.1 z.2) (bit z.2 z.1)
      ∀ z ∈ reps, ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ (t : Fin 13) (dual : Bool),
        let x := row z m t dual
        let P := Finset.univ.filter fun p : Fin 13 => x (Fin.castAdd 13 p)
        let L := Finset.univ.filter fun l : Fin 13 => x (Fin.natAdd 13 l)
        (∀ l : Fin 13, (P ∩ singerLines3 l).card ≤ 2) ∧
        (∀ p : Fin 13, (L.filter fun l => p ∈ singerLines3 l).card ≤ 2) ∧
        L ⊆ missLines singerLines3 P)
    (search :
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
      (∀ p l : Fin 13, p ∈ singerLines3 l →
        circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) ∧
      ∀ S : Finset (Fin 26), IsPrimeImplicant 26 C S →
        let P := Finset.univ.filter fun p : Fin 13 => Fin.castAdd 13 p ∈ S
        let L := Finset.univ.filter fun l : Fin 13 => Fin.natAdd 13 l ∈ S
        (∃ p ∈ P, ∃ l ∈ L, p ∈ singerLines3 l) ∨
        (∃ l : Fin 13, 3 ≤ (P ∩ singerLines3 l).card) ∨
        ∃ p : Fin 13, 3 ≤ (L.filter fun l => p ∈ singerLines3 l).card) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (63 : ℕ) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), (∃ x7 ∈ x1, x5 = x6 + x7) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ x5 ∈ x2, ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool), PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 (x3 x5 x7 x9 x10) = Bool.false := by
  classical
  dsimp only
  obtain ⟨C,mono,budget,accepted,primeSafe⟩ := search
  have endpoints :
      ∀ p l : Fin 13, (∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = l + d) ↔
        p ∈ singerLines3 l := by decide +kernel
  refine ⟨C,mono,budget,(fun p l inc => accepted p l ((endpoints p l).mp inc)),?_⟩
  intro z hz m hm t dual
  let bit := fun (a b : ℕ) (i : Fin 13) =>
    if dual then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
  let x : Fin 26 → Bool := Fin.append (bit z.1 z.2) (bit z.2 z.1)
  change circuitFun 26 C x = false
  let P := Finset.univ.filter fun p : Fin 13 => x (Fin.castAdd 13 p)
  let L := Finset.univ.filter fun l : Fin 13 => x (Fin.natAdd 13 l)
  have negative : (∀ l : Fin 13, (P ∩ singerLines3 l).card ≤ 2) ∧
      (∀ p : Fin 13, (L.filter fun l => p ∈ singerLines3 l).card ≤ 2) ∧
      L ⊆ missLines singerLines3 P := clean z hz m hm t dual
  apply Bool.eq_false_iff.mpr
  intro bad
  let full : Finset (Fin 26) := Finset.univ.filter fun i => x i
  have trueOnFull : circuitFun 26 C (setInput full) = true := by
    have same : setInput full = x := by
      funext i
      change decide (i ∈ full) = x i
      cases value : x i <;> simp [full,value]
    rwa [same]
  let acceptedSets := full.powerset.filter fun S => circuitFun 26 C (setInput S) = true
  obtain ⟨S,hS,minimal⟩ := Finset.exists_min_image acceptedSets Finset.card
    (⟨full,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl,trueOnFull⟩⟩)
  obtain ⟨inPowerset,trueOnS⟩ := Finset.mem_filter.mp hS
  have sub : S ⊆ full := Finset.mem_powerset.mp inPowerset
  have prime : IsPrimeImplicant 26 C S := by
    refine ⟨trueOnS,?_⟩
    intro T mem
    apply Bool.eq_false_iff.mpr
    intro truth
    have less := Finset.mem_ssubsets.mp mem
    have cand : T ∈ acceptedSets :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (less.le.trans sub),truth⟩
    exact (Nat.not_le_of_lt (Finset.card_lt_card less)) (minimal T cand)
  let SP := Finset.univ.filter fun p : Fin 13 => Fin.castAdd 13 p ∈ S
  let SL := Finset.univ.filter fun l : Fin 13 => Fin.natAdd 13 l ∈ S
  have pSub : SP ⊆ P := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp (sub (Finset.mem_filter.mp hp).2)).2⟩
  have lSub : SL ⊆ L := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp (sub (Finset.mem_filter.mp hl).2)).2⟩
  rcases primeSafe S prime with ⟨p,hp,l,hl,inc⟩ | ⟨l,three⟩ | ⟨p,three⟩
  · have miss := (Finset.mem_filter.mp (negative.2.2 (lSub hl))).2
    exact Finset.disjoint_left.mp miss inc (pSub hp)
  · have le : (SP ∩ singerLines3 l).card ≤ (P ∩ singerLines3 l).card :=
      Finset.card_le_card (fun _ h => Finset.mem_inter.mpr
        ⟨pSub (Finset.mem_inter.mp h).1, (Finset.mem_inter.mp h).2⟩)
    have limit := negative.1 l
    change 3 ≤ (SP ∩ singerLines3 l).card at three
    omega
  · have le := Finset.card_le_card (Finset.filter_subset_filter (fun l => p ∈ singerLines3 l) lSub)
    have limit := negative.2.1 p
    change 3 ≤ (SL.filter fun l => p ∈ singerLines3 l).card at three
    omega
