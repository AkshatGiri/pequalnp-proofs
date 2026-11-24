import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3310_271
    (linear : ∀ (q n : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R] (C : Circuit),
      2 ≤ q → n = q^2+q+1 → (∀ l : Fin n, Fintype.card {p : Fin n // R p l} = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, R p l ∧ R r l) → Monotone2 C →
      (∀ p l : Fin n, R p l → circuitFun (n+n) C
        (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true) →
      (∀ y : Fin (n+n) → Bool, Fintype.card {l : Fin n // y (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l : Fin n, R p l ∧ y (Fin.castAdd n p) = true ∧ y (Fin.natAdd n l) = true) →
        circuitFun (n+n) C y = false) → 3*n ≤ C.size+1)
    (large : ∀ (q n : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R] (C : Circuit),
      300 ≤ q → n = q^2+q+1 → (∀ l : Fin n, Fintype.card {p : Fin n // R p l} = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, R p l ∧ R r l) → Monotone2 C →
      (∀ p l : Fin n, R p l → circuitFun (n+n) C
        (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true) →
      (∀ y : Fin (n+n) → Bool, Fintype.card {l : Fin n // y (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l : Fin n, R p l ∧ y (Fin.castAdd n p) = true ∧ y (Fin.natAdd n l) = true) →
        circuitFun (n+n) C y = false) →
      let ors := (C.gates.filter fun g => g.op.eval [true,false]).length
      2*q^2+1 ≤ ors → 100*ors < n*q →
      n*q - 100*ors ≤ 100 * (C.gates.filter fun g => !(g.op.eval [true,false])).length) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (200 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →               (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →                 have x13 : ℕ := (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length;                 (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ x13 → (100 : ℕ) * x13 < x2 * x1 → x2 * x1 - (100 : ℕ) * x13 ≤ (100 : ℕ) * (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => !x16.op.eval [Bool.true, Bool.false]) x5.gates).length
 := by
  intro q n R relation C order size degrees joins fan yes no orCount many short
  by_cases high : 300 ≤ q
  · exact large q n R C high size degrees joins fan yes no many short
  have gateFloor := linear q n R C (by omega) size degrees joins fan yes no
  have population : 100 ≤ n := by omega
  have target : n*q ≤ 100*C.size := calc
    n*q ≤ n*299 := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 100*C.size := by omega
  let flag (g : Gate) : Bool := g.op.eval [true,false]
  have tally (gs : List Gate) : (gs.filter flag).length +
      (gs.filter fun g => !flag g).length = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      cases h : flag g <;> simp [h] <;> omega
  have sum : orCount + (C.gates.filter fun g => !flag g).length = C.size := tally C.gates
  change n*q - 100*orCount ≤ 100 * (C.gates.filter fun g => !flag g).length
  omega
