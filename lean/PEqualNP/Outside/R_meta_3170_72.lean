import Mathlib.Tactic
import Mathlib.Data.List.GetD
import PEqualNP.Defs

-- The binary-gate bound is proved inside L_meta_2681 and the 14-gate bound is L_meta_2012.
-- This leaves the distinct-pin case with at most one further NOT gate.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3170_72
    (binaryLower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) →
      13 ≤ C.gates.countP (fun g => !(g.op.eval [false])))
    (smallLower : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9
      (fun x => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) 14)
    (distinctPins : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧
      C.gates.countP (fun g => g.op.eval [false]) ≤ 1 ∧
      ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 1 || x 5]) = ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro pins pinCount _ near C fan size
  let target (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  let negations (g : PEqualNP.CircuitLowerBounds.Gate) := g.op.eval [false]
  let notZero : PEqualNP.CircuitLowerBounds.Gate := ⟨.not, [0]⟩
  let joinPins : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, pins⟩
  let runGate (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  suffices ∃ x, C.eval (runGate (base x) joinPins) ≠ target x by
    obtain ⟨x, hx⟩ := this
    refine ⟨x, ?_⟩
    change C.eval (runGate (base x) joinPins) ≠ _
    have sameTarget : ∀ z : Fin 9 → Bool, target z =
        (z 0 && z 1 || z 1 && z 2 || z 2 && z 3 || z 3 && z 4 ||
         z 4 && z 0 || z 0 && z 5 || z 1 && z 6 || z 2 && z 7 ||
         z 3 && z 8 || z 5 && z 7 || z 6 && z 8 || z 8 && z 5) := by
      decide +kernel
    rwa [← sameTarget x]
  by_contra! agrees
  have notAllowed : notZero.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set _) ∧
      notZero.inputs.length ≤ 2 := by simp [notZero]
  have first (x : Fin 9 → Bool) : runGate (List.ofFn x) notZero = base x := by
    change List.ofFn x ++ [!(List.ofFn x).getD 0 false] = base x
    simp [base, List.getD_eq_getElem?_getD]
  have evalPair (x : Fin 9 → Bool) (l r : ℕ) (h : pins = [l, r]) :
      runGate (base x) joinPins =
        base x ++ [(base x).getD l false || (base x).getD r false] := by
    change base x ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
      (pins.map fun i => (base x).getD i false)] = _
    rw [h]
    change base x ++ [(base x).getD l false || ((base x).getD r false || false)] = _
    simp only [Bool.or_false]
  by_cases many : 2 ≤ C.gates.countP negations
  · let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨notZero :: joinPins :: C.gates, C.output⟩
    have allowed : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      change g ∈ notZero :: joinPins :: C.gates at hg
      rcases List.mem_cons.mp hg with rfl | h
      · exact notAllowed
      rcases List.mem_cons.mp h with rfl | h
      · simp [joinPins, pinCount]
      exact fan g h
    have computes (x : Fin 9 → Bool) : D.eval (List.ofFn x) = target x := by
      change ((C.gates.foldl runGate (runGate (runGate (List.ofFn x) notZero) joinPins)).getD
        C.output false) = target x
      rw [first]
      exact agrees x
    have lower := binaryLower D allowed computes
    change 13 ≤ (notZero :: joinPins :: C.gates).countP (fun g => !negations g) at lower
    have counts := List.length_eq_countP_add_countP negations (l := C.gates)
    have countComplement : (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        decide (¬negations g = true)) = (fun g => !negations g) := by
      funext g
      cases negations g <;> simp
    rw [countComplement] at counts
    change C.gates.length ≤ 13 at size
    simp only [List.countP_cons] at lower
    change 13 ≤ C.gates.countP (fun g => !negations g) + 1 + 0 at lower
    omega
  have few : C.gates.countP negations ≤ 1 := by omega
  obtain ⟨a, b, hpins⟩ := List.length_eq_two.mp pinCount
  have ha := near a (by simp [hpins])
  have hb := near b (by simp [hpins])
  have duplicate (pin : ℕ) (inBase : pin < 10) (same : pins = [pin, pin]) : False := by
    let renumber (i : ℕ) := if i < 10 then i else if i = 10 then pin else i - 1
    let rename (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨g.op, g.inputs.map renumber⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨notZero :: C.gates.map rename, renumber C.output⟩
    have allowed : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      change g ∈ notZero :: C.gates.map rename at hg
      rcases List.mem_cons.mp hg with rfl | h
      · exact notAllowed
      obtain ⟨before, member, rfl⟩ := List.mem_map.mp h
      simpa [rename] using fan before member
    have budget : D.size ≤ 14 := by
      change C.gates.length ≤ 13 at size
      change (notZero :: C.gates.map rename).length ≤ 14
      simpa only [List.length_cons, List.length_map] using Nat.succ_le_succ size
    apply smallLower
    refine ⟨D, allowed, budget, ?_⟩
    intro x
    let inputs := base x
    let reusedBit := inputs.getD pin false
    have inputLength : inputs.length = 10 := by simp [inputs, base]
    have get (vals : List Bool) (i : ℕ) :
        (inputs ++ [reusedBit] ++ vals).getD i false = (inputs ++ vals).getD (renumber i) false := by
      rw [List.append_assoc]
      by_cases before : i < 10
      · simp only [renumber, ite_eq_left before]
        have h : i < inputs.length := by simpa [inputLength] using before
        rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
      · have past : inputs.length ≤ i := by omega
        rw [List.getD_append_right _ _ _ _ past]
        by_cases atReused : i = 10
        · subst i
          have index : renumber 10 = pin := by simp [renumber]
          rw [index, List.getD_append _ _ _ _ (by omega : pin < inputs.length)]
          simp [inputLength, reusedBit, List.getD_eq_getElem?_getD]
        · have index : renumber i = i - 1 := by simp [renumber, before, atReused]
          rw [index, List.getD_append_right _ _ _ _ (by omega : inputs.length ≤ i - 1)]
          have skip : [reusedBit].length ≤ i - inputs.length := by simp; omega
          rw [List.getD_append_right _ _ _ _ skip]
          simp only [List.length_singleton]
          congr 1
    have simulation (gs : List PEqualNP.CircuitLowerBounds.Gate) (vals : List Bool) :
        ∃ rest : List Bool,
          gs.foldl runGate (inputs ++ [reusedBit] ++ vals) = inputs ++ [reusedBit] ++ rest ∧
          (gs.map rename).foldl runGate (inputs ++ vals) = inputs ++ rest := by
      induction gs generalizing vals with
      | nil => exact ⟨vals, rfl, rfl⟩
      | cons g gs ih =>
        let bit := g.op.eval (g.inputs.map fun i => (inputs ++ [reusedBit] ++ vals).getD i false)
        have evalEq : runGate (inputs ++ vals) (rename g) = inputs ++ vals ++ [bit] := by
          simp only [runGate, rename, List.map_map, bit]
          congr 2
          apply congrArg g.op.eval
          exact List.map_congr_left (fun i _ => (get vals i).symm)
        simpa only [List.map_cons, List.foldl_cons, evalEq, runGate, bit, List.append_assoc]
          using ih (vals ++ [bit])
    obtain ⟨rest, before, after⟩ := simulation C.gates []
    have second : runGate inputs joinPins = inputs ++ [reusedBit] := by
      change runGate (base x) joinPins = _
      rw [evalPair x pin pin same]
      simp only [Bool.or_self, reusedBit, inputs]
    change ((C.gates.map rename).foldl runGate (runGate (List.ofFn x) notZero)).getD
      (renumber C.output) false = target x
    rw [first]
    change ((C.gates.map rename).foldl runGate inputs).getD (renumber C.output) false = target x
    simp only [List.append_nil] at before after
    rw [after, ← get rest C.output, ← before]
    have h := agrees x
    rw [show runGate (base x) joinPins = inputs ++ [reusedBit] from second] at h
    exact h
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact duplicate 1 (by decide) hpins
  · apply distinctPins
    refine ⟨C, fan, size, few, ?_⟩
    intro x
    change C.eval (List.ofFn x ++ [!x 0, x 1 || x 5]) = target x
    have h := agrees x
    rw [evalPair x 1 5 hpins] at h
    simpa [base, List.getD_append, List.getD_eq_getElem?_getD] using h
  · apply distinctPins
    refine ⟨C, fan, size, few, ?_⟩
    intro x
    change C.eval (List.ofFn x ++ [!x 0, x 1 || x 5]) = target x
    have h := agrees x
    rw [evalPair x 5 1 hpins] at h
    simpa [base, List.getD_append, List.getD_eq_getElem?_getD, Bool.or_comm] using h
  · exact duplicate 5 (by decide) hpins
