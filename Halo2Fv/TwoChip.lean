import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace TwoChip

  section defs
    structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) :=
      Instance: ℕ → ℕ → ZMod P
      Advice: ℕ → ℕ → ZMod P
      -- Fixed: ℕ → ℕ → ZMod P
      Selector: ℕ → ℕ → ZMod P
      a: ZMod P
      b: ZMod P
      c: ZMod P

    variable {P: ℕ} {P_Prime: Nat.Prime P} (c: Circuit P P_Prime)

    --REGION: load private
    --Annotation: private input
    -- def advice_0_0: Prop := c.Advice 0 0 = c.a
    --EXITED REGION: load private
    --REGION: load private
    --Annotation: private input
    -- def advice_0_1: Prop := c.Advice 0 1 = c.b
    --EXITED REGION: load private
    --REGION: load private
    --Annotation: private input
    -- def advice_0_2: Prop := c.Advice 0 2 = c.c
    --EXITED REGION: load private
    --REGION: add
    def selector_0_3: Prop := c.Selector 0 3 = 1
    --Annotation: lhs
    -- def advice_0_3: Prop := c.Advice 0 3 = c.a
    def copy_0: Prop := c.Advice 0 3 = c.Advice 0 0
    --Annotation: rhs
    -- def advice_1_3: Prop := c.Advice 1 3 = c.b
    def copy_1: Prop := c.Advice 1 3 = c.Advice 0 1
    --Annotation: lhs + rhs
    -- def advice_0_4: Prop := c.Advice 0 4 = (c.a) + (c.b)
    --EXITED REGION: add
    --REGION: mul
    def selector_1_5: Prop := c.Selector 1 5 = 1
    --Annotation: lhs
    -- def advice_0_5: Prop := c.Advice 0 5 = (c.a) + (c.b)
    def copy_2: Prop := c.Advice 0 5 = c.Advice 0 4
    --Annotation: rhs
    -- def advice_1_5: Prop := c.Advice 1 5 = c.c
    def copy_3: Prop := c.Advice 1 5 = c.Advice 0 2
    --Annotation: lhs * rhs
    -- def advice_0_6: Prop := c.Advice 0 6 = ((c.a) + (c.b)) * (c.c)
    --EXITED REGION: mul
    def copy_4: Prop := c.Advice 0 6 = c.Instance 0 0
    ------GATES-------
    def gate_0: Prop := ∀ row : ℕ, c.Selector 0 row * (c.Advice 0 (row) + c.Advice 1 (row) - c.Advice 0 (row + 1)) = 0
    def gate_1: Prop := ∀ row : ℕ, c.Selector 1 row * (c.Advice 0 (row) * c.Advice 1 (row) - c.Advice 0 (row + 1)) = 0

    def advice_func: ℕ → ℕ → ZMod P :=
      λ x y => match x with
        | 0 => match y with
          | 0 => c.a
          | 1 => c.b
          | 2 => c.c
          | 3 => c.a
          | 4 => (c.a) + (c.b)
          | 5 => (c.a) + (c.b)
          | 6 => ((c.a) + (c.b)) * (c.c)
          | _ => 0
        | 1 => match y with
          | 3 => c.b
          | 5 => c.c
          | _ => 0
        | _ => 0
    
    def all_copy_constraints: Prop :=
      copy_0 c ∧
      copy_1 c ∧
      copy_2 c ∧
      copy_3 c ∧
      copy_4 c

    def all_gates: Prop :=
      gate_0 c ∧
      gate_1 c
    
    def selector_0_n: Prop := ∀ row : ℕ, row ≠ 3 → c.Selector 0 row = 0
    def selector_1_n: Prop := ∀ row : ℕ, row ≠ 5 → c.Selector 1 row = 0
    def all_selectors: Prop :=
      selector_0_3 c ∧
      selector_0_n c ∧
      selector_1_5 c ∧
      selector_1_n c

    def meets_constraints: Prop := all_selectors c ∧ all_gates c ∧ all_copy_constraints c

    def spec (x y z: ZMod P): Prop := (x + y) * z = c.Instance 0 0
  end defs

  section proofs
    lemma advice_satisfies_spec_of_constraints (c: Circuit P P_Prime) : meets_constraints c → spec c (c.Advice 0 0) (c.Advice 0 1) (c.Advice 0 2) := by
      unfold meets_constraints
      unfold all_selectors all_gates all_copy_constraints
      unfold selector_0_3 selector_0_n selector_1_5 selector_1_n
      unfold gate_0 gate_1
      unfold copy_0 copy_1 copy_2 copy_3 copy_4
      intro ⟨
        ⟨hS_0_3, _, hS_1_5, _⟩,
        ⟨
          ⟨hGate0, hGate1⟩,
          ⟨hAdvice_0_3, hAdvice_1_3, hAdvice_0_5, hAdvice_1_5, hAdvice_0_6⟩
        ⟩
      ⟩
      have h: c.Selector 0 3 * (c.Advice 0 3 + c.Advice 1 3 - c.Advice 0 4) = 0 := hGate0 3
      rewrite [hS_0_3, one_mul] at h
      have h': c.Selector 1 5 * (c.Advice 0 5 * c.Advice 1 5 - c.Advice 0 6) = 0 := hGate1 5
      rewrite [hS_1_5, one_mul] at h'
      rewrite [hAdvice_0_3, hAdvice_1_3, sub_eq_zero] at h
      rewrite [hAdvice_0_5, hAdvice_1_5, hAdvice_0_6, sub_eq_zero, ←h] at h'
      exact h'

    theorem spec_of_constraints (c: Circuit P P_Prime) : meets_constraints c → ∃ x y z: ZMod P, spec c x y z := by
      intro hConstraints
      exact ⟨c.Advice 0 0, c.Advice 0 1, c.Advice 0 2, advice_satisfies_spec_of_constraints c hConstraints⟩

    theorem instance_of_witness (c: Circuit P P_Prime) (hAdvice: c.Advice = advice_func c) :
      meets_constraints c → spec c c.a c.b c.c := by
        intro hConstraints
        have hSpec: spec c (c.Advice 0 0) (c.Advice 0 1) (c.Advice 0 2) := advice_satisfies_spec_of_constraints c hConstraints
        aesop

    -- theorem witness_of_valid_instance :
    --   ∀ c : Circuit P P_Prime,
    --     @meets_constraints P P_Prime c →
    --     @meets_constraints P P_Prime {c with Advice := advice_func c} := by
    --   intro c ⟨
    --     ⟨hS_0_3, hS_0_n, hS_1_5, hS_1_n⟩,
    --     ⟨
    --       ⟨hGate0, hGate1⟩,
    --       ⟨hAdvice_0_3, hAdvice_1_3, hAdvice_0_5, hAdvice_1_5, hAdvice_0_6⟩
    --     ⟩
    --   ⟩
    --   unfold meets_constraints
    --   let c': Circuit P P_Prime := {c with Advice := advice_func c}
    --   have hS_0_3': selector_0_3 c' := by aesop
    --   have hS_0_n': selector_0_n c' := by aesop
    --   have hS_1_5': selector_1_5 c' := by aesop
    --   have hS_1_n': selector_1_n c' := by aesop
    --   have hGate_0' : gate_0 c' := by
    --     unfold gate_0 at hGate0 ⊢
    --     intro row
    --     match row with
    --       | 3 => unfold selector_0_3 at hS_0_3; simp [hS_0_3, one_mul, advice_func]
    --       | 0 => unfold selector_0_n at hS_0_n; simp [*]
    --       | 1 => unfold selector_0_n at hS_0_n; simp [*]
    --       | 2 => unfold selector_0_n at hS_0_n; simp [*]
    --       | x+4 => unfold selector_0_n at hS_0_n; simp [*]
    --   have hGate_1' : @gate_1 P P_Prime c' := by
    --     unfold gate_1 at hGate1 ⊢
    --     intro row
    --     match row with
    --       | 5 => unfold selector_1_5 at hS_1_5; simp [advice_func]
    --       | 0 => unfold selector_1_n at hS_1_n; simp [*]
    --       | 1 => unfold selector_1_n at hS_1_n; simp [*]
    --       | 2 => unfold selector_1_n at hS_1_n; simp [*]
    --       | 3 => unfold selector_1_n at hS_1_n; simp [*]
    --       | 4 => unfold selector_1_n at hS_1_n; simp [*]
    --       | x+6 => unfold selector_1_n at hS_1_n; simp [*]
    --   have hCopy_0' : copy_0 c' := by unfold copy_0; aesop
    --   have hCopy_1' : copy_1 c' := by unfold copy_1; aesop
    --   have hCopy_2' : copy_2 c' := by unfold copy_2; aesop
    --   have hCopy_3' : copy_3 c' := by unfold copy_3; aesop
    --   split_ands
    --   . exact hS_0_3'
    --   . exact hS_0_n'
    --   . exact hS_1_5'
    --   . exact hS_1_n'
    --   . exact hGate_0'
    --   . exact hGate_1'
    --   . exact hCopy_0'
    --   . exact hCopy_1'
    --   . exact hCopy_2'
    --   . exact hCopy_3'
    --   . unfold copy_4 at hAdvice_0_6 ⊢
    --     simp only [advice_func]
    --     unfold copy_0 at hAdvice_0_3
    --     unfold copy_1 at hAdvice_1_3
    --     unfold copy_2 at hAdvice_0_5
    --     unfold copy_3 at hAdvice_1_5
    --     -- need c.Instance 0 0 = (c.a + c.b) * c.c

  end proofs

end TwoChip