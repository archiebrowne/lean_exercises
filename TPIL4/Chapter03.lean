import Mathlib.Tactic

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
apply Iff.intro
·intro h; constructor; exact h.2; exact h.1
·intro h; constructor; exact h.2; exact h.1


example : p ∨ q ↔ q ∨ p := by 
apply Iff.intro
·intro h
 cases h with
 |inl hp => apply Or.inr; assumption
 |inr hq => apply Or.inl; assumption
·intro h
 cases h with
 |inr hq => apply Or.inl; assumption 
 |inl hp => apply Or.inr; assumption



-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
apply Iff.intro
·intro h; constructor; exact h.1.1; constructor; exact h.1.2; exact h.2
·intro h; constructor; constructor; exact h.1; exact h.2.1; exact h.2.2


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
apply Iff.intro
·intro h
 cases h with
 |inl hpq => 
  cases hpq with
  |inl hp => apply Or.inl; assumption
  |inr hq => apply Or.inr; apply Or.inl; assumption
 |inr hr => apply Or.inr; apply Or.inr; assumption
·intro h
 cases h with
 |inl hp => apply Or.inl; apply Or.inl; assumption
 |inr hqr => 
  cases hqr with
  |inl hq => apply Or.inl; apply Or.inr; assumption
  |inr hr => apply Or.inr; assumption

-- distributivity
/- example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry 
-/