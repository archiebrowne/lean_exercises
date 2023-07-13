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
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
apply Iff.intro
·intro h
 match h with
 |⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
 |⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
·intro h
 match h with
 |Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
 |Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
apply Iff.intro
·intro h
 match h with
 |Or.inl hp => constructor <;> apply Or.inl <;> assumption
 |Or.inr ⟨hq, hr⟩ => constructor <;> apply Or.inr <;> assumption
·intro h
 have hpq : p ∨ q := h.1
 have hpr : p ∨ r := h.2
 cases hpq with
 |inl hp => apply Or.inl; exact hp
 |inr hq => 
  cases hpr with
  |inl hp => apply Or.inl; exact hp
  |inr hr => apply Or.inr; constructor <;> assumption


-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
apply Iff.intro
·intros h₁ h₂ 
 exact h₁ h₂.1 h₂.2
·intros h₁ hp hq
 exact h₁ ⟨hp, hq⟩ 
  


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
apply Iff.intro
·intro h; constructor <;> intro h'; exact h (Or.inl h'); exact h (Or.inr h')
·intros h h'
 cases h' with
 |inl hp => exact h.1 hp
 |inr hq => exact h.2 hq


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
apply Iff.intro
·intro h 
 push_neg at h; exact h
·intro h 
 push_neg; exact h













/-example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry 
-/