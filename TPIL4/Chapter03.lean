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

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
intro h
cases h with
|inl hnp => intro hpq; have hp : p := hpq.1; contradiction
|inr hnq => intro hpq; have hq : q := hpq.2; contradiction

example : ¬(p ∧ ¬p) := by
intro hpnp
have hp : p := hpnp.1
have hnp : ¬p := hpnp.2
contradiction

example : p ∧ ¬q → ¬(p → q) := by
intros h hpq
have hp : p := h.1
have hnq : ¬q := h.2
have hq : q := hpq hp
contradiction

example : ¬p → (p → q) := by
intros hnp hp
exfalso
contradiction

example : (¬p ∨ q) → (p → q) := by
intros h hp
cases h with
|inl hnp => exfalso; contradiction
|inr hq => exact hq

example : p ∨ False ↔ p := by
apply Iff.intro
·intro h
 cases h with
 |inl hp => exact hp
 |inr hfalse => exfalso; exact hfalse
·intro h; apply Or.inl; exact h

example : p ∧ False ↔ False := by
apply Iff.intro
·intro h; exact h.2
·intro h; exfalso; exact h

example : (p → q) → (¬q → ¬p) := by
intros hpq hnq hp
have hq : q := hpq hp
contradiction

/-
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
-/

/-
Prove ¬(p ↔ ¬p) without using classical reasoning.
-/
