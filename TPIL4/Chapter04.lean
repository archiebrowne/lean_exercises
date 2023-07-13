import Mathlib.Tactic

variable (α : Type) (p q : α → Prop)

-- Exercise 01


example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
apply Iff.intro
·intro h
 constructor <;> intro x; exact (h x).1; exact (h x).2
·intro h
 intro x; constructor; exact h.1 x; exact h.2 x
 
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
intros hpq hp
intro x
specialize hp x
specialize hpq x
exact hpq hp

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
intro h
intro x
cases h with
|inl hp => apply Or.inl; exact hp x
|inr hq => apply Or.inr; exact hq x


-- Exercise 02

variable (r : Prop)

/-
example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
-/


-- Exercise 03

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

/-
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
-/

-- Exercise 04

/-
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry
-/

-- Exercise 05

/- Prove as many exercises in existential quantifer section as possible -/

