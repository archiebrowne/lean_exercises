import Mathlib.Tactic

-- Exercise 01

variable (α : Type) (p q : α → Prop) (r : Prop)

section Exercise01

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

end Exercise01

-- Exercise 02

section Exercise02

example : α → ((∀ x : α, r) ↔ r) := by
intro hα
apply Iff.intro
·intro h; exact h hα
·intro h; intro; exact h

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
apply Iff.intro
·intro h
 apply Or.elim (Classical.em r)
 ·intro hr; apply Or.inr; exact hr
 ·intro hnr 
  apply Or.inl
  intro x
  specialize h x
  cases h with
  |inl hp => exact hp
  |inr hr => exfalso; contradiction
·intro h
 cases h with
 |inl hp => intro x; apply Or.inl; exact hp x
 |inr hr => intro x; apply Or.inr; exact hr

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
apply Iff.intro
·intros hrp hr x
 specialize hrp x
 exact hrp hr
·intros h x hr
 exact h hr x

end Exercise02
 
-- Exercise 03
section Exercise03

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
have hpara : shaves barber barber ↔ ¬ shaves barber barber := h barber
apply Or.elim (Classical.em (shaves barber barber))
·intro h
 have hn_shaves_self : ¬ shaves barber barber := hpara.mp h
 contradiction
·intro h
 have h_shaves_self : shaves barber barber := hpara.mpr h
 contradiction

end Exercise03

-- Exercise 04

section Exercise04

def even (n : Nat) : Prop := ∃ m : Nat, n = 2 * m

def prime (n : Nat) : Prop := (n > 2) ∧ (∀ m : Nat, n % m = 0 → (m = 0 ∨ m = 1 ∨ m = n ))

def infinitely_many_primes : Prop := ∀ n : Nat, ∃ p : Nat, p > n ∧ prime p

def Fermat_prime (n : Nat) : Prop := prime n ∧ (∃ m : Nat, n = 2^(2^m) + 1) 

def infinitely_many_Fermat_primes : Prop := ∀ n : Nat, ∃ p : Nat, p > n ∧ Fermat_prime n

def goldbach_conjecture : Prop := ∀ n : Nat, n > 2 → ∃ p q : Nat, prime p ∧ prime q ∧ (n = p + q)  

def Goldbach's_weak_conjecture : Prop := ∀ n : Nat, (n % 2 = 1) ∧ n > 5 → ∃ p q r : Nat, prime p ∧ prime q ∧ prime r ∧ n = p + q + r    

def Fermat's_last_theorem : Prop := ∀ n : Nat, n > 2 → ¬ ∃ (a b c : Nat), a^n + b^n = c^n

end Exercise04

-- Exercise 05

section Exercise05

open Classical

example : (∃ x : α, r) → r := by
intro
|⟨a ,hr⟩ => assumption

example (a : α) : r → (∃ x : α, r) := by
intro hr
exact ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
apply Iff.intro
·intro
 |⟨a, hpa, hr⟩ => exact ⟨⟨a, hpa⟩, hr⟩
·intro
 |⟨⟨a, hpa⟩, hr⟩ => exact ⟨a, hpa, hr⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
apply Iff.intro
·intro
 |⟨a, Or.inl hpa⟩ => apply Or.inl; exact ⟨a, hpa⟩
 |⟨a, Or.inr hqa⟩ => apply Or.inr; exact ⟨a, hqa⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
apply Iff.intro
·intro h; simp; exact h
·intro h; simp at h; exact h

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
apply Iff.intro
·intro
 |⟨a, hpa⟩ => simp; exact ⟨a, hpa⟩
·simp
 intro a hpa
 exact ⟨a, hpa⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
apply Iff.intro
·intro h
 simp at h
 assumption
·intro h 
 simp
 assumption

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
apply Iff.intro
·intro h 
 simp at h
 assumption
·intro h
 simp
 assumption

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
apply Iff.intro
·intros h₁ h₂
 match h₂ with
 |⟨a, hpa⟩ => exact h₁ a hpa
·intros h₁ a hpa
 exact h₁ ⟨a, hpa⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
apply Iff.intro
·intros h₁ h₂
 match h₁ with
 |⟨a, ha⟩ => specialize h₂ a; exact ha h₂
·intro h
 apply Classical.by_contradiction
 simp
 intro h'
 have hp : ∀ (x : α), p x := by {
  intro a
  exact (h' a).1
 }
 specialize h hp
 apply absurd h (h' a).2
 
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
apply Iff.intro
·intros h hr
 match h with
 |⟨a, ha⟩ => specialize ha hr; use a; assumption
·intro h
 apply Or.elim (Classical.em r)
 ·intro hr
  match h hr with
  |⟨w, hw⟩ => use w; intro hr'; assumption
 ·intro hnr
  apply Classical.by_contradiction
  simp
  intro h'
  specialize h' a
  apply absurd h'.1 hnr

end Exercise05