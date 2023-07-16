import Mathlib.Tactic

-- Examples

-- natural number division
example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)] -- deimplify the divides function
  use 8

-- integer division
example : (-2 : ℤ) ∣ 6 := by
 use (-3)
 norm_num

-- more complex examples
example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
match hab with
|⟨k, hk⟩ => use k * (a * k + 2); rw [hk]; ring

example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
match hbc with
|⟨y, hy⟩ => match hab with
            |⟨x, hx⟩ => use x ^ 2 * y
                        calc
                        c = b ^ 2 * y := by exact hy
                        _ = (a * x) ^ 2 * y := by rw [hx]
                        _ = a ^ 2 * (x ^ 2 * y) := by ring
 
example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  match h with 
  |⟨c, hc⟩ => use (y * c); rw [hc]; ring

example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  match hab with
  |⟨k, hk⟩ => 
  have hak : 0 < a * k := by {
    calc
    0 < b := by exact hb
    _ = a * k := by rw [hk]
  }
  apply by_contradiction
  intro ha
  simp at ha
  rw [ha] at hak
  rw [ha] at hk
  simp at hk
  rw [zero_mul] at hak
  contradiction


-- The real exercises

example (t : ℤ) : t ∣ 0 := by
use 0
simp

example : ¬(3 : ℤ) ∣ -10 := by
dsimp [(·∣·)]
intro
|⟨k, hk⟩ => sorry




            
 



