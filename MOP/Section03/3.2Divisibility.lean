import Mathlib.Tactic

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
 


 
            
 



