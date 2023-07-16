import Mathlib.Tactic

example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by
calc
  a = 2 * b + 5 := by exact h1
  _ = 2 * 3 + 5 := by rw [h2]
  _ = 11 := by ring

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
calc
  x = (x + 4) - 4 := by ring
  _ = 2 - 4 := by rw [h1]
  _ = -2 := by ring

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
calc
  a = (a - 5 * b) + 5 * b := by ring
  _ = 4 + 5 * (b + 2) - 10 := by rw [h1]; ring
  _ = 4 + 5 * 3 - 10 := by rw [h2]
  _ = 9 := by ring

example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
calc
  w = ((3 * w + 1) / 3) - (1 / 3) := by ring
  _ = (4 / 3) - (1 / 3) := by rw [h1]
  _ = 1 := by ring

example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 := by
calc
  x = 2 * x + 3 - x - 3 := by ring
  _ = x - x - 3 := by rw [h1]
  _ = -3 := by ring

example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 := by
calc
  x = (2 * x - y) + (y - x + 1) - 1 := by ring
  _ = 4 + 2 - 1 := by rw [h1, h2]
  _ = 5 := by ring

example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 := by
calc
  u = ((u + 2 * v) + (u - 2 * v)) / 2 := by ring
  _ = (4 + 6) / 2 := by rw [h1, h2]
  _ = 5 := by ring

example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 := by
calc
  x = (3 * (x + y) + (5 * x - 3 * y)) / 8 := by ring
  _ = (3 * 4 + 4) / 8 := by rw [h1, h2]
  _ = 2 := by ring

example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 := by
calc
  a ^ 2 - a + 3 = (a - 3) ^ 2 + 5 * (a - 3) + 9 := by ring
  _ = (2 * b) ^ 2 + 5 * (2 * b) + 9 := by rw [h1]
  _ = 4 * b ^ 2 + 10 * b + 9 := by ring

example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 := by
calc
  z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = (z ^ 2 - z + 1) * (z ^ 2 - 2) + 3 := by ring
  _ = (z ^ 2 - z + 1) * 0 + 3 := by rw [h1]
  _ = 3 := by ring

