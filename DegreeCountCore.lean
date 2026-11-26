import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators
namespace DegreeCount

/-- A binary walk of odd period has a nonflipping step. -/
theorem odd_period_exists_equal (k : ℕ) (f : ℕ → Bool)
    (hp : f (2*k+1) = f 0) : ∃ j < 2*k+1, f (j+1) = f j := by
  by_contra h
  have step : ∀ j < 2*k+1, f (j+1) = !f j := by
    intro j hj
    have hn : f (j+1) ≠ f j := fun he => h ⟨j, hj, he⟩
    cases h1 : f j <;> cases h2 : f (j+1) <;> simp_all
  have even : ∀ j ≤ k, f (2*j) = f 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have h1 : 2*j < 2*k+1 := by omega
      have h2 : 2*j+1 < 2*k+1 := by omega
      rw [show 2*(j+1) = (2*j+1)+1 by omega, step _ h2, step _ h1, ih (by omega)]
      simp
  have hh := step (2*k) (by omega)
  rw [even k (le_refl k), hp] at hh
  cases hf : f 0 <;> simp [hf] at hh

/-- The odd torus condition used to select compatible arcs. -/
theorem odd_torus_compatibility (a b : ℕ) (A : ℕ → ℕ → Bool)
    (hr : ∀ i j, A (i+(2*a+1)) j = A i j)
    (hc : ∀ i j, A i (j+(2*b+1)) = A i j) :
    ∃ i j : ℕ, A (i+1) j = A i (j+1) := by
  let L := (2*a+1)*(2*b+1)
  have row : ∀ k : ℕ, A ((2*a+1)*k) 0 = A 0 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, hr, ih]
  have col : ∀ k : ℕ, A 0 ((2*b+1)*k) = A 0 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, hc, ih]
  have hL : L = 2*(2*a*b+a+b)+1 := by dsimp [L]; ring
  let f : ℕ → Bool := fun t => A t (L-t)
  have hp : f L = f 0 := by
    dsimp [f]
    rw [Nat.sub_self]
    have hh : A L 0 = A 0 0 := row (2*b+1)
    have hh' : A 0 L = A 0 0 := by
      dsimp [L]
      rw [Nat.mul_comm (2*a+1) (2*b+1)]
      exact col (2*a+1)
    exact hh.trans hh'.symm
  have hp' : f (2*(2*a*b+a+b)+1) = f 0 := by rw [← hL]; exact hp
  obtain ⟨t, ht, he⟩ := odd_period_exists_equal (2*a*b+a+b) f hp'
  have ht' : t < L := by omega
  change A (t+1) (L-(t+1)) = A t (L-t) at he
  exact ⟨t, L-(t+1), by simpa only [show L-(t+1)+1 = L-t by omega] using he⟩

section Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]
def eye (a i : V) : ℤ := if i=a then 1 else 0

def delta (a b c e i j : V) : ℤ := (eye a i-eye c i)*(eye e j-eye b j)

theorem eye_sum (a : V) : ∑ i, eye a i = 1 := by simp [eye]

theorem delta_row (a b c e i : V) : ∑ j, delta a b c e i j = 0 := by
  simp only [delta, ← Finset.mul_sum, Finset.sum_sub_distrib, eye_sum, sub_self, mul_zero]

theorem delta_col (a b c e j : V) : ∑ i, delta a b c e i j = 0 := by
  simp only [delta, ← Finset.sum_mul, Finset.sum_sub_distrib, eye_sum, sub_self, zero_mul]

/-- The empty-pair switch preserves every row and column margin. -/
theorem switch_margins (A : V → V → ℤ) (a b c e : V) :
    (∀ i, (∑ j, (A i j + delta a b c e i j)) = ∑ j, A i j) ∧
    (∀ j, (∑ i, (A i j + delta a b c e i j)) = ∑ i, A i j) := by
  constructor
  · intro i; rw [Finset.sum_add_distrib, delta_row, add_zero]
  · intro j; rw [Finset.sum_add_distrib, delta_col, add_zero]

/-- Inverse of the local empty-pair switch, pointwise. -/
theorem switch_inverse (A : V → V → ℤ) (a b c e i j : V) :
    A i j + delta a b c e i j + delta a e c b i j = A i j := by
  unfold delta; ring

/-- Full-pair repair is the reversed/complemented empty-pair repair. -/
theorem full_switch_delta (a b c e i j : V) :
    delta b c e a i j = - delta a b c e j i := by
  unfold delta; ring
end Matrix

/-- Scalar AM-GM conversion giving the conjecture's constant one. -/
theorem conjecture_scalar (x : ℝ) : 8*x ≤ (2+x)^2 := by nlinarith [sq_nonneg (x-2)]

theorem fourth_le_pow_four_aux (k : ℕ) : (4+k)^4 ≤ 4^(4+k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    calc
      (4+(k+1))^4 ≤ 4*(4+k)^4 := by
        nlinarith [Nat.zero_le (k^2), Nat.zero_le (k^3), Nat.zero_le (k^4)]
      _ ≤ 4*4^(4+k) := Nat.mul_le_mul_left 4 ih
      _ = 4^(4+(k+1)) := by rw [show 4+(k+1)=4+k+1 by omega, pow_succ]; ring

theorem fourth_le_pow_four (s : ℕ) (hs : 4 ≤ s) : s^4 ≤ 4^s := by
  have h : s = 4+(s-4) := by omega
  nth_rw 1 2 [h]
  exact fourth_le_pow_four_aux (s-4)

#print axioms odd_period_exists_equal
#print axioms odd_torus_compatibility
#print axioms switch_margins
#print axioms switch_inverse
#print axioms full_switch_delta
#print axioms conjecture_scalar
#print axioms fourth_le_pow_four
end DegreeCount
