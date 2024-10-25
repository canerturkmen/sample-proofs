import Mathlib

open Finset

/-
If $a$ and $r$ are real numbers and $r \neq 1$, then
$$
\sum_{j=0}^{n} a r^{j}=a+a r+a r^{2}+\cdots+a r^{n}=\frac{a r^{n+1}-a}{r-1} .
$$
-/

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) :
    ∑ i ∈ range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) := by
  induction n with
  | zero =>
      simp
      calc
        a = a * (r - 1) / (r - 1) := Eq.symm (mul_div_cancel_right₀ a (sub_ne_zero_of_ne h))
        _ = (a * r - a) / (r - 1) := by ring
  | succ n h_ind =>
      rw[range_succ, sum_insert, h_ind]
      have : (r - 1) / (r - 1) = 1 := div_self (sub_ne_zero.mpr h)
      calc
        a * r ^ (n + 1) + (a * r ^ (n + 1) - a) / (r - 1)
          = a * r ^ (n + 1) * 1 + (a * r ^ (n + 1) - a) / (r - 1) := add_right_cancel_iff.mpr (by ring)
        _ = a * r ^ (n + 1) * (r - 1) / (r - 1) + (a * r ^ (n + 1) - a) / (r - 1) := by nth_rewrite 1 [← this]; ring
        _ = (a * r ^ (n + 1 + 1) - a) / (r - 1) := by ring
      exact not_mem_range_self


/-
Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then
(i ) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.
-/

example (n k : Nat) (h : k ≤ n) :
    (Nat.choose n 0 = 1) ∧ (Nat.choose n n = 1) ∧
    (Nat.choose n k = Nat.choose n (n-k)) :=
  And.intro (Nat.choose_zero_right n) (
    And.intro (Nat.choose_self n) (Eq.symm (Nat.choose_symm h))
  )

/-
We define a function recursively for all positive integers $n$ by $f(1)=1$,
$f(2)=5$, and for $n>2, f(n+1)=f(n)+2 f(n-1)$.

Show that $f(n)=$ $2^{n}+(-1)^{n}$, using the second
principle of mathematical induction.
-/


def f (n : ℕ+) : Nat :=
  match n with
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 5
  | ⟨k + 3, ih⟩ => f ⟨k + 2, by linarith⟩ + 2 * f ⟨k + 1, by linarith⟩
  termination_by n.val
  decreasing_by norm_num; norm_num

def g (n : ℕ+) : ℤ := 2^(n:ℕ) + (-1:ℤ)^(n:ℕ)

example (n : ℕ+) : f n = g n := by
  have hkm (_ m : ℕ+) (h : (k : ℕ+) → k < m → f k = g k) : (f m = g m) := by (
    match m with
    | ⟨1, _⟩ => simp[f.eq_def,g]
    | ⟨2, _⟩ => simp[f.eq_def,g]
    | ⟨x + 3, ih⟩ => (
        have hm2 : f ⟨x + 2, by linarith⟩ = g ⟨x + 2, by linarith⟩ := h ⟨x+2, by linarith⟩ (Subtype.mk_lt_mk.mpr (by norm_num))
        have hm1 : f ⟨x + 1, by linarith⟩ = g ⟨x + 1, by linarith⟩ := h ⟨x+1, by linarith⟩ (Subtype.mk_lt_mk.mpr (by norm_num))
        rw[f.eq_def]
        simp
        rw[hm1, hm2]
        simp[g]
        ring
    )
  )
  exact n.strongInductionOn (hkm n)
