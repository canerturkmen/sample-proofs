import Mathlib

-- Function to compute the sum of digits of a number, a.k.a. ♣
@[simp] def sumdigits (n : ℕ) : ℕ := (Nat.digits 10 n).sum

set_option maxHeartbeats 0

/--
PROBLEM:
Let $\clubsuit(x)$ denote the sum of the digits of the positive integer $x$.
For example, $\clubsuit(8)=8$ and $\clubsuit(123)=1+2+3=6$. For how many
two-digit values of $x$ is $\clubsuit(\clubsuit(x))=3$?

$\textbf{(A) } 3 \qquad\textbf{(B) } 4 \qquad\textbf{(C) } 6 \qquad\textbf{(D) }
9 \qquad\textbf{(E) } 10$

PROPOSED INFORMAL SOLUTION 1:
Let $y=\clubsuit (x)$. Since $x \leq 99$, we have $y \leq 18$.
Thus if $\clubsuit (y)=3$, then $y=3$ or $y=12$.
The 3 values of $x$ for which $\clubsuit (x)=3$ are 12, 21, and 30,
and the 7 values of $x$ for which $\clubsuit (x)=12$ are 39, 48, 57, 66, 75, 84,
and 93. There are $\boxed{E=10}$ values in all.
-/
theorem numbertheory_1147 {A : Finset ℕ}
  (h : ∀ x, (x ∈ A ↔ (Nat.digits 10 x).length = 2 ∧ sumdigits (sumdigits x) = 3))
  : A.card = 10 := by

  have hA : ∀ x ∈ A, (Nat.digits 10 x).length = 2 ∧ sumdigits (sumdigits x) = 3 := by
    intro y hy
    exact (h y).mp hy

  -- note $x ≥ 10$
  have h_x_ge (x : ℕ) : x ∈ A → x ≥ 10 := by
    intro hx
    have : (Nat.digits 10 x).length = 2 := (hA x hx).left
    -- simp
    by_contra hc
    simp at hc
    interval_cases x <;> norm_num at this

  -- Since $x \leq 99$,
  have h_x_le (x : ℕ) : x ∈ A → x ≤ 99 := by
    intro hx
    have hlen : (Nat.digits 10 x).length = 2 := (hA x hx).left
    have h_ne_0 : x ≠ 0 := by
      have : x ≥ 10 := h_x_ge x hx
      by_contra hc
      rw [hc] at this
      contradiction
    have : Nat.log 10 x + 1 = 2 := by
      rw [← hlen]
      apply Eq.symm
      exact Nat.digits_len 10 x (by norm_num) h_ne_0
    have : x < 10^2 := Nat.lt_pow_of_log_lt (by norm_num) (by linarith)
    norm_num at this
    exact Nat.le_of_lt_succ this

  -- we have $y \leq 18$.
  have h_sum_digits_le (x : ℕ) : (Nat.digits 10 x).length = 2 → sumdigits x ≤ 18 := by
    intro hx
    dsimp
    -- every digit is less than or equal to 9 in base 10
    have hle9 : ∀ d ∈ Nat.digits 10 x, d ≤ 9 :=
      fun d hd => Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hd)
    -- This applies to all digits in the digits of x, which are not more than 2 digits
    have : List.Forall₂ (fun a b => a ≤ b) (Nat.digits 10 x) [9, 9] := by
      apply List.forall₂_iff_get.mpr
      constructor
      . simp; exact hx
      . intro i h1 _
        simp [hx] at h1
        interval_cases i
        . exact hle9 (Nat.digits 10 x)[0] (by apply List.get_mem)
        . exact hle9 (Nat.digits 10 x)[1] (by apply List.get_mem)
    have : (Nat.digits 10 x).sum ≤ [9, 9].sum := by exact List.Forall₂.sum_le_sum this
    simp at this
    exact this

  -- Thus if $\clubsuit (y)=3$, then $y=3$ or $y=12$.
  have h_possible_y : ∀ x ∈ A, sumdigits x = 3 ∨ sumdigits x = 12 := by
    intro x hx
    let y := sumdigits x
    have hyle : y ≤ 18 := h_sum_digits_le x (hA x hx).left
    have hsumy : sumdigits y = 3 := (hA x hx).right
    have : y ≠ 3 ∧ y ≠ 12 → False := by
      intro hneq
      interval_cases y <;> simp at hsumy <;> contradiction
    simp at this
    exact Decidable.or_iff_not_imp_left.mpr this

  -- The 3 values of $x$ for which $\clubsuit (x)=3$ are 12, 21, and 30,
  let possible_x_sum3 : Finset ℕ := {12, 21, 30}
  have h_possible_x_sum3 : ∀ x ∈ A, sumdigits x = 3 → x ∈ possible_x_sum3 := by
    intro x hx
    have : x ≤ 99 := h_x_le x hx
    have : x ≥ 10 := h_x_ge x hx
    simp [possible_x_sum3]
    intro hsum
    by_contra hcontra
    simp at hcontra
    interval_cases x <;> norm_num at hsum <;> simp at hcontra

  -- and the 7 values of $x$ for which $\clubsuit (x)=12$ are 39, 48, 57, 66, 75, 84, and 93.
  let possible_x_sum12 : Finset ℕ := {39, 48, 57, 66, 75, 84, 93}
  have h_possible_x_sum12 : ∀ x ∈ A, sumdigits x = 12 → x ∈ possible_x_sum12 := by
    intro x hx
    have : x ≤ 99 := h_x_le x hx
    have : x ≥ 10 := h_x_ge x hx
    simp [possible_x_sum12]
    intro hsum
    by_contra hcontra
    simp at hcontra
    interval_cases x <;> norm_num at hsum <;> simp at hcontra

  -- so these are all the possible results
  let possible_x : Finset ℕ := possible_x_sum3 ∪ possible_x_sum12
  have h_possible_x : ∀ x ∈ A, x ∈ possible_x := by
    intro x hx
    have hy : sumdigits x = 3 ∨ sumdigits x = 12 := h_possible_y x hx
    cases hy with
    | inl hsum3 =>
      -- Case: `sumdigits x = 3`
      apply Finset.mem_union_left
      exact h_possible_x_sum3 x hx hsum3
    | inr hsum12 =>
      -- Case: `sumdigits x = 12`
      apply Finset.mem_union_right
      exact h_possible_x_sum12 x hx hsum12

  -- We finally need to show the set of possible xs we found indeed cover A
  have h_set_eq: A = possible_x := by
    apply Finset.ext_iff.mpr
    intro x
    constructor
    . exact fun a ↦ h_possible_x x a
    . intro hx
      have hval : x ∈ possible_x_sum3 ∨ x ∈ possible_x_sum12 := Finset.mem_union.mp hx
      have hbound : x ≤ 93 := by
        calc
          x ≤ Finset.max' possible_x (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_empty_of_mem hx)) := Finset.le_max' possible_x x hx
          _ = 93 := rfl
      have : (Nat.digits 10 x).length = 2 ∧ sumdigits (sumdigits x) = 3 := by
        interval_cases x <;> simp <;> contradiction
      exact (h x).mpr this

  have : possible_x.card = 10 := rfl
  rw[← h_set_eq] at this
  exact this
