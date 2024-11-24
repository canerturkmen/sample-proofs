import Mathlib

/--
PROBLEM:
Alicia earns 20 dollars per hour, of which $1.45\%$ is deducted to pay local taxes.  How many cents per hour of Alicia's wages are used to pay local taxes?
$\mathrm{(A) \ } 0.0029 \qquad \mathrm{(B) \ } 0.029 \qquad \mathrm{(C) \ } 0.29 \qquad \mathrm{(D) \ } 2.9 \qquad \mathrm{(E) \ } 29$

PROPOSED INFORMAL SOLUTION 1:
$20$ dollars is the same as $2000$ cents, and $1.45\%$ of $2000$ is $0.0145\times2000=29$ cents. $\Rightarrow\boxed{\mathrm{(E)}\ 29}$.
-/

-- 20 dollars equals (20 * 100) cents as every dollar equals 100 cents.
-- 1.45 per cent equals (1.45 / 100) by definition.
-- We must show (20 * 100) * (1.45 / 100) is equal to 29.
theorem algebra_1148 : ((20:ℝ) * 100) * (1.45 / 100) = 29 := by norm_num
