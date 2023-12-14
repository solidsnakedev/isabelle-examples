theory Example11
  imports Main

begin

text \<open> 
Exercise 2.11. Define arithmetic expressions in one variable over integers
(type int ) as a data type:
datatype exp = Var | Const int | Add exp exp | Mult exp exp
Define a function eval :: exp ⇒ int ⇒ int such that eval e x evaluates e at
the value x.

A polynomial can be represented as a list of coefficients, starting with the
constant. For example, [4, 2, − 1, 3] represents the polynomial 4+2x−x2 +3x3 .
Define a function evalp :: int list ⇒ int ⇒ int that evaluates a polynomial at
the given value. Define a function coeffs :: exp ⇒ int list that transforms an
expression into a polynomial. This may require auxiliary functions. Prove that
coeffs preserves the value of the expression: evalp (coeffs e) x = eval e x.
Hint: simplifying with the list of theorems algebra_simps takes care of
common algebraic properties of the arithmetic operators. You need to add these
theorems for certain proofs using "using algebra_simps" apply(simp) or
 write apply(simp add: algebra_simps)
\<close>

(* Start with this definition of an expression *)
datatype exp = Var | Const int | Add exp exp | Mult exp exp


end
