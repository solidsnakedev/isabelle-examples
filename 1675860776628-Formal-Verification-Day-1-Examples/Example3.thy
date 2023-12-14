theory Example3
  imports Main

begin

text \<open> 
  Define a function count that counts the
  number of occurrences of an element in a list. Prove "count x xs <= length xs".
\<close>

fun eq :: "'a \<Rightarrow> 'a \<Rightarrow> nat" where
"eq x y = (if (x = y) then (1::nat) else (0::nat))"
(* "eq x y = If (x = y) (1::nat) (0::nat)" *)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0" |
"count x (y # xs) = eq x y + count x xs"

theorem exercise [simp]: "count x y \<le> length y"
  apply(induction y)
  apply(auto)
  done

end