theory Example4
  imports Main

begin

text \<open> 
  Define a recursive function snoc that appends an element to the end of a list.
  With the help of snoc define a recursive function reverse that reverses a list.
  Prove reverse (reverse xs) = xs.
\<close>

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = x # []" |
"snoc (x # xs) y = x # (snoc xs y)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # []) = snoc [] x" |
"reverse (x # xs) = snoc (reverse xs) x"

theorem t1 [simp]: "reverse (reverse xs) = xs"

end
