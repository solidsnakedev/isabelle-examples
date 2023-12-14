theory Example3
  imports Main

begin

text \<open> 
  Define a function count that counts the
  number of occurrences of an element in a list. Prove "count x xs <= length xs".
\<close>

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
one: "count x [] = 0" |
two: "count x (y # xs) = ((if x = y then 1 else 0) + count x xs)"

theorem length1: "count x xs \<le> length xs"
  apply(induction xs)
   using [[simp_trace]] apply(simp)
  apply(auto)
   done


theorem length[simp]: "count x xs \<le> length xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume assumption: "count x xs \<le> length xs"
  then show "count x (a # xs) \<le> length (a # xs)"
  proof(cases "x = a")
    case True
    hence "x = a" by simp
    hence eq1: "count x (a # xs) = 1 + count x xs" using two by auto
    hence "1 + count x xs \<le> length (a # xs)" using assumption by auto
    hence "count x (a # xs) \<le> length (a # xs)" using eq1 by simp
    then show ?thesis by auto
  next
    case False
    then show ?thesis sorry
  qed  
  qed
qed



end