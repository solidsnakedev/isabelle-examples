theory Example6
  imports Main

begin

text \<open>
  Starting from the type tree defined in the text, define a
  function contents that collects all values in a tree in a list,
  in any order, without removing duplicates. Then define a function sum_tree
  that sums up all values in a tree of natural numbers and
  prove sum_tree t = sum_list (contents t) (where sum_list is predefined).
\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) = a # (contents l @ contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = a + (sum_tree l) + (sum_tree r)"

theorem excersize [simp]: "sum_tree t = sum_list (contents t)"
apply(induction t)
apply(auto)
done

end