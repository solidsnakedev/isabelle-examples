theory Example2
  imports Main

begin

text \<open>
  Exercise:
  Prove that add
  is associative and commutative. Define a recursive function double :: nat )
  nat and prove: double m = add m m.
\<close>

definition addS :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"addS x y \<equiv> x + y"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
one: "add x 0 = x" |
two: "add x (Suc y) = Suc (add x y)"

definition doubleS :: "nat \<Rightarrow> nat" where
"doubleS x \<equiv> x + x"

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc x) = Suc (Suc (double x))"

value "double 4"

lemma zero: "add 0 x = x"
  apply(induction x)
   apply(auto)
  done

lemma succ1: "Suc (add x y) = add (Suc x) y"
  apply(induction y)
   apply(auto)
  done

theorem add_comm: "add m n = add n m"
  apply(induction n)
  apply(simp add: zero)
  using succ1 [[simp_trace]] apply(simp)
  done

lemma succ2: "add (Suc x) y = Suc (add x y)"
  apply(induction y)
   apply(auto)
  done

theorem add_ass: "add (add x y) z = add x (add y z)"
  apply(induction y)
  using zero apply(auto)
  using add_comm apply(simp)
  done

theorem "doubleS m = addS m m"
  using doubleS_def addS_def by simp

theorem "double m = add m m"
proof(induction m)
  case 0
  then show ?case by simp
next
  case ind_case: (Suc m)
  have "double (Suc m) = Suc (Suc (double m))" by simp
  hence part1: "double (Suc m) = Suc (Suc (add m m))" using ind_case by simp
  have "add (Suc m) (Suc m) = Suc (add (Suc m) m)" by simp
  hence part2: "add (Suc m) (Suc m) = Suc (Suc (add m m))" using succ1 by simp
  thus "double (Suc m) = add (Suc m) (Suc m)" using part1 by simp
qed

(*apply(induction m)
   apply(auto)
  using succ1 apply(simp)
  done *)



end