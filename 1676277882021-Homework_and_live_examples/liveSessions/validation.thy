theory validation
  imports Main
begin

(*
mathBountyValidator :: MathBountyDatum -> Integer -> ScriptContext -> Bool
mathBountyValidator datum x sContext =  traceIfFalse "Wrong guess!" ((mBounty datum) == x*x) &&
                                        traceIfFalse "Deadline passed!" deadlineReached
*)

(*
1. if r * r == datum transaction should be unlocked, r is an integer
2. we shouldn't unlock the transaction if r * r != datum, r is an integer    
3. we should be able to unlock the transaction before the deadline 
4. we shouldn't be able to unlock the transaction after(> or \<ge>) the deadline
*)

section \<open>Model\<close>

text \<open>Datum\<close>

datatype datum = Datum "int" "nat"

fun secretOf :: "datum \<Rightarrow> int" where "secretOf (Datum x t) = x"
fun deadlineOf :: "datum \<Rightarrow> nat set" where "deadlineOf (Datum x t) = atMost t"

text \<open>Redeemer\<close>
datatype redeemer = Redeemer "int"

fun guessOf :: "redeemer \<Rightarrow> int" where "guessOf (Redeemer x) = x"

text \<open>Context\<close>
datatype contxt = Context "nat" 

fun validTime :: "contxt \<Rightarrow> nat set" where "validTime (Context x) = atMost x"


section \<open> Implementation \<close>

definition Limit :: "int" where "Limit \<equiv> 2^63"
definition Domain :: "int set" where "Domain \<equiv> {-Limit..<Limit}"

definition calcOverflow :: "int \<Rightarrow> int" where
"calcOverflow x \<equiv> if x \<in> Domain then x else (SOME y . y \<in> Domain)"

lemma "(calcOverflow x) \<in> Domain"
  apply(cases "x \<in> Domain")
   apply (simp add: calcOverflow_def)
  using calcOverflow_def oops

definition sqOverflow :: "int \<Rightarrow> int" where "sqOverflow x \<equiv> calcOverflow (x * x)"

definition sq :: "int \<Rightarrow> int" where "sq x \<equiv> x * x"

definition checkGuess :: "(int \<Rightarrow> int) \<Rightarrow> datum \<Rightarrow> redeemer \<Rightarrow> bool" where
"checkGuess op d r \<equiv> (op (guessOf r)) = (secretOf d)"

definition checkDeadline :: "datum \<Rightarrow> contxt \<Rightarrow> bool" where
"checkDeadline d c \<equiv> (validTime c) \<subseteq> (deadlineOf d)"

definition validateTx :: "(int \<Rightarrow> int) \<Rightarrow> datum \<Rightarrow> redeemer \<Rightarrow> contxt \<Rightarrow> bool" where
"validateTx op d r c \<equiv> (checkGuess op d r) \<and> (checkDeadline d c)"

section \<open> Implementation \<close>

text \<open> if r * r == datum transaction should be unlocked, r is an integer \<close>
theorem req13: "(sq r = s \<and> t \<le> d) \<longrightarrow> validateTx sq (Datum s d) (Redeemer r) (Conext t)" 
  sorry

theorem req13Overflow: "(sq r = s \<and> t \<le> d) \<longrightarrow> validateTx sqOverflow (Datum s d) (Redeemer r) (Conext t)" 
  sorry

text \<open>we shouldn't unlock the transaction if r * r != datum, r is an integer\<close>
theorem req2: "(sq r \<noteq> s \<and> t \<le> d) \<longrightarrow> \<not>validateTx sq (Datum s d) (Redeemer r) (Conext t)" 
  sorry

theorem req2Overflow: "(sq r \<noteq> s \<and> t \<le> d) \<longrightarrow> \<not>validateTx sqOverflow (Datum s d) (Redeemer r) (Conext t)" 
  sorry

(* we shouldn't be able to unlock the transaction after(> or \<ge>) the deadline  *)
theorem req3w: "(sq r = s \<and> t > d) \<longrightarrow> \<not>validateTx sq (Datum s d) (Redeemer r) (Conext t)" 
  sorry

end