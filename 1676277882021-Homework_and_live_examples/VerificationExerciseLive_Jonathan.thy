theory VerificationExerciseLive
  imports Main
begin


text \<open> The exercise describes the same Plutus contract for a Math bounty game
       but conditions for validating the transactions are the following:
      
       * Guess redeemer from dividing X by Y and time has minimum and maximum timestamps.
\<close>

section \<open> Data Types \<close>

datatype datum = Datum "int" "int" "nat" "nat"

fun numerator :: "datum \<Rightarrow> int" where "numerator (Datum x _ _ _) = x"
fun denominator :: "datum \<Rightarrow> int" where "denominator (Datum _ y _ _) = y"
fun startTime :: "datum \<Rightarrow> nat" where "startTime (Datum _ _ x _) = x"
fun endTime :: "datum \<Rightarrow> nat" where "endTime (Datum _ _ _ x) = x"

datatype redeemer = Redeemer "int"

fun guess :: "redeemer \<Rightarrow> int" where "guess (Redeemer x) = x"

datatype contxt = Context "nat"

fun transactionTime :: "contxt \<Rightarrow> nat" where "transactionTime (Context x) = x"

definition checkDeadline :: "datum \<Rightarrow> contxt \<Rightarrow> bool" where
"checkDeadline d c \<equiv> (startTime d) < (transactionTime c) \<and> (endTime d) > (transactionTime c)"

definition checkMod :: "datum \<Rightarrow> redeemer \<Rightarrow> bool" where
"checkMod d r \<equiv> (guess r) = ((numerator d) mod (denominator d))"

definition validateTx :: "datum \<Rightarrow> redeemer \<Rightarrow> contxt \<Rightarrow> bool" where
"validateTx d r c \<equiv> (checkMod d r) \<and> (checkDeadline d c)"

text \<open> Check that first interval is covered by the second one \<close>

section \<open> Verification \<close>

text \<open> Safety Property 1. 
       If a user knows the right guess and transaction is executed before the deadline then 
       the NFT can be minted.
     \<close>

text \<open> Safety Property 2. 
       Nobody without the right guess can get the NFT even if the time is right.
     \<close>

text \<open> Safety Property 3. 
       Nobody can unlock the NFT after the deadline or before start date.

       Must be valid. Should be proven with Isar.
     \<close>



end