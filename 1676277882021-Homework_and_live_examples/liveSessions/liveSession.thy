theory VerificationExerciseLive
  imports Main
begin


text \<open> The exercise describes the same Plutus contract for a Math bounty game
       but conditions for validating the transactions are the following:
      
       * Guess redeemer from dividing X by Y and time has minimum and maximum timestamps.
\<close>

section \<open> Data Types \<close>

section \<open> Model \<close>

text \<open> Check that first interval is covered by the second one \<close>

section \<open> Verification \<close>

text \<open> Safety Property 1. 
       If a user knows the right guess and transaction is executed before the deadline then 
       the NFT can be minted.
     \<close>

text \<open> Safety Property 2. 
       Nobody without the right 