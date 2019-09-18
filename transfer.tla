------------------------------ MODULE transfer ------------------------------

EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money \in 1..20,
          account_total = alice_account + bob_account;

begin
Transfer:
  if alice_account >= money then
    Substract_Add_Account: alice_account := alice_account - money;
                       bob_account := bob_account + money;
end if;
ASSERT_C: assert alice_account >= 0;

end algorithm *)


\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, money, account_total, pc

vars == << alice_account, bob_account, money, account_total, pc >>

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ money \in 1..20
        /\ account_total = alice_account + bob_account
        /\ pc = "Transfer"

Transfer == /\ pc = "Transfer"
            /\ IF alice_account >= money
                  THEN /\ pc' = "Substract_Add_Account"
                  ELSE /\ pc' = "ASSERT_C"
            /\ UNCHANGED << alice_account, bob_account, money, account_total >>

Substract_Add_Account == /\ pc = "Substract_Add_Account"
                         /\ alice_account' = alice_account - money
                         /\ bob_account' = bob_account + money
                         /\ pc' = "ASSERT_C"
                         /\ UNCHANGED << money, account_total >>

ASSERT_C == /\ pc = "ASSERT_C"
            /\ Assert(alice_account >= 0, 
                      "Failure of assertion at line 15, column 11.")
            /\ pc' = "Done"
            /\ UNCHANGED << alice_account, bob_account, money, account_total >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Transfer \/ Substract_Add_Account \/ ASSERT_C
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

MoneyNotNegative == money >= 0
MoneyInvariant == alice_account + bob_account = account_total

=============================================================================
\* Modification History
\* Last modified Tue Sep 17 14:29:14 EDT 2019 by syzhou
\* Created Tue Sep 17 14:20:23 EDT 2019 by syzhou
