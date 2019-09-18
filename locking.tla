------------------------------ MODULE locking ------------------------------
EXTENDS Naturals, Sequences, TLC

\* Locks = [ Resource |-> Lock ]
\* Lock = [ Granted |-> RequestList, Pending |-> RequestList ]
\* RequestList = <<ThreadNames>>

\*CONSTANTS DB1, DB2

(* --algorithm transfer
\*variables alice_account = 10, bob_account = 10, money \in 1..20,
\*          account_total = alice_account + bob_account;
variables locks = [ DB1 |-> {}, DB2 |-> {} ];

macro lock(resource)
begin
    await locks[resource] = {};
    \* self should have been defined in the scope.
    locks[resource] := {self};
end macro;

macro unlock(resource)
begin
    assert self \in locks[resource];
    locks[resource] := {};
end macro;


process ThreadA \in {"ThreadA"}
begin
LOCK1:   lock("DB1");
LOCK2:   lock("DB2");
UNLOCK1: unlock("DB1");
UNLOCK2: unlock("DB2");
end process

process ThreadB \in {"ThreadB"}
begin
LOCK2:   lock("DB2");
LOCK1:   lock("DB1");
UNLOCK1: unlock("DB1");
UNLOCK2: unlock("DB2");
end process

end algorithm *)


\* BEGIN TRANSLATION
\* Label LOCK1 of process ThreadA at line 17 col 5 changed to LOCK1_
\* Label LOCK2 of process ThreadA at line 17 col 5 changed to LOCK2_
\* Label UNLOCK1 of process ThreadA at line 24 col 5 changed to UNLOCK1_
\* Label UNLOCK2 of process ThreadA at line 24 col 5 changed to UNLOCK2_
VARIABLES locks, pc

vars == << locks, pc >>

ProcSet == ({"ThreadA"}) \cup ({"ThreadB"})

Init == (* Global variables *)
        /\ locks = [ DB1 |-> {}, DB2 |-> {} ]
        /\ pc = [self \in ProcSet |-> CASE self \in {"ThreadA"} -> "LOCK1_"
                                        [] self \in {"ThreadB"} -> "LOCK2"]

LOCK1_(self) == /\ pc[self] = "LOCK1_"
                /\ locks["DB1"] = {}
                /\ locks' = [locks EXCEPT !["DB1"] = {self}]
                /\ pc' = [pc EXCEPT ![self] = "LOCK2_"]

LOCK2_(self) == /\ pc[self] = "LOCK2_"
                /\ locks["DB2"] = {}
                /\ locks' = [locks EXCEPT !["DB2"] = {self}]
                /\ pc' = [pc EXCEPT ![self] = "UNLOCK1_"]

UNLOCK1_(self) == /\ pc[self] = "UNLOCK1_"
                  /\ Assert(self \in locks["DB1"], 
                            "Failure of assertion at line 24, column 5 of macro called at line 33, column 10.")
                  /\ locks' = [locks EXCEPT !["DB1"] = {}]
                  /\ pc' = [pc EXCEPT ![self] = "UNLOCK2_"]

UNLOCK2_(self) == /\ pc[self] = "UNLOCK2_"
                  /\ Assert(self \in locks["DB2"], 
                            "Failure of assertion at line 24, column 5 of macro called at line 34, column 10.")
                  /\ locks' = [locks EXCEPT !["DB2"] = {}]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]

ThreadA(self) == LOCK1_(self) \/ LOCK2_(self) \/ UNLOCK1_(self)
                    \/ UNLOCK2_(self)

LOCK2(self) == /\ pc[self] = "LOCK2"
               /\ locks["DB2"] = {}
               /\ locks' = [locks EXCEPT !["DB2"] = {self}]
               /\ pc' = [pc EXCEPT ![self] = "LOCK1"]

LOCK1(self) == /\ pc[self] = "LOCK1"
               /\ locks["DB1"] = {}
               /\ locks' = [locks EXCEPT !["DB1"] = {self}]
               /\ pc' = [pc EXCEPT ![self] = "UNLOCK1"]

UNLOCK1(self) == /\ pc[self] = "UNLOCK1"
                 /\ Assert(self \in locks["DB1"], 
                           "Failure of assertion at line 24, column 5 of macro called at line 41, column 10.")
                 /\ locks' = [locks EXCEPT !["DB1"] = {}]
                 /\ pc' = [pc EXCEPT ![self] = "UNLOCK2"]

UNLOCK2(self) == /\ pc[self] = "UNLOCK2"
                 /\ Assert(self \in locks["DB2"], 
                           "Failure of assertion at line 24, column 5 of macro called at line 42, column 10.")
                 /\ locks' = [locks EXCEPT !["DB2"] = {}]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]

ThreadB(self) == LOCK2(self) \/ LOCK1(self) \/ UNLOCK1(self)
                    \/ UNLOCK2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {"ThreadA"}: ThreadA(self))
           \/ (\E self \in {"ThreadB"}: ThreadB(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Sep 18 01:55:20 EDT 2019 by syzhou
\* Created Tue Sep 17 18:48:11 EDT 2019 by syzhou
