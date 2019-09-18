------------------------------ MODULE locking ------------------------------
EXTENDS Naturals, Sequences, TLC

\* Locks = [ Resource |-> Lock ]
\* Lock = [ Granted |-> RequestList, Pending |-> RequestList ]
\* RequestList = [ thread |-> ThreadNames, mode |-> mode ]

\* This matrix answers the question, "Is a lock request with mode 'Requested Mode' compatible with
\* an existing lock held in mode 'Granted Mode'?"
\*
\* | Requested Mode |                      Granted Mode                     |
\* |----------------|:------------:|:-------:|:--------:|:------:|:--------:|
\* |                |  MODE_NONE   | MODE_IS |  MODE_IX | MODE_S |  MODE_X  |
\* | MODE_IS        |      +       |    +    |     +    |    +   |          |
\* | MODE_IX        |      +       |    +    |     +    |        |          |
\* | MODE_S         |      +       |    +    |          |    +   |          |
\* | MODE_X         |      +       |         |          |        |          |

\* MODE_NONE is implied by an empty holder list.
CONSTANTS MODE_IS, MODE_IX, MODE_S, MODE_X
CompatibilityMatrix == {
\* IS
<<MODE_IS, MODE_IS>>,
<<MODE_IS, MODE_IX>>,
<<MODE_IS, MODE_S>> ,
\* IX
<<MODE_IX, MODE_IS>>,
<<MODE_IX, MODE_IX>>,
\* S
<<MODE_S, MODE_IS>>,
<<MODE_S, MODE_S>>
}

(* --algorithm locking
variables locks = [ DB1 |-> {}, DB2 |-> {} ];

macro lock(resource, mode)
begin
    await \/ locks[resource] = {}
          \/ \A request \in locks[resource]:
                <<request.mode, mode>> \in CompatibilityMatrix;
    \* self should have been defined in the scope.
    locks[resource] := locks[resource] \union {[thread |-> self, mode |-> mode]};
end macro;

macro unlock(resource)
begin
    assert \E request \in locks[resource]: request.thread = self;
    locks[resource] := { r \in locks[resource]: r.thread /= self };
end macro;


process ThreadA \in {"ThreadA"}
begin
LOCK1:   lock("DB1", MODE_IX);
LOCK2:   lock("DB2", MODE_X);
UNLOCK1: unlock("DB1");
UNLOCK2: unlock("DB2");
end process

process ThreadB \in {"ThreadB"}
begin
LOCK2:   lock("DB2", MODE_X);
LOCK1:   lock("DB1", MODE_IX);
UNLOCK1: unlock("DB1");
UNLOCK2: unlock("DB2");
end process

end algorithm *)


\* BEGIN TRANSLATION
\* Label LOCK1 of process ThreadA at line 39 col 5 changed to LOCK1_
\* Label LOCK2 of process ThreadA at line 39 col 5 changed to LOCK2_
\* Label UNLOCK1 of process ThreadA at line 48 col 5 changed to UNLOCK1_
\* Label UNLOCK2 of process ThreadA at line 48 col 5 changed to UNLOCK2_
VARIABLES locks, pc

vars == << locks, pc >>

ProcSet == ({"ThreadA"}) \cup ({"ThreadB"})

Init == (* Global variables *)
        /\ locks = [ DB1 |-> {}, DB2 |-> {} ]
        /\ pc = [self \in ProcSet |-> CASE self \in {"ThreadA"} -> "LOCK1_"
                                        [] self \in {"ThreadB"} -> "LOCK2"]

LOCK1_(self) == /\ pc[self] = "LOCK1_"
                /\ \/ locks["DB1"] = {}
                   \/ \A request \in locks["DB1"]:
                         <<request.mode, MODE_IX>> \in CompatibilityMatrix
                /\ locks' = [locks EXCEPT !["DB1"] = locks["DB1"] \union {[thread |-> self, mode |-> MODE_IX]}]
                /\ pc' = [pc EXCEPT ![self] = "LOCK2_"]

LOCK2_(self) == /\ pc[self] = "LOCK2_"
                /\ \/ locks["DB2"] = {}
                   \/ \A request \in locks["DB2"]:
                         <<request.mode, MODE_X>> \in CompatibilityMatrix
                /\ locks' = [locks EXCEPT !["DB2"] = locks["DB2"] \union {[thread |-> self, mode |-> MODE_X]}]
                /\ pc' = [pc EXCEPT ![self] = "UNLOCK1_"]

UNLOCK1_(self) == /\ pc[self] = "UNLOCK1_"
                  /\ Assert(\E request \in locks["DB1"]: request.thread = self,
                            "Failure of assertion at line 48, column 5 of macro called at line 57, column 10.")
                  /\ locks' = [locks EXCEPT !["DB1"] = { r \in locks["DB1"]: r.thread /= self }]
                  /\ pc' = [pc EXCEPT ![self] = "UNLOCK2_"]

UNLOCK2_(self) == /\ pc[self] = "UNLOCK2_"
                  /\ Assert(\E request \in locks["DB2"]: request.thread = self,
                            "Failure of assertion at line 48, column 5 of macro called at line 58, column 10.")
                  /\ locks' = [locks EXCEPT !["DB2"] = { r \in locks["DB2"]: r.thread /= self }]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]

ThreadA(self) == LOCK1_(self) \/ LOCK2_(self) \/ UNLOCK1_(self)
                    \/ UNLOCK2_(self)

LOCK2(self) == /\ pc[self] = "LOCK2"
               /\ \/ locks["DB2"] = {}
                  \/ \A request \in locks["DB2"]:
                        <<request.mode, MODE_X>> \in CompatibilityMatrix
               /\ locks' = [locks EXCEPT !["DB2"] = locks["DB2"] \union {[thread |-> self, mode |-> MODE_X]}]
               /\ pc' = [pc EXCEPT ![self] = "LOCK1"]

LOCK1(self) == /\ pc[self] = "LOCK1"
               /\ \/ locks["DB1"] = {}
                  \/ \A request \in locks["DB1"]:
                        <<request.mode, MODE_IX>> \in CompatibilityMatrix
               /\ locks' = [locks EXCEPT !["DB1"] = locks["DB1"] \union {[thread |-> self, mode |-> MODE_IX]}]
               /\ pc' = [pc EXCEPT ![self] = "UNLOCK1"]

UNLOCK1(self) == /\ pc[self] = "UNLOCK1"
                 /\ Assert(\E request \in locks["DB1"]: request.thread = self,
                           "Failure of assertion at line 48, column 5 of macro called at line 65, column 10.")
                 /\ locks' = [locks EXCEPT !["DB1"] = { r \in locks["DB1"]: r.thread /= self }]
                 /\ pc' = [pc EXCEPT ![self] = "UNLOCK2"]

UNLOCK2(self) == /\ pc[self] = "UNLOCK2"
                 /\ Assert(\E request \in locks["DB2"]: request.thread = self,
                           "Failure of assertion at line 48, column 5 of macro called at line 66, column 10.")
                 /\ locks' = [locks EXCEPT !["DB2"] = { r \in locks["DB2"]: r.thread /= self }]
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
\* Last modified Wed Sep 18 03:12:19 EDT 2019 by syzhou
\* Created Tue Sep 17 18:48:11 EDT 2019 by syzhou
