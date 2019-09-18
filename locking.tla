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

AllResources == { "DB1", "DB2" }

(* --algorithm locking
variables locks = [ r \in AllResources |-> [granted |-> {}, pending |-> {}]];


macro unlock(resource)
begin
    assert \E request \in locks[resource].granted: request.thread = self;
    locks[resource].granted := { r \in locks[resource].granted: r.thread /= self };
end macro;


procedure lock(resource, mode) begin
try_lock:
    locks[resource].pending := locks[resource].pending \union {[thread |-> self, mode |-> mode]};
lock_wait:
    await \/ locks[resource].granted = {}
          \/ \A request \in locks[resource].granted:
                <<request.mode, mode>> \in CompatibilityMatrix;
lock_granted:
    \* self should have been defined in the scope.
    locks[resource] := [ pending |-> { r \in locks[resource].pending: r.thread /= self },
                         granted |-> locks[resource].granted \union {[thread |-> self, mode |-> mode]} ];
    return;
end procedure;

process ThreadA \in {"ThreadA"}
begin
LOCK1:   call lock("DB1", MODE_IX);
LOCK2:   call lock("DB2", MODE_X);
UNLOCK1: unlock("DB1");
UNLOCK2: unlock("DB2");
end process

process ThreadB \in {"ThreadB"}
begin
LOCK2:   call lock("DB2", MODE_X);
LOCK1:   call lock("DB1", MODE_IX);
UNLOCK1: unlock("DB1");
UNLOCK2: unlock("DB2");
end process

end algorithm *)


\* BEGIN TRANSLATION
\* Label LOCK1 of process ThreadA at line 63 col 10 changed to LOCK1_
\* Label LOCK2 of process ThreadA at line 64 col 10 changed to LOCK2_
\* Label UNLOCK1 of process ThreadA at line 42 col 5 changed to UNLOCK1_
\* Label UNLOCK2 of process ThreadA at line 42 col 5 changed to UNLOCK2_
CONSTANT defaultInitValue
VARIABLES locks, pc, stack, resource, mode

vars == << locks, pc, stack, resource, mode >>

ProcSet == ({"ThreadA"}) \cup ({"ThreadB"})

Init == (* Global variables *)
        /\ locks = [ r \in AllResources |-> [granted |-> {}, pending |-> {}]]
        (* Procedure lock *)
        /\ resource = [ self \in ProcSet |-> defaultInitValue]
        /\ mode = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {"ThreadA"} -> "LOCK1_"
                                        [] self \in {"ThreadB"} -> "LOCK2"]

try_lock(self) == /\ pc[self] = "try_lock"
                  /\ locks' = [locks EXCEPT ![resource[self]].pending = locks[resource[self]].pending \union {[thread |-> self, mode |-> mode[self]]}]
                  /\ pc' = [pc EXCEPT ![self] = "lock_wait"]
                  /\ UNCHANGED << stack, resource, mode >>

lock_wait(self) == /\ pc[self] = "lock_wait"
                   /\ \/ locks[resource[self]].granted = {}
                      \/ \A request \in locks[resource[self]].granted:
                            <<request.mode, mode[self]>> \in CompatibilityMatrix
                   /\ pc' = [pc EXCEPT ![self] = "lock_granted"]
                   /\ UNCHANGED << locks, stack, resource, mode >>

lock_granted(self) == /\ pc[self] = "lock_granted"
                      /\ locks' = [locks EXCEPT ![resource[self]] = [ pending |-> { r \in locks[resource[self]].pending: r.thread /= self },
                                                                      granted |-> locks[resource[self]].granted \union {[thread |-> self, mode |-> mode[self]]} ]]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ resource' = [resource EXCEPT ![self] = Head(stack[self]).resource]
                      /\ mode' = [mode EXCEPT ![self] = Head(stack[self]).mode]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

lock(self) == try_lock(self) \/ lock_wait(self) \/ lock_granted(self)

LOCK1_(self) == /\ pc[self] = "LOCK1_"
                /\ /\ mode' = [mode EXCEPT ![self] = MODE_IX]
                   /\ resource' = [resource EXCEPT ![self] = "DB1"]
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                            pc        |->  "LOCK2_",
                                                            resource  |->  resource[self],
                                                            mode      |->  mode[self] ] >>
                                                        \o stack[self]]
                /\ pc' = [pc EXCEPT ![self] = "try_lock"]
                /\ locks' = locks

LOCK2_(self) == /\ pc[self] = "LOCK2_"
                /\ /\ mode' = [mode EXCEPT ![self] = MODE_X]
                   /\ resource' = [resource EXCEPT ![self] = "DB2"]
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                            pc        |->  "UNLOCK1_",
                                                            resource  |->  resource[self],
                                                            mode      |->  mode[self] ] >>
                                                        \o stack[self]]
                /\ pc' = [pc EXCEPT ![self] = "try_lock"]
                /\ locks' = locks

UNLOCK1_(self) == /\ pc[self] = "UNLOCK1_"
                  /\ Assert(\E request \in locks["DB1"].granted: request.thread = self,
                            "Failure of assertion at line 42, column 5 of macro called at line 65, column 10.")
                  /\ locks' = [locks EXCEPT !["DB1"].granted = { r \in locks["DB1"].granted: r.thread /= self }]
                  /\ pc' = [pc EXCEPT ![self] = "UNLOCK2_"]
                  /\ UNCHANGED << stack, resource, mode >>

UNLOCK2_(self) == /\ pc[self] = "UNLOCK2_"
                  /\ Assert(\E request \in locks["DB2"].granted: request.thread = self,
                            "Failure of assertion at line 42, column 5 of macro called at line 66, column 10.")
                  /\ locks' = [locks EXCEPT !["DB2"].granted = { r \in locks["DB2"].granted: r.thread /= self }]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << stack, resource, mode >>

ThreadA(self) == LOCK1_(self) \/ LOCK2_(self) \/ UNLOCK1_(self)
                    \/ UNLOCK2_(self)

LOCK2(self) == /\ pc[self] = "LOCK2"
               /\ /\ mode' = [mode EXCEPT ![self] = MODE_X]
                  /\ resource' = [resource EXCEPT ![self] = "DB2"]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                           pc        |->  "LOCK1",
                                                           resource  |->  resource[self],
                                                           mode      |->  mode[self] ] >>
                                                       \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "try_lock"]
               /\ locks' = locks

LOCK1(self) == /\ pc[self] = "LOCK1"
               /\ /\ mode' = [mode EXCEPT ![self] = MODE_IX]
                  /\ resource' = [resource EXCEPT ![self] = "DB1"]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                           pc        |->  "UNLOCK1",
                                                           resource  |->  resource[self],
                                                           mode      |->  mode[self] ] >>
                                                       \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "try_lock"]
               /\ locks' = locks

UNLOCK1(self) == /\ pc[self] = "UNLOCK1"
                 /\ Assert(\E request \in locks["DB1"].granted: request.thread = self,
                           "Failure of assertion at line 42, column 5 of macro called at line 73, column 10.")
                 /\ locks' = [locks EXCEPT !["DB1"].granted = { r \in locks["DB1"].granted: r.thread /= self }]
                 /\ pc' = [pc EXCEPT ![self] = "UNLOCK2"]
                 /\ UNCHANGED << stack, resource, mode >>

UNLOCK2(self) == /\ pc[self] = "UNLOCK2"
                 /\ Assert(\E request \in locks["DB2"].granted: request.thread = self,
                           "Failure of assertion at line 42, column 5 of macro called at line 74, column 10.")
                 /\ locks' = [locks EXCEPT !["DB2"].granted = { r \in locks["DB2"].granted: r.thread /= self }]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << stack, resource, mode >>

ThreadB(self) == LOCK2(self) \/ LOCK1(self) \/ UNLOCK1(self)
                    \/ UNLOCK2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: lock(self))
           \/ (\E self \in {"ThreadA"}: ThreadA(self))
           \/ (\E self \in {"ThreadB"}: ThreadB(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Sep 18 03:56:58 EDT 2019 by syzhou
\* Created Tue Sep 17 18:48:11 EDT 2019 by syzhou
