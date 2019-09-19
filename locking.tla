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
          \/ /\ \A request \in locks[resource].granted:
                  <<request.mode, mode>> \in CompatibilityMatrix
             /\ \A request \in locks[resource].pending:
                  request.mode /= MODE_X;
lock_granted:
    \* self should have been defined in the scope.
    locks[resource] := [ pending |-> { r \in locks[resource].pending: r.thread /= self },
                         granted |-> locks[resource].granted \union {[thread |-> self, mode |-> mode]} ];
    return;
end procedure;

process ThreadA \in {"ThreadA"}
begin
A_LOCK1:   call lock("DB1", MODE_IX);
A_LOCK2:   call lock("DB2", MODE_X);
A_UNLOCK1: unlock("DB1");
A_UNLOCK2: unlock("DB2");
end process

process ThreadB \in {"ThreadB"}
begin
B_LOCK2:   call lock("DB2", MODE_X);
B_LOCK1:   call lock("DB1", MODE_IX);
B_UNLOCK1: unlock("DB1");
B_UNLOCK2: unlock("DB2");
end process

\* Since IX requests wait for pending X to acquire first, this essentially makes
\* the two IX requests conflict.
process ThreadC \in {"ThreadC"}
begin
C_LOCK1:   call lock("DB1", MODE_X);
C_UNLOCK1: unlock("DB1");
end process


end algorithm *)


\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES locks, pc, stack, resource, mode

vars == << locks, pc, stack, resource, mode >>

ProcSet == ({"ThreadA"}) \cup ({"ThreadB"}) \cup ({"ThreadC"})

Init == (* Global variables *)
        /\ locks = [ r \in AllResources |-> [granted |-> {}, pending |-> {}]]
        (* Procedure lock *)
        /\ resource = [ self \in ProcSet |-> defaultInitValue]
        /\ mode = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {"ThreadA"} -> "A_LOCK1"
                                        [] self \in {"ThreadB"} -> "B_LOCK2"
                                        [] self \in {"ThreadC"} -> "C_LOCK1"]

try_lock(self) == /\ pc[self] = "try_lock"
                  /\ locks' = [locks EXCEPT ![resource[self]].pending = locks[resource[self]].pending \union {[thread |-> self, mode |-> mode[self]]}]
                  /\ pc' = [pc EXCEPT ![self] = "lock_wait"]
                  /\ UNCHANGED << stack, resource, mode >>

lock_wait(self) == /\ pc[self] = "lock_wait"
                   /\ \/ locks[resource[self]].granted = {}
                      \/ /\ \A request \in locks[resource[self]].granted:
                              <<request.mode, mode[self]>> \in CompatibilityMatrix
                         /\ \A request \in locks[resource[self]].pending:
                              request.mode /= MODE_X
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

A_LOCK1(self) == /\ pc[self] = "A_LOCK1"
                 /\ /\ mode' = [mode EXCEPT ![self] = MODE_IX]
                    /\ resource' = [resource EXCEPT ![self] = "DB1"]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                             pc        |->  "A_LOCK2",
                                                             resource  |->  resource[self],
                                                             mode      |->  mode[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "try_lock"]
                 /\ locks' = locks

A_LOCK2(self) == /\ pc[self] = "A_LOCK2"
                 /\ /\ mode' = [mode EXCEPT ![self] = MODE_X]
                    /\ resource' = [resource EXCEPT ![self] = "DB2"]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                             pc        |->  "A_UNLOCK1",
                                                             resource  |->  resource[self],
                                                             mode      |->  mode[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "try_lock"]
                 /\ locks' = locks

A_UNLOCK1(self) == /\ pc[self] = "A_UNLOCK1"
                   /\ Assert(\E request \in locks["DB1"].granted: request.thread = self,
                             "Failure of assertion at line 42, column 5 of macro called at line 67, column 12.")
                   /\ locks' = [locks EXCEPT !["DB1"].granted = { r \in locks["DB1"].granted: r.thread /= self }]
                   /\ pc' = [pc EXCEPT ![self] = "A_UNLOCK2"]
                   /\ UNCHANGED << stack, resource, mode >>

A_UNLOCK2(self) == /\ pc[self] = "A_UNLOCK2"
                   /\ Assert(\E request \in locks["DB2"].granted: request.thread = self,
                             "Failure of assertion at line 42, column 5 of macro called at line 68, column 12.")
                   /\ locks' = [locks EXCEPT !["DB2"].granted = { r \in locks["DB2"].granted: r.thread /= self }]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << stack, resource, mode >>

ThreadA(self) == A_LOCK1(self) \/ A_LOCK2(self) \/ A_UNLOCK1(self)
                    \/ A_UNLOCK2(self)

B_LOCK2(self) == /\ pc[self] = "B_LOCK2"
                 /\ /\ mode' = [mode EXCEPT ![self] = MODE_X]
                    /\ resource' = [resource EXCEPT ![self] = "DB2"]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                             pc        |->  "B_LOCK1",
                                                             resource  |->  resource[self],
                                                             mode      |->  mode[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "try_lock"]
                 /\ locks' = locks

B_LOCK1(self) == /\ pc[self] = "B_LOCK1"
                 /\ /\ mode' = [mode EXCEPT ![self] = MODE_IX]
                    /\ resource' = [resource EXCEPT ![self] = "DB1"]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                             pc        |->  "B_UNLOCK1",
                                                             resource  |->  resource[self],
                                                             mode      |->  mode[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "try_lock"]
                 /\ locks' = locks

B_UNLOCK1(self) == /\ pc[self] = "B_UNLOCK1"
                   /\ Assert(\E request \in locks["DB1"].granted: request.thread = self,
                             "Failure of assertion at line 42, column 5 of macro called at line 75, column 12.")
                   /\ locks' = [locks EXCEPT !["DB1"].granted = { r \in locks["DB1"].granted: r.thread /= self }]
                   /\ pc' = [pc EXCEPT ![self] = "B_UNLOCK2"]
                   /\ UNCHANGED << stack, resource, mode >>

B_UNLOCK2(self) == /\ pc[self] = "B_UNLOCK2"
                   /\ Assert(\E request \in locks["DB2"].granted: request.thread = self,
                             "Failure of assertion at line 42, column 5 of macro called at line 76, column 12.")
                   /\ locks' = [locks EXCEPT !["DB2"].granted = { r \in locks["DB2"].granted: r.thread /= self }]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << stack, resource, mode >>

ThreadB(self) == B_LOCK2(self) \/ B_LOCK1(self) \/ B_UNLOCK1(self)
                    \/ B_UNLOCK2(self)

C_LOCK1(self) == /\ pc[self] = "C_LOCK1"
                 /\ /\ mode' = [mode EXCEPT ![self] = MODE_X]
                    /\ resource' = [resource EXCEPT ![self] = "DB1"]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                             pc        |->  "C_UNLOCK1",
                                                             resource  |->  resource[self],
                                                             mode      |->  mode[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "try_lock"]
                 /\ locks' = locks

C_UNLOCK1(self) == /\ pc[self] = "C_UNLOCK1"
                   /\ Assert(\E request \in locks["DB1"].granted: request.thread = self,
                             "Failure of assertion at line 42, column 5 of macro called at line 84, column 12.")
                   /\ locks' = [locks EXCEPT !["DB1"].granted = { r \in locks["DB1"].granted: r.thread /= self }]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << stack, resource, mode >>

ThreadC(self) == C_LOCK1(self) \/ C_UNLOCK1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: lock(self))
           \/ (\E self \in {"ThreadA"}: ThreadA(self))
           \/ (\E self \in {"ThreadB"}: ThreadB(self))
           \/ (\E self \in {"ThreadC"}: ThreadC(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Sep 18 22:34:38 EDT 2019 by syzhou
\* Created Tue Sep 17 18:48:11 EDT 2019 by syzhou
