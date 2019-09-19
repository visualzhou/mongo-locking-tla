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

AllResources == { "DB1", "DB2", "GLOBAL" }

Range(T) == { T[x] : x \in DOMAIN T }

(* --algorithm locking
variables locks = [ r \in AllResources |-> [granted |-> {}, pending |-> {}]], unreplicated_oplog = <<>>;

macro append_to_oplog(op) begin
    unreplicated_oplog := Append(unreplicated_oplog, [thread |-> self, op |-> op]);
end macro;

macro wait_for_write_concern(op) begin
    await \A entry \in Range(unreplicated_oplog): entry /= [thread |-> self, op |-> op];
end macro;

macro unlock(resource) begin
    assert \E request \in locks[resource].granted: request.thread = self;
    locks[resource].granted := { r \in locks[resource].granted: r.thread /= self };
end macro;


procedure lock(resource, mode) begin
try_lock:
    locks[resource].pending := locks[resource].pending \union {[thread |-> self, mode |-> mode]};
lock_granted:
    await \/ locks[resource].granted = {}
          \/ /\ \A request \in locks[resource].granted:
                  <<request.mode, mode>> \in CompatibilityMatrix
             /\ \A request \in locks[resource].pending:
                  request.mode /= MODE_X;

    \* self should have been defined in the scope.
    locks[resource].pending := { r \in locks[resource].pending: r.thread /= self } ||
    locks[resource].granted := locks[resource].granted \union {[thread |-> self, mode |-> mode]};
    return;
end procedure;

process ThreadTxn \in {"ThreadTxn"}
begin
\* Start transaction.
TXN_LOCK1:   call lock("GLOBAL", MODE_IX);

\* Prepare transaction.
TXN_WRITE:   append_to_oplog("prepare-write");
TXN_WC:      wait_for_write_concern("prepare-write");

\* Commit transaction.
TXN_UNLOCK1: unlock("GLOBAL");
end process

process ThreadDropDB \in {"ThreadDropDB"}
begin
DROP_DB_LOCK1:   call lock("GLOBAL", MODE_X);
DROP_DB_UNLOCK1: unlock("GLOBAL");
end process

process DataReplication \in {"DataReplication"}
begin
DATA_REPL_START:
while TRUE do
    if unreplicated_oplog /= <<>> then
REPL_LOCK:    call lock("GLOBAL", MODE_IS);
              \* Removing elements from the unreplicated_oplog means they have been replicated.
REPL:         unreplicated_oplog := Tail(unreplicated_oplog);
REPL_UNLOCK:  unlock("GLOBAL");
    end if
end while
end process

end algorithm *)





























\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES locks, unreplicated_oplog, pc, stack, resource, mode

vars == << locks, unreplicated_oplog, pc, stack, resource, mode >>

ProcSet == ({"ThreadTxn"}) \cup ({"ThreadDropDB"}) \cup ({"DataReplication"})

Init == (* Global variables *)
        /\ locks = [ r \in AllResources |-> [granted |-> {}, pending |-> {}]]
        /\ unreplicated_oplog = <<>>
        (* Procedure lock *)
        /\ resource = [ self \in ProcSet |-> defaultInitValue]
        /\ mode = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {"ThreadTxn"} -> "TXN_LOCK1"
                                        [] self \in {"ThreadDropDB"} -> "DROP_DB_LOCK1"
                                        [] self \in {"DataReplication"} -> "DATA_REPL_START"]

try_lock(self) == /\ pc[self] = "try_lock"
                  /\ locks' = [locks EXCEPT ![resource[self]].pending = locks[resource[self]].pending \union {[thread |-> self, mode |-> mode[self]]}]
                  /\ pc' = [pc EXCEPT ![self] = "lock_granted"]
                  /\ UNCHANGED << unreplicated_oplog, stack, resource, mode >>

lock_granted(self) == /\ pc[self] = "lock_granted"
                      /\ \/ locks[resource[self]].granted = {}
                         \/ /\ \A request \in locks[resource[self]].granted:
                                 <<request.mode, mode[self]>> \in CompatibilityMatrix
                            /\ \A request \in locks[resource[self]].pending:
                                 request.mode /= MODE_X
                      /\ locks' = [locks EXCEPT ![resource[self]].pending = { r \in locks[resource[self]].pending: r.thread /= self },
                                                ![resource[self]].granted = locks[resource[self]].granted \union {[thread |-> self, mode |-> mode[self]]}]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ resource' = [resource EXCEPT ![self] = Head(stack[self]).resource]
                      /\ mode' = [mode EXCEPT ![self] = Head(stack[self]).mode]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED unreplicated_oplog

lock(self) == try_lock(self) \/ lock_granted(self)

TXN_LOCK1(self) == /\ pc[self] = "TXN_LOCK1"
                   /\ /\ mode' = [mode EXCEPT ![self] = MODE_IX]
                      /\ resource' = [resource EXCEPT ![self] = "GLOBAL"]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                               pc        |->  "TXN_WRITE",
                                                               resource  |->  resource[self],
                                                               mode      |->  mode[self] ] >>
                                                           \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "try_lock"]
                   /\ UNCHANGED << locks, unreplicated_oplog >>

TXN_WRITE(self) == /\ pc[self] = "TXN_WRITE"
                   /\ unreplicated_oplog' = Append(unreplicated_oplog, [thread |-> self, op |-> "prepare-write"])
                   /\ pc' = [pc EXCEPT ![self] = "TXN_WC"]
                   /\ UNCHANGED << locks, stack, resource, mode >>

TXN_WC(self) == /\ pc[self] = "TXN_WC"
                /\ \A entry \in Range(unreplicated_oplog): entry /= [thread |-> self, op |-> "prepare-write"]
                /\ pc' = [pc EXCEPT ![self] = "TXN_UNLOCK1"]
                /\ UNCHANGED << locks, unreplicated_oplog, stack, resource,
                                mode >>

TXN_UNLOCK1(self) == /\ pc[self] = "TXN_UNLOCK1"
                     /\ Assert(\E request \in locks["GLOBAL"].granted: request.thread = self,
                               "Failure of assertion at line 50, column 5 of macro called at line 81, column 14.")
                     /\ locks' = [locks EXCEPT !["GLOBAL"].granted = { r \in locks["GLOBAL"].granted: r.thread /= self }]
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << unreplicated_oplog, stack, resource, mode >>

ThreadTxn(self) == TXN_LOCK1(self) \/ TXN_WRITE(self) \/ TXN_WC(self)
                      \/ TXN_UNLOCK1(self)

DROP_DB_LOCK1(self) == /\ pc[self] = "DROP_DB_LOCK1"
                       /\ /\ mode' = [mode EXCEPT ![self] = MODE_X]
                          /\ resource' = [resource EXCEPT ![self] = "GLOBAL"]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                                   pc        |->  "DROP_DB_UNLOCK1",
                                                                   resource  |->  resource[self],
                                                                   mode      |->  mode[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "try_lock"]
                       /\ UNCHANGED << locks, unreplicated_oplog >>

DROP_DB_UNLOCK1(self) == /\ pc[self] = "DROP_DB_UNLOCK1"
                         /\ Assert(\E request \in locks["GLOBAL"].granted: request.thread = self,
                                   "Failure of assertion at line 50, column 5 of macro called at line 87, column 18.")
                         /\ locks' = [locks EXCEPT !["GLOBAL"].granted = { r \in locks["GLOBAL"].granted: r.thread /= self }]
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << unreplicated_oplog, stack, resource,
                                         mode >>

ThreadDropDB(self) == DROP_DB_LOCK1(self) \/ DROP_DB_UNLOCK1(self)

DATA_REPL_START(self) == /\ pc[self] = "DATA_REPL_START"
                         /\ IF unreplicated_oplog /= <<>>
                               THEN /\ pc' = [pc EXCEPT ![self] = "REPL_LOCK"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "DATA_REPL_START"]
                         /\ UNCHANGED << locks, unreplicated_oplog, stack,
                                         resource, mode >>

REPL_LOCK(self) == /\ pc[self] = "REPL_LOCK"
                   /\ /\ mode' = [mode EXCEPT ![self] = MODE_IS]
                      /\ resource' = [resource EXCEPT ![self] = "GLOBAL"]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                               pc        |->  "REPL",
                                                               resource  |->  resource[self],
                                                               mode      |->  mode[self] ] >>
                                                           \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "try_lock"]
                   /\ UNCHANGED << locks, unreplicated_oplog >>

REPL(self) == /\ pc[self] = "REPL"
              /\ unreplicated_oplog' = Tail(unreplicated_oplog)
              /\ pc' = [pc EXCEPT ![self] = "REPL_UNLOCK"]
              /\ UNCHANGED << locks, stack, resource, mode >>

REPL_UNLOCK(self) == /\ pc[self] = "REPL_UNLOCK"
                     /\ Assert(\E request \in locks["GLOBAL"].granted: request.thread = self,
                               "Failure of assertion at line 50, column 5 of macro called at line 98, column 15.")
                     /\ locks' = [locks EXCEPT !["GLOBAL"].granted = { r \in locks["GLOBAL"].granted: r.thread /= self }]
                     /\ pc' = [pc EXCEPT ![self] = "DATA_REPL_START"]
                     /\ UNCHANGED << unreplicated_oplog, stack, resource, mode >>

DataReplication(self) == DATA_REPL_START(self) \/ REPL_LOCK(self)
                            \/ REPL(self) \/ REPL_UNLOCK(self)

Next == (\E self \in ProcSet: lock(self))
           \/ (\E self \in {"ThreadTxn"}: ThreadTxn(self))
           \/ (\E self \in {"ThreadDropDB"}: ThreadDropDB(self))
           \/ (\E self \in {"DataReplication"}: DataReplication(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Sep 18 23:41:52 EDT 2019 by syzhou
\* Created Tue Sep 17 18:48:11 EDT 2019 by syzhou
