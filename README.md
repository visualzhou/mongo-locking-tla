# TLA+ Spec of Locking Behaviors of MongoDB

## Summary
This project is to explore model checking for the locking behaviors of MongoDB. The spec `locking.tla` successfully reproduced the deadlock in [SERVER-43242](https://jira.mongodb.org/browse/SERVER-43242). The PlusCal spec includes
- Lock compatibility matrix.
- MODE_X has a higher priority than other modes.
- Oplog replication and waiting for write concern.
- PrepareTxn command waits for write concern while holding the global IX lock.
- DropDatabase command can be blocked by the prepare, asking for the global X lock.
- Oplog fetching can be blocked after the DropDatabase for the global IS lock.

To check deadlocks in TLC, you may specify all missing definitions of constants as "Model Value".

Extending the spec should be relatively easy by adding new `process`es.

## Motivation
Locking behaviors became significantly more complex in 4.2 after transactions were introduced due to the extended lifetime of locks across several network round trips, session check-out, newly introduced `ReplicationStateTransitionLock` and prepare conflicts. They all can be modeled as locks on some resources, e.g. collection locks, sessions, RSTL and prepared documents. Addtionally, the "Avoid closing connections and killing operations on stepdown" project rewrote the locking behavior of stepdown in 4.2. Due to the complexity, Integrated tests have [found dozens of deadlocks](https://jira.mongodb.org/issues/?jql=project%20%3D%20SERVER%20AND%20text%20~%20deadlock%20ORDER%20BY%20updated%20DESC) involving transactions, DDL operations, data replication and stepdown in replication and execution systems.

## Future Work
- Extend the spec to include more behaviors to reproduce known bugs and to check solution proposals.
- Model interruptibility so that stepdown and shutdown can be included.

## Takeaways
- PlusCal is an easier way to model threads and sequences of actions than TLA+ since TLA+ is about the global state. Using TLA+ to model threads will inevitably specify the intermediate states explicitly, just as in the transpiled TLA+ version of PlusCal.
- TLA+ and PlusCal are essentially two languages. The syntaxes and labeling rules can be confusing, especially when the error messages of transpile failures do not point to the root cause.
- Specifying nontrival behaviors (e.g. writing for write concern) is straightforward once the right level of abstraction is determined.
