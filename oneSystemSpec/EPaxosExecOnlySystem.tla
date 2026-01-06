---------------- MODULE EPaxosExecOnlySystem ----------------
    EXTENDS EPaxosExecution, TLC, FiniteSets, Sequences, Naturals

    CONSTANTS 
        Procs,      \* Set of process identifiers
        CmdIds,     \* Set of command identifiers
        UnknownDep  \* distinguished value meaning "dependencies unknown"


    Invariants == Validity /\ Integrity /\ Consistency
                
    Liveness ==
    \A c \in CmdIds:
      (c \in submitted \/ \E p \in Procs: IsExecuted(p, c)) =>
        \A p \in Procs: <> IsExecuted(p, c)


    \* Initialization
    Init ==
        /\ submitted = {}
        /\ dep = [c \in CmdIds |-> {UnknownDep}]
        \* /\ \A c \in CmdIds: dep[c] = {UnknownDep}
        /\ executed = [p \in Procs |-> <<>>]    \* each proc starts with empty sequence

    \* Main transition relation
    Next ==
        \E p \in Procs :
            \E c \in CmdIds :
                \E D \in SUBSET CmdIds :
                    (Submit(c) (* /\ Print(<<"Submit",submitted', p, c>>, TRUE) *))
                    \/ (Commit(c) (* /\ Print(<<"Commit",dep', p, c, D>>, TRUE) *))
                    \/ (Execute(p) /\ Print(<<"Execute",executed', dep', submitted', p>>, TRUE))

    Spec ==
        Init /\ [][Next]_vars /\ WF_vars(Next)
=============================================================================
