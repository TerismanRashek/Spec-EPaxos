---------------- MODULE EPaxosState ----------------

VARIABLES
    bal,           \* bal[id][p] = current ballot known by process p for command id
    phase,         \* phase[id][p] ∈ {"none","preaccepted","accepted","committed"}
    cmd,           \* cmd[id][p] = command payload at p
    initCmd,       \* initCmd[id][p] = payload received in PreAccept
    initDep,       \* initDep[id][p] = dependencies sent by initial coordinator
    dep,           \* dep[id][p] = final dependency set (accepted or committed)
    abal,          \* abal[id][p] = last ballot where p accepted a slow-path value
    msgs,           \* multiset of network messages
    submitted,      \* set of submitted command ids
    initCoord,       \* initCoord[id] = process that submitted id

    (** exec vars **)
    submitted,  \* SUBSET CmdIds
    executed,    \* [Procs -> Seq(CmdIds)]

    (** recovery extra var**)
    waiting \* jsp la encore

=============================================================================