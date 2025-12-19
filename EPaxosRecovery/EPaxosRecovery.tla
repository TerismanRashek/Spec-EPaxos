---- MODULE EPaxosRecovery ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Proc,       \* set of processes, e.g. {1,2,3,4,5}
    CmdIds,     \* set of command identifiers, e.g. {"a","b"}
    CmdVals,    \* set of payloads; must include "Nop"
    InitCoord   \* function: CmdIds -> Proc
    E,
    F

\* TLC parameters to be set in the model
VARIABLE INSTANCE_f, INSTANCE_e

\* State variables
VARIABLES
    bal,        \* bal[p][id] : highest ballot known at process p for command id
    abal,       \* abal[p][id] : reported ballot value used in RecoverOK (kept in sync with bal[p][id])
    cmd,        \* cmd[p][id] : payload stored at p for id ("Nop" or other) or Null
    initCmd,    \* initCmd[p][id] : initial payload stored at p (or Null)
    dep,        \* dep[p][id] : dependency set at p for id (subset of CmdIds)
    initDep,    \* initDep[p][id] : initial dependency set at p (or {})
    phase,      \* phase[p][id] \in {"none","preaccepted","accepted","committed"}
    msgs,       \* set of messages in flight
    waiting,    \* set of ids currently in waiting mode (coordinator sent Waiting)
    chosenBallots, \* set of ballots used (auxiliary)
    recoverCount \* number of recover attempts per process per command

\* Message type helpers
TypeRecover   == "Recover"
TypeRecoverOK == "RecoverOK"
TypeValidate  == "Validate"
TypeValidateOK== "ValidateOK"
TypeAccept    == "Accept"
TypeCommit    == "Commit"
TypeWaiting   == "Waiting"

Message(type, from, to, body) ==
    [ type |-> type, from |-> from, to |-> to, body |-> body ]

RecoverMsg(p, q, b, id) ==
    Message(TypeRecover, p, q, [ b |-> b, id |-> id ])

RecoverOKMsg(q, p, b, id, ab, c, D, initD, ph) ==
    Message(TypeRecoverOK, q, p,
            [ b        |-> b,
              id       |-> id,
              abalq    |-> ab,
              cq       |-> c,
              depq     |-> D,
              initDepq |-> initD,
              phaseq   |-> ph ])

ValidateMsg(p, q, b, id, c, D) ==
    Message(TypeValidate, p, q,
            [ b |-> b,
             id |-> id,
              c |-> c,
              D |-> D ])

ValidateOKMsg(q, p, b, id, I, c, D) ==
    Message(TypeValidateOK, q, p,
            [ b |-> b, 
            id |-> id,
             Iq |-> I,
              c |-> c,
              D |-> D ])

AcceptMsg(p, q, b, id, c, D) ==
    Message(TypeAccept, p, q,
            [ b |-> b,
             id |-> id,
              cmdc |-> c,
              depc |-> D ])

CommitMsg(p, q, b, id, c, D) ==
    Message(TypeCommit, p, q,
            [ b |-> b,
             id |-> id,
              cmdc |-> c,
               depc |-> D ])

WaitingMsg(p, q, id, k) ==
    Message(TypeWaiting, p, q,
            [ id |-> id,
             k |-> k ])

\* Phase values and Null marker
AllPhases == {"none","preaccepted","accepted","committed"}
Null == "NULL"

\* Derived constants for convenience
N == Cardinality(Proc)
QuorumSize(f) == N - F
FastQuorumSize(e) == N - E

IsQuorum(S) == S \subseteq Proc /\ Cardinality(S) >= QuorumSize(f)

\* Initial state
Init ==
    /\ bal = [ p \in Proc |-> [ id \in CmdIds |-> 0 ] ]
    /\ abal = [ p \in Proc |-> [ id \in CmdIds |-> 0 ] ]
    /\ cmd = [ p \in Proc |-> [ id \in CmdIds |-> Null ] ]
    /\ initCmd = [ p \in Proc |-> [ id \in CmdIds |-> Null ] ]
    /\ dep = [ p \in Proc |-> [ id \in CmdIds |-> {} ] ]
    /\ initDep = [ p \in Proc |-> [ id \in CmdIds |-> {} ] ]
    /\ phase = [ p \in Proc |-> [ id \in CmdIds |-> "none" ] ]
    /\ msgs = {}
    /\ waiting = {}
    /\ chosenBallots = {}
    /\ recoverCount = [ p \in Proc |-> [ id \in CmdIds |-> 0 ] ]

\* ----------------------------------------------------------------------
\* Parameterized actions
\* ----------------------------------------------------------------------

StartRecover(p, id) ==
    /\ p \in Proc
    /\ id \in CmdIds
    /\ recoverCount[p][id] < 5
    /\ LET b == CHOOSE x \in Nat : x > bal[p][id] IN
       /\ msgs' = msgs \cup
            { RecoverMsg(p, q, b, id) : q \in Proc }
       /\ recoverCount' = [ recoverCount EXCEPT ![p][id] = @ + 1 ]
       /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase, waiting, chosenBallots >>

HandleRecover(m) ==
    /\ m \in msgs
    /\ m.type = TypeRecover
    /\ LET b == m.body.b
           id == m.body.id
           q  == m.to
       IN /\ bal[q][id] < b
          /\ bal'  = [ bal  EXCEPT ![q] = [ bal[q] EXCEPT ![id] = b ] ]
          /\ msgs' = (msgs \ { m }) \cup
                { RecoverOKMsg(q, m.from, b, id, abal[q][id], cmd[q][id], dep[q][id], initDep[q][id], phase[q][id]) }
          /\ UNCHANGED << cmd, initCmd, dep, initDep, phase, waiting, chosenBallots, recoverCount >>

\* Coordinator resolve and other message handlers (simplified version using helpers)
HandleRecoverOK(p, m) ==
    /\ m \in msgs
    /\ m.type = TypeRecoverOK
    /\ p = m.to
    /\ LET id == m.body.id
           b  == m.body.b
       IN
       LET quorum ==
           { q \in Proc :
               \E k \in msgs :
                   /\ k.type = TypeRecoverOK
                   /\ k.to = p
                   /\ k.from = q
                   /\ k.body.id = id
                   /\ k.body.b = b }
       IN
       /\ bal[p][id] = b
       /\ Quorum(quorum)
       /\ LET OKs ==
           { k \in msgs :
               /\ k.type = TypeRecoverOK
               /\ k.to = p
               /\ k.from \in quorum
               /\ k.body.id = id
               /\ k.body.b = b }
          Abals == { k.body.abalq : k \in OKs }
          bmax == IF Abals = {} THEN 0 ELSE Max(Abals)
          U == { k \in OKs : k.body.abalq = bmax }
       IN
       \/ ( \E k \in U : k.body.phaseq = "committed"
            /\ LET mr == CHOOSE k \in U : k.body.phaseq = "committed" IN
               msgs' = (msgs \ OKs) \cup
                   { CommitMsg(p,q,b,id,mr.body.cq,mr.body.depq)
                       : q \in Proc } )
       \/ ( \E k \in U : k.body.phaseq = "accepted"
            /\ LET mr == CHOOSE k \in U : k.body.phaseq = "accepted" IN
               msgs' = (msgs \ OKs) \cup
                   { AcceptMsg(p,q,b,id,mr.body.cq,mr.body.depq)
                       : q \in Proc } )
       \/ ( /\ InitCoord[id] \in quorum
            /\ msgs' = (msgs \ OKs) \cup
                 { AcceptMsg(p,q,b,id,"Nop",{})
                     : q \in Proc } )
       \/ (  LET PreAcc ==
                    { q \in quorum :
                        \E k \in OKs :
                            /\ k.from = q
                            /\ k.body.phaseq = "preaccepted"
                            /\ k.body.depq = k.body.initDepq }
                    Rneeded == Cardinality(quorum) - e
                IN
                /\ Cardinality(PreAcc) >= Rneeded
                /\ LET anyq == CHOOSE q \in PreAcc : TRUE
                       kr == CHOOSE k \in OKs : k.from = anyq
                   IN
                   msgs' = (msgs \ OKs) \cup
                       { ValidateMsg(p,q,b,id,kr.body.cq,kr.body.depq)
                           : q \in quorum } )
    /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase, waiting, chosenBallots, recoverCount >>

HandleWaitingMsg(m) ==
    /\ m \in msgs
    /\ m.type = TypeWaiting
    /\ LET id == m.body.id
           p == m.from
       IN
       /\ id \in waiting
       /\ msgs' =
            (msgs \ {m}) \cup
            { AcceptMsg(p,q,bal[p][id],id,"Nop",{})
                : q \in Proc }
       /\ waiting' = waiting \ {id}
       /\ UNCHANGED << bal, abal, cmd, initCmd, initDep, dep, phase, chosenBallots, recoverCount >>

\* Other handlers (Validate, Accept, Commit) remain mostly unchanged with helpers

\* Deliver arbitrary messages
Deliver(m) ==
    /\ m \in msgs
    /\ msgs' = msgs \ { m }
    /\ UNCHANGED << bal, abal, cmd, initCmd, initDep, dep, phase, waiting, chosenBallots, recoverCount >>

\* ----------------------------------------------------------------------
\* Next: group by common quantifiers
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc, id \in CmdIds : StartRecover(p,id)
    \/ \E m \in msgs : HandleRecover(m)
    \/ \E m \in msgs : HandleRecoverOK(m)
    \/ \E m \in msgs : HandleWaitingMsg(m)
    \/ \E m \in msgs : Deliver(m)
    \* Other operations (HandleValidate, HandleAccept, HandleCommit, HandleValidateOKCollect) can be similarly added

\* Full spec
Spec == Init /\ [][Next]_<< bal, abal, cmd, initCmd, initDep, dep, phase, msgs, waiting, chosenBallots, recoverCount >>

=============================================================================
