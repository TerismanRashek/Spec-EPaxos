------------------------------ MODULE EPaxosCommitProtocolSpec ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Proc,           \* set of processes
    F,              \* max # crash failures
    E,              \* e-fast parameter (E ≤ F)
    Cmd,            \* set of command payloads
    Id,             \* command identifiers  
    NoCmd,           \* special value representing no command
    NoProc          \* special value representing no process

ASSUME E <= F

(**********************************************************************
 * State Variables
 **********************************************************************)

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
    initCoord       \* initCoord[id] = process that submitted id

(**********************************************************************
 * Message constructors
 **********************************************************************)
PreAcceptMsg(id, c, D, b, from, to) ==
    [type  |-> "PreAccept",
     id    |-> id,
     cmd   |-> c,
     dep   |-> D,
     bal   |-> b,
     from  |-> from,
     to    |-> to]

PreAcceptOKMsg(id, Dp, b, from, to) ==
    [type  |-> "PreAcceptOK",
     id    |-> id,
     dep   |-> Dp,
     bal   |-> b,
     from  |-> from,
     to    |-> to]

AcceptMsg(id, D, b, c, from, to) ==
    [type    |-> "Accept",
     id      |-> id,
     dep     |-> D,
     bal     |-> b,
     cmd     |-> c,
     from    |-> from,
     to      |-> to]

AcceptOKMsg(id, b, from, to) ==
    [type |-> "AcceptOK",
     id   |-> id,
     bal  |-> b,
     from |-> from,
     to   |-> to]

CommitMsg(id, D, b, c, from, to) ==
    [type |-> "Commit",
     id   |-> id,
     dep  |-> D,
     bal  |-> b,
     cmd  |-> c,
     from |-> from,
     to   |-> to]

(**********************************************************************
 * Helpers
 **********************************************************************)

\* Conflict function: define according to application logic
Conflicts(c1, c2) == 
    /\ c1 \in Cmd
    /\ c2 \in Cmd
    /\ c1 # c2  

Quorum(Q) == Cardinality(Q) >= Cardinality(Proc) - F
FastQuorum(Q) == Cardinality(Q) >= Cardinality(Proc) - E

ConflictingIds(p, c) ==
    { id2 \in Id :
        /\ phase[id2][p] # "Initial" 
        /\ Conflicts(cmd[id2][p], c)
    }

(**********************************************************************
 * Actions
 **********************************************************************)

Submit(p, id, c) ==
    /\ id \notin submitted
    /\ LET D0 ==
           ConflictingIds(p, c)
       IN
          /\ msgs' = msgs \cup
                { PreAcceptMsg(id, c, D0, 0, p, q) : q \in Proc }
          /\ submitted' = submitted \cup {id}
          /\ initCoord' = [initCoord EXCEPT ![id] = p]
          /\ UNCHANGED << phase, bal, cmd, initCmd, initDep,
                           dep, abal >>

HandlePreAccept(p, m) ==
    /\ phase[m.id][p] = "Initial"
    /\ m.type = "PreAccept"
    /\ p = m.to
    /\ bal[m.id][p] = 0
    /\ cmd' = [cmd EXCEPT ![m.id][p] = m.cmd]
    /\ initCmd' = [initCmd EXCEPT ![m.id][p] = m.cmd]
    /\ initDep' = [initDep EXCEPT ![m.id][p] = m.dep]
    /\ phase' = [phase EXCEPT ![m.id][p] = "preaccepted"]
    /\ LET Dp ==
             ConflictingIds(p, m.cmd)
       IN
       /\ LET Dfinal ==
              m.dep \cup Dp
          IN
          /\ dep' = [dep EXCEPT ![m.id][p] = Dfinal]
          /\ msgs' = (msgs \cup {
                  PreAcceptOKMsg(m.id, dep'[m.id][p],
                                  m.bal, p, m.from)
              }) \ {m}
    /\ UNCHANGED << abal, submitted, bal, initCoord >>

HandlePreAcceptOK(p, m) ==
    /\ m.type = "PreAcceptOK"
    /\ phase[m.id][p] = "preaccepted"
    /\ p = initCoord[m.id]
    /\ p = m.to
    /\ LET id == m.id IN
       LET quorum ==
           { q \in Proc :
               \E k \in msgs :
                   /\ k.type = "PreAcceptOK"
                   /\ k.id = id
                   /\ k.to = p
                   /\ k.from = q
           }
       IN
       /\ Quorum(quorum)
       /\ LET OKs == { k \in msgs :
              /\ k.type = "PreAcceptOK"
              /\ k.to = p
              /\ k.from \in quorum
              /\ k.id = id
          }
          IN
          /\ LET Dfinal == UNION { k.dep : k \in OKs }
                IN
            /\ IF (FastQuorum(quorum) /\ \A k \in OKs : k.dep = initDep[id][p])
                THEN
                    /\ msgs' = (msgs \cup { CommitMsg(id, Dfinal, 0, cmd[id][p], p, q) : q \in Proc }) \ OKs
                    /\ UNCHANGED << bal, phase, cmd, initCmd,
                                    initDep, dep, abal, submitted, initCoord >>
                ELSE
                    /\  msgs' = (msgs \cup { AcceptMsg(id, Dfinal, 0, cmd[id][p], p, q) : q \in Proc }) \ OKs
                    /\ UNCHANGED << bal, phase, cmd, initCmd,
                                    initDep, dep, abal, submitted , initCoord >>

HandleAccept(p, m) ==
    /\ m.type = "Accept"
    /\ p = m.to
    /\ bal[m.id][p] <= m.bal
    /\ bal[m.id][p] = m.bal => phase[m.id][p] # "committed"
    /\ bal' = [bal EXCEPT ![m.id][p] = m.bal]
    /\ abal' = [abal EXCEPT ![m.id][p] = m.bal]
    /\ dep' = [dep EXCEPT ![m.id][p] = m.dep]
    /\ cmd' = [cmd EXCEPT ![m.id][p] = m.cmd]
    /\ phase' = [phase EXCEPT ![m.id][p] = "accepted"]

    /\ msgs' = (msgs \cup {
            AcceptOKMsg(m.id, m.bal, p, m.from)
        }) \ {m}

    /\ UNCHANGED <<  initCmd, initDep,
                     submitted , initCoord >>

HandleAcceptOK(p, m) ==
    /\ m.type = "AcceptOK"
    /\ m.to = p
    /\ bal[m.id][p] = m.bal
    /\ phase[m.id][p] = "accepted"
    /\ LET id == m.id IN
       LET quorum ==
           { q \in Proc :
               \E k \in msgs :
                   /\ k.type = "AcceptOK"
                   /\ k.id = id
                   /\ k.to = p
                   /\ k.from = q
           }
       IN
       /\ Quorum(quorum)
       /\ LET OKs == { k \in msgs :
              /\ k.type = "AcceptOK"
              /\ k.to = p
              /\ k.from \in quorum
              /\ k.id = id
          }
          IN
          /\ msgs' = (msgs \cup {
                  CommitMsg(id, dep[id][p], m.bal, cmd[id][p], p, q)
                    : q \in Proc
             }) \ { m }
          /\ UNCHANGED << bal, phase, cmd, initCmd,
                            initDep, dep, abal, submitted, initCoord >>

HandleCommit(p, m) ==
    /\ m.type = "Commit"
    /\ p = m.to
    /\ bal[m.id][p] = m.bal
    /\ dep' = [dep EXCEPT ![m.id][p] = m.dep]
    /\ phase' = [phase EXCEPT ![m.id][p] = "committed"]
    /\ abal' = [abal EXCEPT ![m.id][p] = m.bal]
    /\ msgs' = msgs \ {m}
    /\ cmd' = [cmd EXCEPT ![m.id][p] = m.cmd]
    /\ UNCHANGED << bal, initCmd, initDep,
                       submitted , initCoord >>

(**********************************************************************
 * Invariants
 **********************************************************************)

Agreement ==
  \A id \in Id :
    \A p, q \in Proc :
      /\ phase[id][p] = "committed"
      /\ phase[id][q] = "committed"
      => /\ dep[id][p] = dep[id][q]
         /\ cmd[id][p] = cmd[id][q]

Visibility ==
  \A id, id2 \in Id : \E p, q \in Proc :
    /\ id # id2
    /\ phase[id][p] = "committed"
    /\ phase[id2][q] = "committed"
    /\ Conflicts(cmd[id][p], cmd[id2][q])
    => \/ id \in dep[id2][q]
       \/ id2 \in dep[id][p]


Invariants ==
    Agreement /\ Visibility

(**********************************************************************
 * Next-state relation
 **********************************************************************)

Next ==
    \/ \E p \in Proc, m \in msgs :
        \/ HandlePreAccept(p, m)
        \/ HandlePreAcceptOK(p, m)
        \/ HandleAccept(p, m)
        \/ HandleAcceptOK(p, m)
        \/ HandleCommit(p, m)
    \/ \E q \in Proc, id \in Id, c \in Cmd :
         \/ (Submit(q, id, c))

(**********************************************************************
 * Initialization
 **********************************************************************)

Init ==
    /\ bal = [id \in Id |-> [p \in Proc |-> 0]]
    /\ abal = [id \in Id |-> [p \in Proc |-> 0]]
    /\ phase = [id \in Id |-> [p \in Proc |-> "Initial"]]
    /\ cmd = [id \in Id |-> [p \in Proc |-> NoCmd]]
    /\ submitted = {}
    /\ initCmd = cmd
    /\ initDep = [id \in Id |-> [p \in Proc |-> {}]]
    /\ dep = initDep
    /\ msgs = {}
    /\ initCoord = [id \in Id |-> NoProc]

(**********************************************************************
 * Specification
 **********************************************************************)

Spec == Init /\ [][Next]_<<bal,phase,cmd,initCmd,initDep,
                  dep,abal,msgs, submitted, initCoord>>

==============================================================================

