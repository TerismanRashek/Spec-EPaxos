----------------------------- MODULE EPaxosCommitWithRecovery -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC


CONSTANTS
    Proc,           \* set of processes
    F,              \* max # crash failures
    E,              \* e-fast parameter (E ≤ F)
    Cmd,            \* set of command payloads
    Id,             \* command identifiers  
    NoCmd,           \* special value representing no command
    NoProc          \* special value representing no process

ASSUME E <= F

N == Cardinality(Proc)
QuorumSize == N - F


TypePreAccept     == "PreAccept"
TypePreAcceptOK   == "PreAcceptOK"
TypeAccept        == "Accept"
TypeAcceptOK      == "AcceptOK"
TypeCommit        == "Commit"
TypeRecover       == "Recover"
TypeRecoverOK     == "RecoverOK"
TypeValidate      == "Validate"
TypeValidateOK    == "ValidateOK"
TypeWaiting       == "Waiting"
TypePostWaiting   == "PostWaiting"

Message(type, from, to, body) ==
    [ type |-> type, from |-> from, to |-> to, body |-> body ]

PreAcceptMsg(p, q, id, c, D, b) ==
    Message(TypePreAccept, p, q,
        [ id  |-> id,
          cmd |-> c,
          dep |-> D,
          bal |-> b ])

PreAcceptOKMsg(q, p, id, Dp, b) ==
    Message(TypePreAcceptOK, q, p,
        [ id  |-> id,
          dep |-> Dp,
          bal |-> b ])

AcceptMsg(p, q, b, id, c, D) ==
    Message(TypeAccept, p, q,
        [ id   |-> id,
          bal  |-> b,
          cmdc |-> c,
          depc |-> D ])

AcceptOKMsg(q, p, id, b) ==
    Message(TypeAcceptOK, q, p,
        [ id  |-> id,
          bal |-> b ])

CommitMsg(p, q, b, id, c, D) ==
    Message(TypeCommit, p, q,
        [ id   |-> id,
          bal  |-> b,
          cmdc |-> c,
          depc |-> D ])

RecoverMsg(p,q,b,id) ==
    Message(TypeRecover,p,q,[b|->b,id|->id])

RecoverOKMsg(q,p,b,id,ab,c,D,iD,ph) ==
    Message(TypeRecoverOK,q,p,
        [ b|->b, id|->id, abalq|->ab, cq|->c,
          depq|->D, initDepq|->iD, phaseq|->ph ])

ValidateMsg(p,q,b,id,c,D,Q,Rmax) ==
    Message(TypeValidate,p,q,[b|->b,id|->id,c|->c,D|->D,Q|->Q,Rmax|->Rmax])

ValidateOKMsg(q,p,b,id,D,I) ==
    Message(TypeValidateOK,q,p,[b|->b,id|->id,Iq|->I,D|->D])

WaitingMsg(p,q,id,k) ==
    Message(TypeWaiting,p,q,[id|->id,k|->k])

PostWaitingMsg(p,id,I,Q,b,Rmax) ==
    Message(TypePostWaiting,p,p,[id|->id,I|->I,Q|->Q, b|->b,Rmax|->Rmax])

VARIABLES
    bal,           \* bal[p][id] = current ballot known by process p for command id
    phase,         \* phase[p][id] ∈ {"none","preaccepted","accepted","committed"}
    cmd,           \* cmd[p][id] = command payload at p
    initCmd,       \* initCmd[p][id] = payload received in PreAccept
    initDep,       \* initDep[p][id] = dependencies sent by initial coordinator
    dep,           \* dep[p][id] =  dependency set at p for command id
    abal,          \* abal[p][id] = last ballot where p accepted a slow-path value
    msgs,          \* multiset of network messages
    submitted,     \* set of submitted ids
    initCoord,     \* initCoord[id] = process that submitted id
    recovered,      \* counter of times recoverd per (p,id)
    counter         \* counter to count what step of the forced history we are in for testing

vars ==
    << bal, abal, cmd, initCmd, dep, initDep, phase, msgs,
       submitted, initCoord, recovered, counter >>
(**********************************************************************
 * Initialization
 **********************************************************************)

Init ==
    /\ bal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ abal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ cmd = [p \in Proc |-> [id \in Id |-> "Nop"]]
    /\ initCmd = [p \in Proc |-> [id \in Id |-> "Nop"]]
    /\ dep = [p \in Proc |-> [id \in Id |-> {}]]
    /\ initDep = [p \in Proc |-> [id \in Id |-> {}]]
    /\ phase = [p \in Proc |-> [id \in Id |-> "Initial"]]
    /\ initCoord = [id \in Id |-> NoProc]
    /\ submitted = {}
    /\ recovered = [p \in Proc |-> [id \in Id |-> 0]]
    /\ counter = 0
    /\ msgs = {}

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
        /\ phase[p][id2] # "Initial" 
        /\ Conflicts(cmd[p][id2], c)
    }

(**********************************************************************
 * Actions
 **********************************************************************)

Submit(p, id, c) ==
    /\ id \notin submitted
    /\ LET D0 == ConflictingIds(p, c)
       IN
          /\ msgs' = msgs \cup
                { PreAcceptMsg(p, q, id, c, D0, 0) : q \in Proc }
          /\ submitted' = submitted \cup {id}
          /\ initCoord' = [initCoord EXCEPT ![id] = p]
          /\ UNCHANGED << phase, bal, cmd, initCmd, initDep,
                           dep, abal, recovered >> 

HandlePreAccept(m) ==
    /\ m.type = TypePreAccept
    /\ LET p  == m.to
           id == m.body.id
           c  == m.body.cmd
           D  == m.body.dep
           b  == m.body.bal
       IN /\ phase[p][id] = "Initial"
          /\ bal[p][id] = 0
          /\ cmd' = [cmd EXCEPT ![p][id] = c]
          /\ initCmd' = [initCmd EXCEPT ![p][id] = c]
          /\ initDep' = [initDep EXCEPT ![p][id] = D]
          /\ phase' = [phase EXCEPT ![p][id] = "preaccepted"]
          /\ LET Dp == ConflictingIds(p, c)
             IN LET Dfinal == D \cup Dp
                IN /\ dep' = [dep EXCEPT ![p][id] = Dfinal]
                   /\ msgs' = (msgs \cup {
                           PreAcceptOKMsg(p, m.from, id, Dfinal, b)
                       }) \ {m}
          /\ UNCHANGED << abal, submitted, bal, initCoord, recovered >>

HandlePreAcceptOK(m) ==
    /\ m.type = TypePreAcceptOK
    /\ LET p  == m.to
           id == m.body.id
       IN
       /\ phase[p][id] = "preaccepted"
       /\ p = initCoord[id]
       /\ LET quorum ==
              { q \in Proc :
                  \E k \in msgs :
                      /\ k.type = TypePreAcceptOK
                      /\ k.body.id = id
                      /\ k.to = p
                      /\ k.from = q
              }
          IN
          /\ Quorum(quorum)
          /\ LET OKs ==
                 { k \in msgs :
                     /\ k.type = TypePreAcceptOK
                     /\ k.to = p
                     /\ k.from \in quorum
                     /\ k.body.id = id
                 }
             IN
             /\ LET Dfinal == UNION { k.body.dep : k \in OKs }
                IN
                /\ IF FastQuorum(quorum)
                      /\ \A k \in OKs :
                            k.body.dep = initDep[p][id]
                   THEN
                      /\ msgs' =
                           (msgs \ OKs) \cup
                           { CommitMsg(p, q, 0, id,
                                        cmd[p][id], Dfinal)
                             : q \in Proc }
                   ELSE
                      /\ msgs' =
                           (msgs \ OKs) \cup
                           { AcceptMsg(p, q, 0, id,
                                        cmd[p][id], Dfinal)
                             : q \in Proc }
    /\ UNCHANGED << bal, phase, cmd, initCmd,
                     initDep, dep, abal,
                     submitted, initCoord, recovered >>

HandleAccept(m) ==
    /\ m.type = TypeAccept
    /\ LET p  == m.to
           id == m.body.id
           b  == m.body.bal
       IN
       /\ bal[p][id] <= b
       /\ (bal[p][id] = b => phase[p][id] # "committed")
       /\ bal'  = [bal  EXCEPT ![p][id] = b]
       /\ abal' = [abal EXCEPT ![p][id] = b]
       /\ dep'  = [dep  EXCEPT ![p][id] = m.body.depc]
       /\ cmd'  = [cmd  EXCEPT ![p][id] = m.body.cmdc]
       /\ phase' = [phase EXCEPT ![p][id] = "accepted"]
       /\ msgs' =
           (msgs \ {m}) \cup
           { AcceptOKMsg(p, m.from, id, b) }
    /\ UNCHANGED << initCmd, initDep,
                      submitted, initCoord, recovered >>


HandleAcceptOK(m) ==
    /\ m.type = TypeAcceptOK
    /\ LET p  == m.to
           id == m.body.id
           b  == m.body.bal
       IN
       /\ bal[p][id] = b
       /\ phase[p][id] = "accepted"
       /\ LET quorum ==
              { q \in Proc :
                  \E k \in msgs :
                      /\ k.type = TypeAcceptOK
                      /\ k.body.id = id
                      /\ k.to = p
                      /\ k.from = q
              }
          IN
          /\ Quorum(quorum)
          /\ LET OKs == { k \in msgs :
                 /\ k.type = TypeAcceptOK
                 /\ k.to = p
                 /\ k.from \in quorum
                 /\ k.body.id = id
             }
             IN
             /\ msgs' = (msgs \cup {
                     CommitMsg(p, q, b, id, cmd[p][id], dep[p][id])
                       : q \in Proc
                }) \ OKs
             /\ UNCHANGED << bal, phase, cmd, initCmd,
                              initDep, dep, abal, submitted, initCoord, recovered >>

HandleCommit(m) ==
    /\ m.type = TypeCommit
    /\ LET p == m.to
           id == m.body.id
           b  == m.body.bal
       IN
       /\ bal[p][id] = b
       /\ dep' = [dep EXCEPT ![p][id] = m.body.depc]
       /\ phase' = [phase EXCEPT ![p][id] = "committed"]
       /\ abal' = [abal EXCEPT ![p][id] = b]
       /\ cmd' = [cmd EXCEPT ![p][id] = m.body.cmdc]
       /\ msgs' = msgs \ {m}
       /\ UNCHANGED << bal, initCmd, initDep,
                        submitted, initCoord, recovered >>

(***************************************************************************)
(* 44–45 StartRecover                                                      *)
(***************************************************************************)
StartRecover(p,id) ==
    /\ recovered[p][id] < 1
    /\ recovered' = [recovered EXCEPT ![p][id] = recovered[p][id] + 1]
    /\ LET  b == IF bal[p][id] = 0 THEN p ELSE bal[p][id] + Cardinality(Proc)
       IN
        /\ msgs' = msgs \cup { RecoverMsg(p,q,b,id) : q \in Proc }
        /\ bal' = [bal EXCEPT ![p][id] = b]
        /\ UNCHANGED << abal, cmd, initCmd, dep, initDep, phase,
                            submitted, initCoord >>

(***************************************************************************)
(* 46–49 HandleRecover                                                     *)
(***************************************************************************)
HandleRecover(m) ==
    /\ m.type = TypeRecover
    /\ LET p == m.to
           q == m.from
           id == m.body.id
           b == m.body.b
       IN
       /\ bal[p][id] < b
       /\ bal' = [bal EXCEPT ![p][id] = b]
       /\ msgs' =
           (msgs \ {m}) \cup
           { RecoverOKMsg(p,q,b,id,abal[p][id],
                          cmd[p][id],dep[p][id],initDep[p][id],
                          phase[p][id]) }
       /\ UNCHANGED << abal, cmd, initCmd, dep, initDep, phase,
                        submitted, initCoord, recovered >>

(***************************************************************************)
(* 50–63 HandleRecoverOK                                                   *)
(***************************************************************************)
HandleRecoverOK(m) ==
    /\ m.type = TypeRecoverOK
    /\ LET p == m.to
           id == m.body.id
           b  == m.body.b
       IN
       LET Q ==
               { q \in Proc :
                   \E k \in msgs :
                       k.type = TypeRecoverOK /\ k.to = p /\ k.from = q /\
                       k.body.id = id /\ k.body.b = b }
           OKs ==
               { k \in msgs :
                   k.type = TypeRecoverOK /\ k.to = p /\ k.from \in Q /\
                   k.body.id = id /\ k.body.b = b }
           Abals == { k.body.abalq : k \in OKs }
           bmax == CHOOSE val \in Abals : \A val2 \in Abals : val >= val2
           U == { k \in OKs : k.body.abalq = bmax }
       IN
       /\ bal[p][id] = b
       /\ Cardinality(Q) >= QuorumSize
       /\ \/ (\E q \in Proc :
                   \E n \in U :
                        n.from = q
                        /\ n.body.phaseq = "committed"
                        /\ msgs' =
                            (msgs \ OKs) \cup
                            { CommitMsg(p, p2, b, id, n.body.cq, n.body.depq)
                                : p2 \in Proc })

          \/ (\E q \in Proc :
                   \E n \in U :
                        n.from = q
                        /\ n.body.phaseq = "accepted"
                        /\ msgs' =
                            (msgs \ OKs) \cup
                            { AcceptMsg(p, p2, b, id, n.body.cq, n.body.depq)
                                : p2 \in Proc })

          \/ (initCoord[id] \in Q
              /\ msgs' =
                  (msgs \ OKs) \cup
                  { AcceptMsg(p, p2, b, id, "Nop", {}) : p2 \in Proc })
          \/ (/\ LET Rsubsets == SUBSET(Q)
                 IN
                 LET validRsubsets == {R \in Rsubsets : 
                                    Cardinality(R) >= Cardinality(Q) - E 
                                    /\ \A q \in R : 
                                            \E n \in U :
                                                n.from = q
                                                /\ n.body.phaseq = "preaccepted"
                                                /\ n.body.depq = n.body.initDepq  }
                 IN
                 LET Rmax == CHOOSE R \in validRsubsets :
                                  \A R2 \in validRsubsets :
                                      Cardinality(R) >= Cardinality(R2)
                 IN
                 LET n ==
                         CHOOSE n \in U :
                             \E q \in Rmax :
                                 n.from = q /\
                                 n.body.phaseq = "preaccepted" /\

                                 n.body.depq = n.body.initDepq
                 IN
                 LET c == n.body.cq
                     D == n.body.depq
                 IN /\ msgs' =
                        (msgs \ OKs) \cup
                        { ValidateMsg(p, q, b, id, c, D, Q, Cardinality(Rmax))
                            : q \in Q })
       /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase,
                        submitted, initCoord, recovered >>

(***************************************************************************)
(* 84–90 HandleValidate                                                    *)
(***************************************************************************)
HandleValidate(m) ==
    /\ m.type = TypeValidate
    /\ LET p == m.to
           id == m.body.id
           c == m.body.c
           D == m.body.D
           b == m.body.b
       IN
       /\ bal[p][id] = b
       /\ cmd' = [cmd EXCEPT ![p][id] = c]
       /\ initCmd' = [initCmd EXCEPT ![p][id] = c]
       /\ initDep' = [initDep EXCEPT ![p][id] = D]
       /\ LET idsForI == 
              { id2 \in Id :
                  id2 # id /\ 
                  ~((phase[p][id2] = "committed" 
                      => cmd[p][id2] # "Nop" /\ id \notin dep[p][id2] /\ Conflicts(c, cmd[p][id2]))
                    /\ (phase[p][id2] # "committed" 
                      => initCmd[p][id2] # "Nop" /\ id \notin initDep[p][id2] /\ Conflicts(c, initCmd[p][id2]))) }
          IN
          LET I == 
              { <<id2, phase[p][id2]>> : id2 \in idsForI }
          IN
          /\ msgs' =
               (msgs \ {m}) \cup
               { ValidateOKMsg(p, m.from, m.body.b, id, D, I) }
          /\ UNCHANGED << bal, abal, dep, phase,
                        submitted, initCoord, recovered >>

(***************************************************************************)
(* 64–70 HandleValidateOK                                                  *)
(***************************************************************************)
HandleValidateOK(m) ==
    /\ m.type = TypeValidateOK
    /\ LET p == m.to
           id == m.body.id
           b  == m.body.b
           c  == m.body.c
           D  == m.body.D
       IN
       LET validateMessage == CHOOSE m3 \in msgs : 
                /\ m3.type = TypeValidate
                /\ m3.to = p
                /\ m3.body.id = id
                /\ m3.body.b = b
       IN
       LET Q == validateMessage.body.Q
            Rmax == validateMessage.body.Rmax
       IN  
       LET 
            OKs ==
            { m2 \in msgs :
                m2.type = TypeValidateOK /\
                m2.to = p /\ m2.from \in Q /\
                m2.body.id = id /\ m2.body.b = b }
            I ==
                UNION { m2.body.Iq : m2 \in OKs }
        IN    
        /\ msgs' =
            (msgs \ OKs) \cup
            IF I = {} THEN
                (* line 66–67 *)
                { AcceptMsg(p, q, b, id, c, D) : q \in Proc }

            ELSE IF
                (* line 68 *)
                (\E x \in I : x[2] = "committed") \/
                (Rmax = Cardinality(Q) - E /\
                \E x \in I : initCoord[x[1]] \notin Q)
            THEN
                (* line 69 *)
                { AcceptMsg(p, q, b, id, "Nop", {}) : q \in Proc }

            ELSE
                (* line 70–71 *)
                ({ WaitingMsg(p, q, id, Rmax) : q \in Proc } \cup 
                { PostWaitingMsg(p, id, I, Q, b, Rmax) })

    /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase,submitted, initCoord, recovered >>

(***************************************************************************)
(* 71–83 HandlePostWaitingMsg                                                 *)
(***************************************************************************)
                    
HandlePostWaitingMsg(m) ==
    /\ m.type = TypePostWaiting
    /\ LET p == m.to
           id == m.body.id
           I == m.body.I
           Q == m.body.Q
           b == m.body.b
           Rmax == m.body.Rmax
       IN /\ b = bal[p][id]
        \/ (\E x \in I :
                x[1] # id /\
                x[2] = "committed" /\
                cmd[p][x[1]] # "Nop" /\
                id \notin dep[p][x[1]]
            /\ msgs' =
                    msgs \cup
                    { AcceptMsg(p, q, bal[p][id], id, "Nop", {}) : q \in Proc })

        \/ (\A x \in I :
                x[1] # id =>
                (x[2] = "committed" /\
                    (cmd[p][x[1]] = "Nop" \/ id \in dep[p][x[1]]))
            /\ msgs' =
                    msgs \cup
                    { AcceptMsg(p, q, bal[p][id], id, cmd[p][id], dep[p][id])
                        : q \in Proc })

        \/ (\E x \in I :
                x[1] # id /\
                \E m2 \in msgs :
                    m2.type = TypeWaiting /\
                    m2.to = p /\
                    m2.body.id = x[1] /\
                    m2.body.k > N - F - E
            /\ msgs' =
                    msgs \cup
                    { AcceptMsg(p, q, bal[p][id], id, "Nop", {}) : q \in Proc })

        \/ (\E m2 \in msgs :
                m2.type = TypeRecoverOK /\
                m2.to = p /\
                m2.body.id = id /\
                m2.from \notin m2.body.Q /\
                (m2.body.phase = "committed" \/
                    m2.body.phase = "accepted" \/
                    m2.from = initCoord[id])
            /\ msgs' =
                msgs \cup
                IF m2.body.phase = "committed" THEN
                    { CommitMsg(p, q, bal[p][id], id,
                                m2.body.cmd, m2.body.dep) : q \in Proc }
                ELSE IF m2.body.phase = "accepted" THEN
                    { AcceptMsg(p, q, bal[p][id], id,
                                m2.body.cmd, m2.body.dep) : q \in Proc }
                ELSE
                    { AcceptMsg(p, q, bal[p][id], id, "Nop", {}) : q \in Proc })

    /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase,
                        submitted, initCoord, recovered >>
                       

Agreement ==
  \A id \in Id :
    \A p, q \in Proc :
      /\ phase[p][id] = "committed"
      /\ phase[q][id] = "committed"
      => /\ dep[p][id] = dep[q][id]
         /\ cmd[p][id] = cmd[q][id]

Visibility ==
  \A id, id2 \in Id : \E p, q \in Proc :
    /\ id # id2
    /\ phase[p][id] = "committed"
    /\ phase[q][id2] = "committed"
    /\ Conflicts(cmd[p][id], cmd[q][id2])
    => \/ id \in dep[q][id2]
       \/ id2 \in dep[p][id]

Invariant9 ==
    counter < 9
    \/
    \A p \in Proc :
        phase[p][1] \in {"accepted", "committed"}
        =>
        /\ cmd[p][1] = "A"
        /\ dep[p][1] = ConflictingIds(1, "A")



Liveness ==
    \A id \in Id :
      id \in submitted
      => \E p \in Proc :
           phase[p][id] = "committed"

(**********************************************************************
 * Next-state relation
 **********************************************************************)

Prefix ==
    \/ /\ counter = 0
       /\ Submit(1, 1, "A")
       /\ counter' = 1

    \/ /\ counter = 1
       /\ \E m \in msgs :
            /\ m.type = TypePreAccept
            /\ m.from = 1
            /\ m.to = 1
            /\ m.body.id = 1
            /\ HandlePreAccept(m)
       /\ counter' = 2

    \/ /\ counter = 2
       /\ \E m \in msgs :
            /\ m.type = TypePreAccept
            /\ m.from = 1
            /\ m.to = 2
            /\ m.body.id = 1
            /\ HandlePreAccept(m)
       /\ counter' = 3

    \/ /\ counter = 3
       /\ \E m \in msgs :
            /\ m.type = TypePreAcceptOK
            /\ m.from = 1
            /\ m.to = 1
            /\ m.body.id = 1
            /\ HandlePreAcceptOK(m)
       /\ counter' = 4

    \/ /\ counter = 4
       /\ \E m \in msgs :
            /\ m.type = TypeAccept
            /\ m.from = 1
            /\ m.to = 1
            /\ m.body.id = 1
            /\ HandleAccept(m)
       /\ counter' = 5

    \/ /\ counter = 5
       /\ \E m \in msgs :
            /\ m.type = TypeAccept
            /\ m.from = 1
            /\ m.to = 2
            /\ m.body.id = 1
            /\ HandleAccept(m)
       /\ counter' = 6

    \/ /\ counter = 6
       /\ \E m \in msgs :
            /\ m.type = TypeAcceptOK
            /\ m.from = 1
            /\ m.to = 1
            /\ m.body.id = 1
            /\ HandleAcceptOK(m)
       /\ counter' = 7

ProtocolNext ==
    \/ \E m \in msgs :
         \/ HandlePreAccept(m)
         \/ HandlePreAcceptOK(m)
         \/ HandleAccept(m)
         \/ HandleAcceptOK(m)
         \/ HandleCommit(m)
         \/ HandleRecover(m)
         \/ HandleRecoverOK(m)
         \/ HandleValidate(m)
         \/ HandleValidateOK(m)
         \/ HandlePostWaitingMsg(m)

    \/ \E q \in Proc, id \in Id, c \in Cmd :
         Submit(q, id, c)

    \/ \E p \in Proc, id \in Id :
         StartRecover(p, id)

Next ==
    \/ Prefix
    \/ (counter >= 7 /\ ProtocolNext /\ counter' = counter)





Spec ==
    Init /\ [][Next]_<< vars >>

=============================================================================
