----------------------------- MODULE EPaxosCommitWithRecovery -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC


CONSTANTS
    Proc,           \* set of processes
    F,              \* max # crash failures
    E,              \* e-fast parameter (E ≤ F)
    Cmd,            \* set of command payloads
    Id,             \* command identifiers  
    NoCmd,           \* special value representing no command
    NoProc,          \* special value representing no process
    NumberOfRecoveryAttempts \* maximum number of recovery attempts per process and command to avoid state space explosion

ASSUME E <= F

N == Cardinality(Proc)
QuorumSize == N - F

\*Phases
(* Initial = 1
   PreAccepted = 2
   Accepted = 3
   Committed = 4 *)
CONSTANTS 
    InitialPhase, PreAcceptedPhase, AcceptedPhase, CommittedPhase

\* Message types
(* 1 = PreAccept
2 = PreAcceptOK
3 = Accept
4 = AcceptOK
5 = Commit
6 = Recover
7 = RecoverOK
8 = Validate
9 = ValidateOK
10 = Waiting
11 = PostWaiting *)
CONSTANTS 
TypePreAccept,
TypePreAcceptOK,
TypeAccept,     
TypeAcceptOK,    
TypeCommit,        
TypeRecover,      
TypeRecoverOK,  
TypeValidate,     
TypeValidateOK,    
TypeWaiting,      
TypePostWaiting 

Message(type, from, to, body) ==
    [ type |-> type, from |-> from, to |-> to, body |-> body ]

PreAcceptMsg(p, q, id, c, D) ==
    Message(TypePreAccept, p, q,
        [ id  |-> id,
          c |-> c,
          D |-> D ])

PreAcceptOKMsg(p, q, id, Dq) ==
    Message(TypePreAcceptOK, p, q,
        [ id  |-> id,
          Dq |-> Dq ])

AcceptMsg(p, q, b, id, c, D) ==
    Message(TypeAccept, p, q,
        [ id   |-> id,
          b  |-> b,
          c |-> c,
          D |-> D ])

AcceptOKMsg(p, q, b, id) ==
    Message(TypeAcceptOK, p, q,
        [ id  |-> id,
          b |-> b ])

CommitMsg(p, q, b, id, c, D) ==
    Message(TypeCommit, p, q,
        [ id   |-> id,
          b  |-> b,
          c |-> c,
          D |-> D ])

RecoverMsg(p,q,b,id) ==
    Message(TypeRecover,p,q,[ b |->b,id|->id])

RecoverOKMsg(p,q,b,id,abalq,cq,depq,initDepq,phaseq) ==
    Message(TypeRecoverOK,p,q,
        [ b|->b, id|->id, abalq|->abalq, cq|->cq,
          depq|->depq, initDepq|->initDepq, phaseq|->phaseq ])

ValidateMsg(p,q,b,id,c,D,Q,Rmax) ==
    Message(TypeValidate,p,q,[b|->b,id|->id,c|->c,D|->D,Q|->Q,Rmax|->Rmax])

ValidateOKMsg(p,q,b,id,D,I,Q,Rmax) ==
    Message(TypeValidateOK,p,q,[b|->b,id|->id,I|->I,D|->D,Q|->Q,Rmax|->Rmax])

WaitingMsg(p,q,id,k) ==
    Message(TypeWaiting,p,q,[id|->id,k|->k])

PostWaitingMsg(p,id,I,Q,b) ==
    Message(TypePostWaiting,p,p,[id|->id,I|->I,Q|->Q, b|->b])

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
    recovered      \* counter of times recoverd per (p,id)

vars ==
    << bal, abal, cmd, initCmd, dep, initDep, phase, msgs,
       submitted, initCoord, recovered >>

(**********************************************************************
 * Initialization
 **********************************************************************)

Init ==
    /\ bal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ abal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ cmd = [p \in Proc |-> [id \in Id |-> NoCmd]]
    /\ initCmd = [p \in Proc |-> [id \in Id |-> NoCmd]]
    /\ dep = [p \in Proc |-> [id \in Id |-> {}]]
    /\ initDep = [p \in Proc |-> [id \in Id |-> {}]]
    /\ phase = [p \in Proc |-> [id \in Id |-> InitialPhase]]
    /\ initCoord = [id \in Id |-> NoProc]
    /\ submitted = {}
    /\ recovered = [p \in Proc |-> [id \in Id |-> 0]]
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
        /\ phase[p][id2] # InitialPhase 
        /\ Conflicts(cmd[p][id2], c)
    }

(**********************************************************************
 * Actions
 **********************************************************************)

Submit(p, id, c) ==
    /\ id \notin submitted
    /\ LET D0 == ConflictingIds(p, c)
       IN
          /\ submitted' = submitted \cup {id}
          /\ initCoord' = [initCoord EXCEPT ![id] = p]
          /\ msgs' = msgs \cup
                { PreAcceptMsg(p, q, id, c, D0) : q \in Proc }
          /\ UNCHANGED << phase, bal, cmd, initCmd, initDep,
                           dep, abal, recovered >> 

HandlePreAccept(m) ==
    /\ m.type = TypePreAccept
    /\ LET p  == m.to
           q  == m.from
           id == m.body.id
           c  == m.body.c
           D  == m.body.D
       IN 
          /\ bal[p][id] = 0
          /\ phase[p][id] = InitialPhase
          /\ cmd' = [cmd EXCEPT ![p][id] = c]
          /\ initCmd' = [initCmd EXCEPT ![p][id] = c]
          /\ initDep' = [initDep EXCEPT ![p][id] = D]
          /\ LET Dp == ConflictingIds(p, c)
             IN LET Dfinal == D \cup Dp
                IN /\ dep' = [dep EXCEPT ![p][id] = Dfinal]
                   /\ msgs' = (msgs \cup {
                           PreAcceptOKMsg(p, q, id, Dfinal)
                       }) \ {m}
          /\ phase' = [phase EXCEPT ![p][id] = PreAcceptedPhase]
          /\ UNCHANGED << abal, submitted, bal, initCoord, recovered >>

HandlePreAcceptOK(m) ==
    /\ m.type = TypePreAcceptOK
    /\ LET p  == m.to
           q  == m.from
           id == m.body.id
           Dq == m.body.Dq
       IN
       /\ bal[p][id] = 0
       /\ phase[p][id] = PreAcceptedPhase
       /\ p = initCoord[id]
       /\ LET quorum ==
              { q2 \in Proc :
                  \E k \in msgs :
                      /\ k.type = TypePreAcceptOK
                      /\ k.body.id = id
                      /\ k.to = p
                      /\ k.from = q2
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
             /\ LET Dfinal == UNION { k.body.Dq : k \in OKs }
                IN
                /\ IF FastQuorum(quorum)
                      /\ \A k \in OKs :
                            k.body.Dq = initDep[p][id]
                   THEN
                      /\ msgs' =
                           (msgs \ OKs) \cup
                           { CommitMsg(p, q2, 0, id,
                                        cmd[p][id], Dfinal)
                             : q2 \in Proc }
                   ELSE
                      /\ msgs' =
                           (msgs \ OKs) \cup
                           { AcceptMsg(p, q2, 0, id,
                                        cmd[p][id], Dfinal)
                             : q2 \in Proc }
    /\ UNCHANGED << bal, phase, cmd, initCmd,
                     initDep, dep, abal,
                     submitted, initCoord, recovered >>

HandleAccept(m) ==
    /\ m.type = TypeAccept
    /\ LET p  == m.to
           q  == m.from
           b  == m.body.b
           id == m.body.id
           c  == m.body.c
           D  == m.body.D
       IN
       /\ bal[p][id] <= b
       /\ (bal[p][id] = b => phase[p][id] # CommittedPhase)
       /\ bal'  = [bal  EXCEPT ![p][id] = b]
       /\ abal' = [abal EXCEPT ![p][id] = b]
       /\ cmd'  = [cmd  EXCEPT ![p][id] = m.body.c]
       /\ dep'  = [dep  EXCEPT ![p][id] = m.body.D]
       /\ phase' = [phase EXCEPT ![p][id] = AcceptedPhase]
       /\ msgs' =
           (msgs \ {m}) \cup
           { AcceptOKMsg(p, q, b, id) }
    /\ UNCHANGED << initCmd, initDep,
                      submitted, initCoord, recovered >>


HandleAcceptOK(m) ==
    /\ m.type = TypeAcceptOK
    /\ LET p  == m.to
           q  == m.from
           b  == m.body.b
           id == m.body.id    
       IN
       /\ bal[p][id] = b
       /\ phase[p][id] = AcceptedPhase
       /\ LET quorum ==
              { q2 \in Proc :
                  \E k \in msgs :
                      /\ k.type = TypeAcceptOK
                      /\ k.body.id = id
                      /\ k.to = p
                      /\ k.from = q2
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
                     CommitMsg(p, q2, b, id, cmd[p][id], dep[p][id])
                       : q2 \in Proc
                }) \ OKs
             /\ UNCHANGED << bal, phase, cmd, initCmd,
                              initDep, dep, abal, submitted, initCoord, recovered >>

HandleCommit(m) ==
    /\ m.type = TypeCommit
    /\ LET p == m.to
           q == m.from
           b  == m.body.b
           id == m.body.id
           c  == m.body.c
           D  == m.body.D
       IN
       /\ bal[p][id] = b
       /\ abal' = [abal EXCEPT ![p][id] = b]
       /\ cmd' = [cmd EXCEPT ![p][id] = c]
       /\ dep' = [dep EXCEPT ![p][id] = D]
       /\ phase' = [phase EXCEPT ![p][id] = CommittedPhase]
       /\ msgs' = msgs \ {m}
       /\ UNCHANGED << bal, initCmd, initDep,
                        submitted, initCoord, recovered >>

(***************************************************************************)
(* 44–45 StartRecover                                                      *)
(***************************************************************************)
StartRecover(p,id) ==
    \* We count the number of times a process has tried to recover a command to avoid model checker exploding
    /\ recovered[p][id] < NumberOfRecoveryAttempts
    /\ recovered' = [recovered EXCEPT ![p][id] = recovered[p][id] + 1]
    \* Ballots owned by p are of the form k*N + p.
    /\ LET  b == IF bal[p][id] = 0 THEN p ELSE bal[p][id] + Cardinality(Proc)
       IN
        /\ bal' = [bal EXCEPT ![p][id] = b]
        /\ msgs' = msgs \cup { RecoverMsg(p,q,b,id) : q \in Proc }
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
           q == m.from
           b == m.body.b
           id == m.body.id
           abalq == m.body.abalq
           cq == m.body.cq
           depq == m.body.depq
           initDepq == m.body.initDepq
           phaseq == m.body.phaseq
       IN
       /\ bal[p][id] = b
       /\ LET Q ==
               { q2 \in Proc :
                   \E k \in msgs :
                       k.type = TypeRecoverOK /\ k.to = p /\ k.from = q2 /\
                       k.body.id = id /\ k.body.b = b }
           OKs ==
               { k \in msgs :
                   k.type = TypeRecoverOK /\ k.to = p /\ k.from \in Q /\
                   k.body.id = id /\ k.body.b = b }
           Abals == { k.body.abalq : k \in OKs }
           bmax == CHOOSE val \in Abals : \A val2 \in Abals : val >= val2
           U == { k \in OKs : k.body.abalq = bmax }
          IN
            /\ Cardinality(Q) >= QuorumSize
            /\ \/ (\E q2 \in Proc :
                        \E n \in U :
                                n.from = q2
                                /\ n.body.phaseq = CommittedPhase
                                /\ msgs' =
                                    (msgs \ OKs) \cup
                                    { CommitMsg(p, q3, b, id, n.body.cq, n.body.depq)
                                        : q3 \in Proc })

                \/ (\E q2 \in Proc :
                        \E n \in U :
                                n.from = q2
                                /\ n.body.phaseq = AcceptedPhase
                                /\ msgs' =
                                    (msgs \ OKs) \cup
                                    { AcceptMsg(p, q3, b, id, n.body.cq, n.body.depq)
                                        : q3 \in Proc })

                \/ (initCoord[id] \in Q
                    /\ msgs' =
                        (msgs \ OKs) \cup
                        { AcceptMsg(p, q2, b, id, NoCmd, {}) : q2 \in Proc })
                \/ (/\ LET Rsubsets == SUBSET(Q)
                        IN
                        LET validRsubsets == {R \in Rsubsets : 
                                            Cardinality(R) >= Cardinality(Q) - E 
                                            /\ \A q2 \in R : 
                                                    \E n \in U :
                                                        n.from = q2
                                                        /\ n.body.phaseq = PreAcceptedPhase
                                                        /\ n.body.depq = n.body.initDepq  }
                        IN
                        LET Rmax == CHOOSE R \in validRsubsets :
                                        \A R2 \in validRsubsets :
                                            Cardinality(R) >= Cardinality(R2)
                        IN
                        LET n ==
                                CHOOSE n \in U :
                                    \E q2 \in Rmax :
                                        n.from = q2 /\
                                        n.body.phaseq = PreAcceptedPhase /\

                                        n.body.depq = n.body.initDepq
                        IN
                        LET c == n.body.cq
                            D == n.body.depq
                        IN /\ msgs' =
                                (msgs \ OKs) \cup
                                { ValidateMsg(p, q2, b, id, c, D, Q, Cardinality(Rmax)) \*passing Q and Rmax because we still need them in the rest of the recoverOK, but in my TLA here the following will be in validateOK
                                    : q2 \in Q })
       /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase,
                        submitted, initCoord, recovered >>

(***************************************************************************)
(* 84–90 HandleValidate                                                    *)
(***************************************************************************)
HandleValidate(m) ==
    /\ m.type = TypeValidate
    /\ LET p == m.to
           q == m.from
           id == m.body.id
           c == m.body.c
           D == m.body.D
           b == m.body.b
           Q == m.body.Q
           Rmax == m.body.Rmax
       IN
       /\ bal[p][id] = b
       /\ cmd' = [cmd EXCEPT ![p][id] = c]
       /\ initCmd' = [initCmd EXCEPT ![p][id] = c]
       /\ initDep' = [initDep EXCEPT ![p][id] = D]
       /\ LET idsForI == 
              { id2 \in Id :
                  id2 # id /\ 
                  ~((phase[p][id2] = CommittedPhase 
                      => cmd[p][id2] # NoCmd /\ id \notin dep[p][id2] /\ Conflicts(c, cmd[p][id2]))
                    /\ (phase[p][id2] # CommittedPhase 
                      => initCmd[p][id2] # NoCmd /\ id \notin initDep[p][id2] /\ Conflicts(c, initCmd[p][id2]))) }
          IN
          LET I == 
              { <<id2, phase[p][id2]>> : id2 \in idsForI }
          IN
          /\ msgs' =
               (msgs \ {m}) \cup
               { ValidateOKMsg(p, q, b, id, D, I, Q, Rmax) }
          /\ UNCHANGED << bal, abal, dep, phase,
                        submitted, initCoord, recovered >>

(***************************************************************************)
(* 64–70 HandleValidateOK                                                  *)
(***************************************************************************)
HandleValidateOK(m) ==
    /\ m.type = TypeValidateOK
    /\ LET p == m.to
           q == m.from
           id == m.body.id
           b  == m.body.b
           c  == m.body.c
           D  == m.body.D
           Iq  == m.body.I
           Q  == m.body.Q
           Rmax == m.body.Rmax
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
        /\  \/ (I = {}
                /\ msgs' = (msgs \ OKs) \cup
                    { AcceptMsg(p, q2, b, id, c, D) : q2 \in Proc })
            \/ (((\E x \in I : x[2] = CommittedPhase) \/ (Rmax = Cardinality(Q) - E /\ \E x \in I : initCoord[x[1]] \notin Q))
                /\ msgs' = (msgs \ OKs) \cup
                    { AcceptMsg(p, q2, b, id, NoCmd, {}) : q2 \in Proc })
            \/ (msgs' = (msgs \ OKs) \cup
                { WaitingMsg(p, q2, id, Rmax) : q2 \in Proc } \cup
                { PostWaitingMsg(p, id, I, Q, b) })


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
       IN /\ b = bal[p][id]
        \/ (\E x \in I :
                x[1] # id /\
                x[2] = CommittedPhase /\
                cmd[p][x[1]] # NoCmd /\
                id \notin dep[p][x[1]]
            /\ msgs' =
                    msgs \cup
                    { AcceptMsg(p, q, bal[p][id], id, NoCmd, {}) : q \in Proc })

        \/ (\A x \in I :
                x[1] # id =>
                (x[2] = CommittedPhase /\
                    (cmd[p][x[1]] = NoCmd \/ id \in dep[p][x[1]]))
            /\ msgs' =
                    msgs \cup
                    { AcceptMsg(p, q, bal[p][id], id, cmd[p][id], dep[p][id])
                        : q  \in Proc })

        \/ (\E x \in I :
                x[1] # id /\
                \E m2 \in msgs :
                    m2.type = TypeWaiting /\
                    m2.to = p /\
                    m2.body.id = x[1] /\
                    m2.body.k > N - F - E
            /\ msgs' =
                    msgs \cup
                    { AcceptMsg(p, q, bal[p][id], id, NoCmd, {}) : q \in Proc })

        \/ (\E m2 \in msgs :
                m2.type = TypeRecoverOK /\
                m2.to = p /\
                m2.body.id = id /\
                m2.from \notin m2.body.Q /\
                (m2.body.phase = CommittedPhase \/
                    m2.body.phase = AcceptedPhase \/
                    m2.from = initCoord[id])
            /\ msgs' =
                msgs \cup
                IF m2.body.phase = CommittedPhase THEN
                    { CommitMsg(p, q, bal[p][id], id,
                                m2.body.cmd, m2.body.dep) : q \in Proc }
                ELSE IF m2.body.phase = AcceptedPhase THEN
                    { AcceptMsg(p, q, bal[p][id], id,
                                m2.body.cmd, m2.body.dep) : q \in Proc }
                ELSE
                    { AcceptMsg(p, q, bal[p][id], id, NoCmd, {}) : q \in Proc })

    /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase,
                        submitted, initCoord, recovered >>
                       

Agreement ==
  \A id \in Id :
    \A p, q \in Proc :
      /\ phase[p][id] = CommittedPhase
      /\ phase[q][id] = CommittedPhase
      => /\ dep[p][id] = dep[q][id]
         /\ cmd[p][id] = cmd[q][id]

Visibility ==
  \A id, id2 \in Id : \E p, q \in Proc :
    /\ id # id2
    /\ phase[p][id] = CommittedPhase
    /\ phase[q][id2] = CommittedPhase
    /\ Conflicts(cmd[p][id], cmd[q][id2])
    => \/ id \in dep[q][id2]
       \/ id2 \in dep[p]    [id]


Liveness ==
    \A id \in Id :
      id \in submitted
      => \E p \in Proc :
           phase[p][id] = CommittedPhase

TypeInv ==
    /\ \A p \in Proc, id \in Id :
        /\ bal[p][id] >= 0 
        /\ abal[p][id] >= 0
        /\ (cmd[p][id] \in Cmd \/ cmd[p][id] = NoCmd)
        /\ (initCmd[p][id] \in Cmd \/ initCmd[p][id] = NoCmd)
        /\ dep[p][id] \subseteq Id
        /\ initDep[p][id] \subseteq Id
        /\ phase[p][id] \in {InitialPhase, PreAcceptedPhase, AcceptedPhase, CommittedPhase}
        /\ recovered[p][id] >= 0 /\ recovered[p][id] <= NumberOfRecoveryAttempts

    /\ \A m \in msgs :
        m.type \in {TypePreAccept, TypePreAcceptOK, TypeAccept, TypeAcceptOK, TypeCommit,
                    TypeRecover, TypeRecoverOK, TypeValidate, TypeValidateOK,
                    TypeWaiting, TypePostWaiting} 
    
    /\ \A id \in Id :
        /\ initCoord[id] \in Proc \cup {NoProc}
    /\ submitted \subseteq Id
(**********************************************************************
 * Next-state relation
 **********************************************************************)



Next ==
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



Spec ==
    Init /\ [][Next]_<< vars >> /\ WF_vars(Next)

=============================================================================
