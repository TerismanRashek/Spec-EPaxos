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

ValidateMsg(p,q,b,id,c,D) ==
    Message(TypeValidate,p,q,[b|->b,id|->id,c|->c,D|->D])

ValidateOKMsg(p,q,b,id,c,D,I) ==
    Message(TypeValidateOK,p,q,[b|->b,id|->id,c|->c,D|->D,I|->I])

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
    recovered,     \* counter of times recoverd per (p,id)
    

    \* These variables are used to persist to local state in the RecoverOK part, which is split in 3 in my TLA spec.
    I,             \* I[p]][id] used to keep track of I set in validateOK handler, which we need in PostWaiting handler.
    Q,             \* Q[p][id] and CardinalityRmax[p][id] : temporary variables used in recoverOK handler to avoid having to pass what is local state in messages,
    CardinalityRmax\* they only appear because I have the split the pseudocode of RecoverOK in 3 handlers and these local variables are lost from one handler to the other.    
    recoveryState  \* recoveryState[p][id] : variable to keep track of which step of the recoverOK handler p is in.

CONSTANTS InitialrecoveryState, RecoverOKState, ValidateOKState, PostWaitingState

vars ==
    << bal, abal, cmd, initCmd, dep, initDep, phase, msgs,
       submitted, initCoord, recovered, Q, CardinalityRmax, recoveryState >>

(***************************************************************************)
(* Initialisation                                                            *)
(***************************************************************************)

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
    /\ I = [p \in Proc |-> [id \in Id |-> {}]]
    /\ Q = [p \in Proc |-> [id \in Id |-> {}]]
    /\ CardinalityRmax = [p \in Proc |-> [id \in Id |-> 0]]
    /\ recoveryState = [p \in Proc |-> [id \in Id |-> InitialrecoveryState]]

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)

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

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

(***************************************************************************)
(* 8–10 Submit                                                             *)
(***************************************************************************)

Submit(p, id, c) ==
    /\ id \notin submitted
    /\ LET D0 == ConflictingIds(p, c)
       IN
          /\ submitted' = submitted \cup {id}
          /\ initCoord' = [initCoord EXCEPT ![id] = p]
          /\ msgs' = msgs \cup
                { PreAcceptMsg(p, q, id, c, D0) : q \in Proc }
          /\ UNCHANGED << phase, bal, cmd, initCmd, initDep,
                           dep, abal, recovered, Q, CardinalityRmax, recoveryState >> 

(***************************************************************************)
(* 11–18 HandlePreAccept                                                   *)
(***************************************************************************)                    

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
          /\ UNCHANGED << abal, submitted, bal, initCoord, recovered, Q, CardinalityRmax, recoveryState  >>

(***************************************************************************)
(* 19–25 HandlePreAcceptOk                                                 *)
(***************************************************************************)


HandlePreAcceptOK(p, id) ==
    /\ bal[p][id] = 0
    /\ phase[p][id] = PreAcceptedPhase
    /\ p = initCoord[id]
    /\ LET fullMessageSet ==
            {  m \in msgs :
                    /\ m.type = TypePreAcceptOK
                    /\ m.body.id = id
                    /\ m.to = p
            }
        IN
        /\ \E m \in fullMessageSet : m.from = p
        \* question here, I assume that delivering self messages instantly implies that the sender is always in the quorum. This was the case when handler triggered of that
        \* specific message, but now initCoord may not be in the quorum. I suppose I should add a precondition that the self-sent preAcceptOK is in fullMessageSet?
        /\ Quorum(fullMessageSet)
        \* I build the set of fast quorums from the messages, check if there is at least one, and CHOOSE it deterministically
        /\ LET fastQuorums ==
                { Q \in  SUBSET(fullMessageSet) :
                    \A m in Q : m.body.Dq = initDep[p][id] /\ FastQuorum(Q) }
           IN
            /\ IF fastQuorums # {} THEN
                    LET Q == CHOOSE Q \in fastQuorums : TRUE
                    IN
                    LET Dfinal == UNION { m.body.Dq : m \in Q }
                    IN
                    /\ msgs' =
                        (msgs \ fullMessageSet) \cup \* can I remove the fullMessageSet here? I am pretty sure I can but just in case I'm missing something.
                        { CommitMsg(p, q, 0, id, cmd[p][id], Dfinal) : q \in Proc }
               ELSE
                    \* If fast path fails, I just take the quorum with all the messages, there is no need to check in the same way as the fast path        
                    LET Dfinal == UNION { m.body.Dq : m \in fullMessageSet }
                    IN
                    /\ msgs' =
                        (msgs \ fullMessageSet) \cup
                        { AcceptMsg(p, q, 0, id, cmd[p][id], Dfinal) : q \in Proc }
    /\ UNCHANGED << bal, phase, cmd, initCmd,
                     initDep, dep, abal,
                     submitted, initCoord, recovered, Q, CardinalityRmax, recoveryState  >>
                   
(***************************************************************************)
(* 26–33 HandleAccept                                                      *)
(***************************************************************************)                            

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
                      submitted, initCoord, recovered, Q, CardinalityRmax, recoveryState  >>

(***************************************************************************)
(* 34–36 HandleAcceptOk                                                    *)
(***************************************************************************)

(*  Here, it's very clunky to go find the self sent message only to recover the b value, but if I include it in the parameters of the handler
 the precondition would make it correct but then the next state relation needs something like :
     \/ \E p \in Proc, id \in ID, b \in Nat
            HandleAcceptOK(p, id, b)
    but the \E b \in Nat is not okay. 
  *)
HandleAcceptOK(p, id) ==
    /\ LET m == CHOOSE m \in msgs : m.type = TypeAcceptOK /\ m.to = p /\ m.from = p /\ m.body.id = id 
       IN
       LET b == m.body.b
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
                initDep, dep, abal, submitted, initCoord, recovered, Q, CardinalityRmax, recoveryState  >>

(***************************************************************************)
(* 37–42 HandleCommit                                                      *)
(***************************************************************************)
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
                        submitted, initCoord, recovered, Q, CardinalityRmax, recoveryState  >>

(***************************************************************************)
(* 43–45 StartRecover                                                      *)
(***************************************************************************)
StartRecover(p,id) ==
    \* We count the number of times a process has tried to recover a command to avoid model checker exploding
    /\ recovered[p][id] < NumberOfRecoveryAttempts
    /\ recovered' = [recovered EXCEPT ![p][id] = recovered[p][id] + 1]
    \* Ballots owned by p are of the form k*N + p.
    /\ LET  b == IF bal[p][id] = 0 THEN p ELSE bal[p][id] + Cardinality(Proc)
       IN
        /\ msgs' = msgs \cup { RecoverMsg(p,q,b,id) : q \in Proc }
        /\ recoveryState' = [recoveryState EXCEPT ![p][id] = RecoverOKState]
        /\ UNCHANGED << abal, cmd, initCmd, dep, initDep, phase,
                            submitted, initCoord, Q, CardinalityRmax, recoveryState  >>

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
                        submitted, initCoord, recovered, Q, CardinalityRmax, recoveryState  >>

(***************************************************************************)
(* 50–60 HandleRecoverOK                                                   *)
(***************************************************************************)
HandleRecoverOK(p, id) ==
    /\ recoveryState[p][id] = RecoverOKState
    /\ LET m == CHOOSE m \in msgs : m.type = TypeRecoverOK /\ m.to = p /\ m.from = p /\ m.body.id = id /\ m.body.b = bal[p][id]
        IN
        /\ LET b == m.body.b
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
                    \/ (/\ LET Rmax == { q2 \in Q :
                                        \E n \in U :
                                            n.from = q2
                                            /\ n.body.phaseq = PreAcceptedPhase
                                            /\ n.body.depq = n.body.initDepq }
                            IN
                            LET n == CHOOSE n \in U :
                                            n.from \in Rmax /\
                                            n.body.phaseq = PreAcceptedPhase /\
                            IN
                            LET c == n.body.cq
                                D == n.body.depq
                            IN
                            /\ Q' = [Q  EXCEPT ![p][id] = Q]
                            /\ CardinalityRmax' = [CardinalityRmax EXCEPT ![p][id] = Cardinality(Rmax)]
                            /\ recoveryState' = [recoveryState EXCEPT ![p][id] = ValidateOKState]
                            /\ msgs' =
                                    (msgs \ OKs) \cup
                                    { ValidateMsg(p, q2, b, id, c, D)
                                        : q2 \in Q })
       /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase,
                        submitted, initCoord, recovered >>

(***************************************************************************)
(* 81–87 HandleValidate                                                    *)
(***************************************************************************)
HandleValidate(m) ==
    /\ m.type = TypeValidate
    /\ LET p == m.to
           q == m.from
           id == m.body.id
           c == m.body.c
           D == m.body.D
           b == m.body.b
       IN
       /\ bal[p][id] = b
       /\ cmd' = [cmd EXCEPT ![p][id] = c]
       /\ initCmd' = [initCmd EXCEPT ![p][id] = c]
       /\ initDep' = [initDep EXCEPT ![p][id] = D]
       /\ LET I == 
              { <<id2, phase[p][id2]>> : id2 \in Id :
                  id2 # id /\ id2 \notin D /\
                    ((phase[p][id2] = CommittedPhase 
                      => ( cmd[p][id2] # NoCmd /\ id \notin dep[p][id2] /\ Conflicts(c, cmd[p][id2]) ))
                    /\ (phase[p][id2] # CommittedPhase 
                      => initCmd[p][id2] # NoCmd /\ id \notin initDep[p][id2] /\ Conflicts(c, initCmd[p][id2])))
              }
          IN
          /\ msgs' =
               (msgs \ {m}) \cup
               { ValidateOKMsg(p, q, b, id, c, D, I) }
          /\ UNCHANGED << bal, abal, dep, phase,
                        submitted, initCoord, recovered, Q, CardinalityRmax  >>

(***************************************************************************)
(* 61–68 HandleValidateOK                                                  *)
(***************************************************************************)
HandleValidateOK(p, id) ==
    /\ recoveryState[p][id] = ValidateOKState
    /\ LET b  == bal[p][id]
           Q  == Q[p][id]
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
        /\ recoveryState' = [recoveryState EXCEPT ![p][id] = PostWaitingState] 
        /\ I' = [I EXCEPT ![p][id] = I]
        /\  \/ (I = {}
                /\ msgs' = (msgs \ OKs) \cup
                    { AcceptMsg(p, q2, b, id, c, D) : q2 \in Proc })
            \/ (((\E x \in I : x[2] = CommittedPhase) \/ (CardinalityRmax[p][id] = Cardinality(Q) - E /\ \E x \in I : initCoord[x[1]] \notin Q))
                /\ msgs' = (msgs \ OKs) \cup
                    { AcceptMsg(p, q2, b, id, NoCmd, {}) : q2 \in Proc })
            \/ (msgs' = (msgs \ OKs) \cup
                { WaitingMsg(p, q2, id, CardinalityRmax[p][id]) : q2 \in Proc })


    /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase,submitted, initCoord, recovered, Q, CardinalityRmax  >>

(***************************************************************************)
(* 69–80 HandlePostWaitingMsg                                                 *)
(***************************************************************************)
                    
HandlePostWaiting(p, id) ==
    /\ recoveryState[p][id] = PostWaitingState
    /\ LET 
           I == I[p][id]
           Q == Q[p][id]
           b == bal[p][id] \* bal[id] = b as a precondition of RecoverOK so I can conflate the two
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


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)                 

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
       \/ id2 \in dep[p][id]


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


(***************************************************************************)
(* Next State Relation                                                     *)
(***************************************************************************)

Next ==
    \/ \E m \in msgs :
          \/ HandlePreAccept(m)
          \/ HandleAccept(m)
          \/ HandleCommit(m)

          \/ HandleRecover(m)
          \/ HandleValidate(m)

    \/ \E q \in Proc, id \in Id, c \in Cmd :
          Submit(q, id, c)

    \/ \E p \in Proc, id \in Id :
          StartRecover(p, id)
          HandlePreAcceptOK(p, id)
          HandleValidateOK(p, id)
          HandlePostWaiting(p, id)
          HandleRecoverOK(p, id)
          HandleAcceptOK(p, id)





Spec ==
    Init /\ [][Next]_<< vars >> /\ WF_vars(Next)

=============================================================================
