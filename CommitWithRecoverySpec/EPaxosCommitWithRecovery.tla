----------------------------- MODULE EPaxosCommitWithRecovery -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC


CONSTANTS
    Proc,           \* set of processes
    F,              \* max # crash failures
    E,              \* e-fast parameter (E ≤ F)
    Cmd,            \* set of command payloads
    Id,             \* command identifiers  
    Nop,           \* special value representing no command
    Bottom,         \* special value for bottom command payload
    NoProc,          \* special value representing no process
    NumberOfRecoveryAttempts \* maximum number of recovery attempts per process and command to avoid state space explosion

ASSUME E <= F

N == Cardinality(Proc)
QuorumSize == N - F

ASSUME QuorumSize > N \div 2

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

ValidateOKMsg(p,q,b,id,c,D,Iq) ==
    Message(TypeValidateOK,p,q,[b|->b,id|->id,c|->c,D|->D,Iq|->Iq])

WaitingMsg(p,q,id,k) ==
    Message(TypeWaiting,p,q,[id|->id,k|->k])

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
    Ivar,             \* I[p]][id] used to keep track of I set in validateOK handler, which we need in PostWaiting handler.
    Qvar,             \* Q[p][id] and CardinalityRmax[p][id] : temporary variables used in recoverOK handler to avoid having to pass what is local state in messages,
    CardinalityRmax,\* they only appear because I have the split the pseudocode of RecoverOK in 3 handlers and these local variables are lost from one handler to the other.    
    postWaitingFlag, 

    selfAddressedMessageFlag, \* bool to know when we have to switch off normal behaviour and immediately consume a message
    messageToDeliver   \*  a record to store what is needed to find message to consume

vars ==
    << bal, abal, cmd, initCmd, dep, initDep, phase, msgs,
       submitted, initCoord, recovered, Qvar, CardinalityRmax, Ivar, selfAddressedMessageFlag, messageToDeliver, postWaitingFlag >>

(***************************************************************************)
(* Initialisation                                                            *)
(***************************************************************************)

Init ==
    /\ bal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ abal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ cmd = [p \in Proc |-> [id \in Id |-> Bottom]]
    /\ initCmd = [p \in Proc |-> [id \in Id |-> Bottom]]
    /\ dep = [p \in Proc |-> [id \in Id |-> {}]]
    /\ initDep = [p \in Proc |-> [id \in Id |-> {}]]
    /\ phase = [p \in Proc |-> [id \in Id |-> InitialPhase]]
    /\ initCoord = [id \in Id |-> NoProc]
    /\ submitted = {}
    /\ recovered = [p \in Proc |-> [id \in Id |-> 0]]
    /\ msgs = {}
    /\ Ivar = [p \in Proc |-> [id \in Id |-> {}]]
    /\ Qvar = [p \in Proc |-> [id \in Id |-> {}]]
    /\ CardinalityRmax = [p \in Proc |-> [id \in Id |-> 0]]
    /\ selfAddressedMessageFlag = FALSE
    /\ messageToDeliver = 0
    /\ postWaitingFlag = [p \in Proc |-> [id \in Id |-> FALSE]]

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)

Conflicts(c1, c2) ==
    IF c1 = Bottom \/ c2 = Bottom THEN
        FALSE
    ELSE IF c1 = Nop \/ c2 = Nop THEN
        TRUE
    ELSE
        c1 % 2 = c2 % 2

IsQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - F
IsFastQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - E

ConflictingIds(p, c) ==
    { id \in Id :
        /\ phase[p][id] # InitialPhase 
        /\ Conflicts(cmd[p][id], c)
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
                           dep, abal, recovered, Qvar, CardinalityRmax, Ivar, selfAddressedMessageFlag, messageToDeliver, postWaitingFlag >> 

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
                   /\ msgs' = (msgs \cup { PreAcceptOKMsg(p, q, id, Dfinal) }) \ {m}
          /\ phase' = [phase EXCEPT ![p][id] = PreAcceptedPhase]
          /\ UNCHANGED << abal, submitted, bal, initCoord, recovered, Qvar, CardinalityRmax, Ivar, selfAddressedMessageFlag, messageToDeliver, postWaitingFlag >>

(***************************************************************************)
(* 19–25 HandlePreAcceptOk                                                 *)
(***************************************************************************)


HandlePreAcceptOK(p, id) ==
    /\ bal[p][id] = 0
    /\ phase[p][id] = PreAcceptedPhase
    /\ p = initCoord[id]
    /\ LET quorumOfMessages ==
            {  m \in msgs :
                    /\ m.type = TypePreAcceptOK
                    /\ m.body.id = id
                    /\ m.to = p
            }
        IN
        /\ IsQuorumSized(quorumOfMessages)
        \* I build the set of fast quorums from the messages, check if there is at least one, and CHOOSE it deterministically
        /\ LET fastQuorums ==
                { quorum \in  SUBSET(quorumOfMessages) :
                    \A m \in quorum : m.body.Dq = initDep[p][id] /\ IsFastQuorumSized(quorum) }
           IN
            /\ IF fastQuorums # {} THEN
                    LET Q == CHOOSE Q \in fastQuorums : TRUE
                    IN
                    LET Dfinal == UNION { m.body.Dq : m \in quorumOfMessages }
                    IN
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(p, q, 0, id, cmd[p][id], Dfinal) : q \in Proc }
                    /\ selfAddressedMessageFlag' = TRUE
                    /\ messageToDeliver' = [ type |-> TypeCommit, p |-> p, id |-> id, b |-> 0, c |-> cmd[p][id], D |-> Dfinal ]
               ELSE
                    \* If fast path fails, I just take the quorum with all the messages, there is no need to check in the same way as the fast path        
                    LET Dfinal == UNION { m.body.Dq : m \in quorumOfMessages }
                    IN
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, 0, id, cmd[p][id], Dfinal) : q \in Proc }
                    /\ selfAddressedMessageFlag' = TRUE
                    /\ messageToDeliver' = [ type |-> TypeAccept, p |-> p, id |-> id, b |-> 0, c |-> cmd[p][id], D |-> Dfinal ]
    /\ UNCHANGED << bal, phase, cmd, initCmd, initDep, dep, abal, submitted, initCoord, recovered, Qvar, CardinalityRmax, Ivar, postWaitingFlag >>
                   
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
       /\ msgs' = (msgs \ {m}) \cup { AcceptOKMsg(p, q, b, id) }
       /\ selfAddressedMessageFlag' = FALSE
       /\ messageToDeliver' = 0
    /\ UNCHANGED << initCmd, initDep,
                      submitted, initCoord, recovered, Qvar, CardinalityRmax, Ivar, postWaitingFlag >>

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
    /\ phase[p][id] = AcceptedPhase
    /\ LET quorumOfMessages == { k \in msgs :
        /\ k.type = TypeAcceptOK
        /\ k.to = p
        /\ k.body.b = bal[p][id] \*Ballot precondition is here
        /\ k.body.id = id }   
        IN
        /\ IsQuorumSized(quorumOfMessages)
        /\ msgs' = (msgs \cup {CommitMsg(p, q, bal[p][id], id, cmd[p][id], dep[p][id]) : q \in Proc }) \ quorumOfMessages
        /\ selfAddressedMessageFlag' = TRUE
        /\ messageToDeliver' = [ type |-> TypeCommit, p |-> p, id |-> id, b |-> bal[p][id], c |-> cmd[p][id], D |-> dep[p][id] ]
    /\ UNCHANGED << bal, phase, cmd, initCmd,
                initDep, dep, abal, submitted, initCoord, recovered, Qvar, CardinalityRmax, Ivar, postWaitingFlag >>

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
       /\ selfAddressedMessageFlag' = FALSE
       /\ messageToDeliver' = 0
       /\ UNCHANGED << bal, initCmd, initDep,
                        submitted, initCoord, recovered, Qvar, CardinalityRmax, Ivar, postWaitingFlag >>

(***************************************************************************)
(* 43–45 StartRecover                                                      *)
(***************************************************************************)
StartRecover(p, id) ==
    /\ phase[p][id] # InitialPhase
    \* We count the number of times a process has tried to recover a command to avoid model checker exploding
    /\ recovered[p][id] < NumberOfRecoveryAttempts
    /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE] 
    /\ recovered' = [recovered EXCEPT ![p][id] = recovered[p][id] + 1]
    \* Ballots owned by p are of the form k*N + p.
    /\ LET  b == IF bal[p][id] = 0 THEN p ELSE bal[p][id] + Cardinality(Proc)
       IN
        /\ msgs' = msgs \cup { RecoverMsg(p,q,b,id) : q \in Proc }
        /\ UNCHANGED << abal, bal, cmd, initCmd, dep, initDep, phase,
                            submitted, initCoord, Qvar, CardinalityRmax, Ivar, selfAddressedMessageFlag, messageToDeliver >>

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
                        submitted, initCoord, recovered, Qvar, CardinalityRmax, Ivar, selfAddressedMessageFlag, messageToDeliver, postWaitingFlag >>

(***************************************************************************)
(* 50–60 HandleRecoverOK                                                   *)
(***************************************************************************)
HandleRecoverOK(p, id) ==
    /\  LET quorumOfMessages ==
        { k \in msgs :
            /\ k.type = TypeRecoverOK
            /\ k.to = p 
            /\ k.body.id = id 
            /\ k.body.b = bal[p][id]  } \* ballot precondition is here
        IN
        /\ IsQuorumSized(quorumOfMessages)
        /\  LET Q == { k.from : k \in quorumOfMessages}
                Abals == { k.body.abalq : k \in quorumOfMessages }
                bmax == CHOOSE val \in Abals : \A val2 \in Abals : val >= val2
                U == { k \in quorumOfMessages : k.body.abalq = bmax }
            IN
            /\  IF (\E n \in U :
                        /\ n.body.phaseq = CommittedPhase)
                THEN
                        /\  LET n == CHOOSE n \in U :
                                        n.body.phaseq = CommittedPhase
                            IN
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(p, q2, bal[p][id], id, n.body.cq, n.body.depq) : q2 \in Proc }
                            /\ selfAddressedMessageFlag' = TRUE
                            /\ messageToDeliver' = [ type |-> TypeCommit, p |-> p, id |-> id, b |-> bal[p][id], c |-> n.body.cq, D |-> n.body.depq ]
                            /\ UNCHANGED <<Qvar, CardinalityRmax>>

                ELSE    IF ( \E n \in U :
                            /\ n.body.phaseq = AcceptedPhase)
                        THEN    
                                /\  LET n == CHOOSE n \in U :
                                        n.body.phaseq = AcceptedPhase
                                    IN
                                    /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q2, bal[p][id], id, n.body.cq, n.body.depq) : q2 \in Proc }
                                    /\ selfAddressedMessageFlag' = TRUE
                                    /\ messageToDeliver' = [ type |-> TypeAccept, p |-> p, id |-> id, b |-> bal[p][id], c |-> n.body.cq, D |-> n.body.depq ]
                                    /\ UNCHANGED <<Qvar, CardinalityRmax>>

                ELSE    IF (/\ initCoord[id] \in Q)
                        THEN
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc }
                            /\ selfAddressedMessageFlag' = TRUE
                            /\ messageToDeliver' = [ type |-> TypeAccept, p |-> p, id |-> id, b |-> bal[p][id], c |-> Nop, D |-> {} ]
                            /\ UNCHANGED <<Qvar, CardinalityRmax>>

                ELSE    IF (    LET Rmax == { q \in Q :
                                    \E n \in U :
                                        n.from = q
                                        /\ n.body.phaseq = PreAcceptedPhase
                                        /\ n.body.depq = n.body.initDepq }
                                IN
                                /\  Cardinality(Rmax) >= QuorumSize - E )
                        THEN
                        LET Rmax == { q \in Q :
                                    \E n \in U :
                                        n.from = q
                                        /\ n.body.phaseq = PreAcceptedPhase
                                        /\ n.body.depq = n.body.initDepq }
                        IN
                        /\  LET n == CHOOSE n \in U :
                                        n.body.phaseq = PreAcceptedPhase /\ n.from \in Rmax
                            IN
                            LET c == n.body.cq
                                D == n.body.depq
                            IN
                            /\ Qvar' = [Qvar EXCEPT ![p][id] = Q]
                            /\ CardinalityRmax' = [CardinalityRmax EXCEPT ![p][id] = Cardinality(Rmax)]
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { ValidateMsg(p, q, bal[p][id], id, c, D) : q \in Q }
                            /\ UNCHANGED <<selfAddressedMessageFlag, messageToDeliver>>
                
                ELSE (/\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc }
                    /\ selfAddressedMessageFlag' = TRUE
                    /\ messageToDeliver' = [ type |-> TypeAccept, p |-> p, id |-> id, b |-> bal[p][id], c |-> Nop, D |-> {} ]
                    /\ UNCHANGED <<Qvar, CardinalityRmax>>)
    
    /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase, submitted, initCoord, recovered, Ivar, postWaitingFlag >>

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
              { <<id2, phase[p][id2]>> : id2 \in { id3 \in Id :
                  id3 # id /\ id3 \notin D /\
                    ((phase[p][id3] = CommittedPhase 
                      => ( cmd[p][id3] # Bottom /\ id \notin dep[p][id3] /\ Conflicts(c, cmd[p][id3]) ))
                    /\ (phase[p][id3] # CommittedPhase 
                      => initCmd[p][id3] # Bottom /\ id \notin initDep[p][id3] /\ Conflicts(c, initCmd[p][id3]))) }
              }
          IN
          /\ msgs' = (msgs \ {m}) \cup { ValidateOKMsg(p, q, b, id, c, D, I) }
          /\ UNCHANGED << bal, abal, dep, phase,
                        submitted, initCoord, recovered, Qvar, CardinalityRmax, Ivar , selfAddressedMessageFlag, messageToDeliver, postWaitingFlag >>

(***************************************************************************)
(* 61–68 HandleValidateOK                                                  *)
(***************************************************************************)
HandleValidateOK(p, id) ==
    /\  LET Q  == Qvar[p][id]
        IN 
        LET quorumOfMessages ==
            { m \in msgs :
                /\ m.type = TypeValidateOK 
                /\ m.to = p 
                /\ m.body.id = id 
                /\ m.body.b = bal[p][id] } \* must recheck Im still in the same ballot
            I == UNION { m.body.Iq : m \in quorumOfMessages }
        IN
        /\  IsQuorumSized(quorumOfMessages)     
        /\  LET m == CHOOSE m \in quorumOfMessages : TRUE
            IN 
            LET c == m.body.c
                D == m.body.D
            IN      
            /\  IF (I = {}) THEN
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, c, D) : q \in Proc }
                    /\ selfAddressedMessageFlag' = TRUE
                    /\ messageToDeliver' = [ type |-> TypeAccept, p |-> p, id |-> id, b |-> bal[p][id], c |-> c, D |-> D ]
                    /\ UNCHANGED <<Ivar, postWaitingFlag>>
                            
                ELSE IF 
                    ((\E x \in I : x[2] = CommittedPhase) \/ (CardinalityRmax[p][id] = Cardinality(Q) - E /\ \E x \in I : initCoord[x[1]] \notin Q))
                    THEN
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc }
                    /\ selfAddressedMessageFlag' = TRUE
                    /\ messageToDeliver' = [ type |-> TypeAccept, p |-> p, id |-> id, b |-> bal[p][id], c |-> Nop, D |-> {} ]    
                    /\ UNCHANGED <<Ivar, postWaitingFlag>>
                            
                ELSE (/\ Ivar' = [Ivar EXCEPT ![p][id] = I]
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { WaitingMsg(p, q, id, CardinalityRmax[p][id]) : q \in Proc }
                    /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = TRUE]
                    /\ UNCHANGED <<selfAddressedMessageFlag, messageToDeliver>>)


    /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase,submitted, initCoord, recovered, Qvar, CardinalityRmax >>

(***************************************************************************)
(* 69–80 HandlePostWaitingMsg                                                 *)
(***************************************************************************)
                    
HandlePostWaiting(p, id) ==
    /\  postWaitingFlag[p][id] = TRUE
    /\  LET 
           I == Ivar[p][id]
           Q == Qvar[p][id]
           b == bal[p][id] \* bal[id] = b as a precondition of RecoverOK so I can conflate the two
        IN  /\ b = bal[p][id]
            /\  \/ (\E x \in I :
                        x[1] # id /\
                        x[2] = CommittedPhase /\
                        cmd[p][x[1]] # Nop /\
                        id \notin dep[p][x[1]]
                    /\ msgs' = msgs \cup { AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc }
                    /\ selfAddressedMessageFlag' = TRUE
                    /\ messageToDeliver' = [ type |-> TypeAccept, p |-> p, id |-> id, b |-> bal[p][id], c |-> Nop, D |-> {} ])

                \/ (\A x \in I :
                        x[1] # id =>
                        (x[2] = CommittedPhase /\
                            (cmd[p][x[1]] = Nop \/ id \in dep[p][x[1]]))
                    /\ msgs' =  msgs \cup { AcceptMsg(p, q, bal[p][id], id, cmd[p][id], dep[p][id]) : q  \in Proc }
                    /\ selfAddressedMessageFlag' = TRUE
                    /\ messageToDeliver' = [ type |-> TypeAccept, p |-> p, id |-> id, b |-> bal[p][id], c |-> cmd[p][id], D |-> dep[p][id] ])

                \/ (\E x \in I :
                        x[1] # id /\
                        \E m2 \in msgs :
                            m2.type = TypeWaiting /\
                            m2.to = p /\
                            m2.body.id = x[1] /\
                            m2.body.k > N - F - E
                    /\ msgs' =  msgs \cup { AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc }
                    /\ selfAddressedMessageFlag' = TRUE
                    /\ messageToDeliver' = [ type |-> TypeAccept, p |-> p, id |-> id, b |-> bal[p][id], c |-> Nop, D |-> {} ])

                \/ (\E m2 \in msgs :
                        /\ m2.type = TypeRecoverOK 
                        /\ m2.to = p 
                        /\ m2.body.id = id 
                        /\ m2.from \notin Q 
                        /\ (m2.body.phaseq = CommittedPhase \/ m2.body.phaseq = AcceptedPhase \/ m2.from = initCoord[id])
                        /\  IF m2.body.phaseq = CommittedPhase THEN
                                /\ msgs' = msgs \cup {CommitMsg(p, q, bal[p][id], id, m2.body.cq, m2.body.depq) : q \in Proc }
                                /\ selfAddressedMessageFlag' = TRUE
                                /\ messageToDeliver' = [ type |-> TypeCommit, p |-> p, id |-> id, b |-> bal[p][id], c |-> m2.body.cq, D |-> m2.body.depq ]
                            ELSE IF m2.body.phaseq = AcceptedPhase THEN
                                /\ msgs' = msgs \cup {AcceptMsg(p, q, bal[p][id], id, m2.body.cq, m2.body.depq) : q \in Proc }
                                /\ selfAddressedMessageFlag' = TRUE
                                /\ messageToDeliver' = [ type |-> TypeAccept, p |-> p, id |-> id, b |-> bal[p][id], c |-> m2.body.cq, D |-> m2.body.depq ]
                            ELSE
                                /\ msgs' = msgs \cup {AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc }
                                /\ selfAddressedMessageFlag' = TRUE
                                /\ messageToDeliver' = [ type |-> TypeAccept, p |-> p, id |-> id, b |-> bal[p][id], c |-> Nop, D |-> {} ]
                                )
                

    /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase,
                        submitted, initCoord, recovered, Qvar, CardinalityRmax, Ivar, postWaitingFlag >>


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
  \A id, id2 \in Id : \A p, q \in Proc :
    /\ id # id2
    /\ cmd[p][id] # Nop
    /\ cmd[q][id2] # Nop 
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
        /\ (cmd[p][id] \in Cmd \/ cmd[p][id] = Nop \/ cmd[p][id] = Bottom)
        /\ (initCmd[p][id] \in Cmd \/ initCmd[p][id] = Nop \/ initCmd[p][id] = Bottom)
        /\ dep[p][id] \subseteq Id
        /\ initDep[p][id] \subseteq Id
        /\ phase[p][id] \in {InitialPhase, PreAcceptedPhase, AcceptedPhase, CommittedPhase}
        /\ recovered[p][id] >= 0 /\ recovered[p][id] <= NumberOfRecoveryAttempts
        /\ Ivar[p][id] \subseteq { <<id2, phase2>> : id2 \in Id, phase2 \in {InitialPhase, PreAcceptedPhase, AcceptedPhase, CommittedPhase} }
        /\ Qvar[p][id] \subseteq Proc
        /\ CardinalityRmax[p][id] >= 0 /\ CardinalityRmax[p][id] <= Cardinality(Proc)
    
    /\ selfAddressedMessageFlag \in BOOLEAN 

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
    

    \/ ~selfAddressedMessageFlag 
        /\ (\/ \E m \in msgs :
                \/ HandlePreAccept(m)
                \/ HandleAccept(m)
                \/ HandleCommit(m)
                \/ HandleRecover(m)
                \/ HandleValidate(m)

            \/ \E q \in Proc, id \in Id, c \in Cmd :
                Submit(q, id, c)

            \/ \E p \in Proc, id \in Id :
                \/ StartRecover(p, id)
                \/ HandlePreAcceptOK(p, id)
                \/ HandleValidateOK(p, id)
                \/ HandlePostWaiting(p, id)
                \/ HandleRecoverOK(p, id)
                \/ HandleAcceptOK(p, id)
            \/ UNCHANGED <<vars>>
            )

    \/ selfAddressedMessageFlag /\
        (   IF   messageToDeliver.type = TypeCommit THEN 
                    LET m == CHOOSE m \in msgs :
                                    /\ m.type = TypeCommit
                                    /\ m.from = messageToDeliver.p
                                    /\ m.body.id = messageToDeliver.id
                                    /\ m.body.c = messageToDeliver.c
                                    /\ m.body.D = messageToDeliver.D
                                    /\ m.body.b = messageToDeliver.b
                    IN HandleCommit(m)
            ELSE IF messageToDeliver.type = TypeAccept THEN 
                    LET m == CHOOSE m \in msgs :
                                    /\ m.type = TypeAccept
                                    /\ m.from = messageToDeliver.p
                                    /\ m.body.id = messageToDeliver.id
                                    /\ m.body.c = messageToDeliver.c
                                    /\ m.body.D = messageToDeliver.D
                                    /\ m.body.b = messageToDeliver.b
                    IN HandleAccept(m)
            ELSE UNCHANGED <<vars>>)
              

Spec ==
    Init /\ [][Next]_<< vars >>

=============================================================================
