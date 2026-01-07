----------------------------- MODULE EPaxosRecovery -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Proc, CmdIds, CmdVals, InitCoord, E, F

N == Cardinality(Proc)
QuorumSize == N - F

TypeRecover     == "Recover"
TypeRecoverOK   == "RecoverOK"
TypeValidate    == "Validate"
TypeValidateOK  == "ValidateOK"
TypeAccept      == "Accept"
TypeCommit      == "Commit"
TypeWaiting     == "Waiting"

Message(type, from, to, body) ==
    [ type |-> type, from |-> from, to |-> to, body |-> body ]

RecoverMsg(p,q,b,id) ==
    Message(TypeRecover,p,q,[b|->b,id|->id])

RecoverOKMsg(q,p,b,id,ab,c,D,iD,ph) ==
    Message(TypeRecoverOK,q,p,
        [ b|->b, id|->id, abalq|->ab, cq|->c,
          depq|->D, initDepq|->iD, phaseq|->ph ])

ValidateMsg(p,q,b,id,c,D) ==
    Message(TypeValidate,p,q,[b|->b,id|->id,c|->c,D|->D])

ValidateOKMsg(q,p,b,id,I) ==
    Message(TypeValidateOK,q,p,[b|->b,id|->id,Iq|->I])

AcceptMsg(p,q,b,id,c,D) ==
    Message(TypeAccept,p,q,[b|->b,id|->id,cmdc|->c,depc|->D])

CommitMsg(p,q,b,id,c,D) ==
    Message(TypeCommit,p,q,[b|->b,id|->id,cmdc|->c,depc|->D])

WaitingMsg(p,q,id,k,I) ==
    Message(TypeWaiting,p,q,[id|->id,k|->k,I|->I])

VARIABLES
    bal, abal,
    cmd, initCmd,
    dep, initDep,
    phase,
    msgs

Init ==
    /\ bal = [p \in Proc |-> [id \in CmdIds |-> 0]]
    /\ abal = [p \in Proc |-> [id \in CmdIds |-> 0]]
    /\ cmd = [p \in Proc |-> [id \in CmdIds |-> "Nop"]]
    /\ initCmd = [p \in Proc |-> [id \in CmdIds |-> "Nop"]]
    /\ dep = [p \in Proc |-> [id \in CmdIds |-> {}]]
    /\ initDep = [p \in Proc |-> [id \in CmdIds |-> {}]]
    /\ phase = [p \in Proc |-> [id \in CmdIds |-> "none"]]
    /\ msgs = {}

(***************************************************************************)
(* 44–45 StartRecover                                                      *)
(***************************************************************************)
StartRecover(p,id) ==
    LET b == bal[p][id] + 1 IN
    /\ msgs' = msgs \cup { RecoverMsg(p,q,b,id) : q \in Proc }
    /\ UNCHANGED << abal, cmd, initCmd, dep, initDep, phase, bal >>

(***************************************************************************)
(* 46–49 HandleRecover                                                     *)
(***************************************************************************)
HandleRecover(m) ==
    /\ m \in msgs /\ m.type = TypeRecover
    LET p == m.to
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
    /\ UNCHANGED << abal, cmd, initCmd, dep, initDep, phase >>

(***************************************************************************)
(* 50–63 HandleRecoverOK                                                   *)
(***************************************************************************)
HandleRecoverOK(p,id,b) ==
    LET Q ==
        { q \in Proc :
            \E m \in msgs :
                m.type = TypeRecoverOK /\ m.to=p /\ m.from=q /\
                m.body.id=id /\ m.body.b=b }
        OKs ==
        { m \in msgs :
            m.type = TypeRecoverOK /\ m.to=p /\ m.from \in Q /\
            m.body.id=id /\ m.body.b=b }
        Abals == { m.body.abalq : m \in OKs }
        bmax == Max(Abals)
        U == { m \in OKs : m.body.abalq = bmax }
    IN
    /\ bal[p][id] = b
    /\ Cardinality(Q) >= QuorumSize

    \/ (\E q \in Proc : phase[q][id] = "committed"
           /\ msgs' =
             (msgs \ OKs) \cup
             { CommitMsg(p,q,b,id,mr.body.cq,mr.body.depq)
                 : q \in Proc })

    \/ (\E q \in Proc : phase[q][id] = "accepted"
           /\ msgs' =
             (msgs \ OKs) \cup
             { AcceptMsg(p,q,b,id,mr.body.cq,mr.body.depq)
                 : q \in Proc })

    \/ (InitCoord[id] \in Q
        /\ msgs' =
             (msgs \ OKs) \cup
             { AcceptMsg(p,q,b,id,"Nop",{}) : q \in Proc })

    \/ (\E R \subseteq Q :
       /\ Cardinality(R) >= Cardinality(Q) - e
       /\ \A q \in R : phase[q][id] = "preaccepted" /\ dep[q][id] = initDep[q][id]
       /\ LET Rmax == CHOOSE S \in SUBSET(Q) :
                        Cardinality(S) >= Cardinality(Q) - e
                        /\ \A q \in S : phase[q][id] = "preaccepted" /\ dep[q][id] = initDep[q][id]
          IN
             /\ \E q \in Rmax :
                  LET c == cq[q]
                      D == dep[q][id]
                  IN
                      msgs' =
                        (msgs \ OKs) \cup
                        { Validate(p, q2, b, id, c, D) : q2 \in Q }
        )

    /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase >>

(***************************************************************************)
(* 64–70 HandleValidateOK                                                 *)
(***************************************************************************)
HandleValidateOK(p, id, b, c, D) ==
  LET Q ==
        { q \in Proc :
            \E m \in msgs :
                m.type = TypeValidateOK /\ m.to = p /\ m.from = q /\
                m.body.id = id /\ m.body.b = b }
      OKs ==
        { m \in msgs :
            m.type = TypeValidateOK /\ m.to = p /\ m.from \in Q /\
            m.body.id = id /\ m.body.b = b }
      I == UNION { m.body.Iq : m \in OKs }
  IN
  /\ Cardinality(Q) >= QuorumSize
  /\ msgs' =
       (msgs \ OKs) \cup
       IF I = {} THEN
           { AcceptMsg(p, q, b, id, c, D) : q \in Proc }
       ELSE IF (\E (id', committed) \in I : committed = "committed") \/
                (Cardinality(Rmax) = Cardinality(Q) - e /\
                 \E (id', _) \in I : initCoord[id'] \notin Q) THEN
           { AcceptMsg(p, q, b, id, "Nop", {}) : q \in Proc }
       ELSE
           { WaitingMsg(p, q, id, Cardinality(Rmax), I) : q \in Proc }

  /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase >>


(***************************************************************************)
(* 71–83 HandleWaitingMsg                                                  *)
(***************************************************************************)
HandleWaitingMsg(m) ==
    /\ m \in msgs /\ m.type = TypeWaiting
    LET p == m.to
        id == m.body.id
        k == m.body.k
        I == m.body.I
    IN
    \/ (\E x \in I :
            phase[p][x[1]] = "committed" /\
            cmd[p][x[1]] # "Nop" /\ id \notin dep[p][x[1]]
        /\ msgs' =
             (msgs \ {m}) \cup
             { AcceptMsg(p, q, bal[p][id], id, "Nop", {}) : q \in Proc })

    \/ (\A x \in I :
            phase[p][x[1]] = "committed" /\
            (cmd[p][x[1]] = "Nop" \/ id \in dep[p][x[1]])
        /\ msgs' =
             (msgs \ {m}) \cup
             { AcceptMsg(p, q, bal[p][id], id, cmd[p][id], dep[p][id])
                 : q \in Proc })

    \/ (\E x \in I :
            \E m2 \in msgs :
                m2.type = TypeWaiting /\
                m2.to = p /\
                m2.body.id = x[1] /\
                m2.body.k > n - f - e
        /\ msgs' =
             (msgs \ {m}) \cup
             { AcceptMsg(p, q, bal[p][id], id, "Nop", {}) : q \in Proc })

    \/ (\E m2 \in msgs :
            m2.type = TypeRecoverOK /\
            m2.to = p /\
            m2.body.id = id /\
            m2.from \notin Q /\
            (m2.body.phase = "committed" \/
             m2.body.phase = "accepted" \/
             m2.from = initCoord[id])
        /\ msgs' =
            (msgs \ {m}) \cup
            IF m2.body.phase = "committed" THEN
                { CommitMsg(p, q, bal[p][id], id,
                            m2.body.cmd, m2.body.dep) : q \in Proc }
            ELSE IF m2.body.phase = "accepted" THEN
                { AcceptMsg(p, q, bal[p][id], id,
                            m2.body.cmd, m2.body.dep) : q \in Proc }
            ELSE
                { AcceptMsg(p, q, bal[p][id], id, "Nop", {}) : q \in Proc })

    /\ UNCHANGED << bal, abal, cmd, initCmd, dep, initDep, phase >>

(***************************************************************************)
(* 84–90 HandleValidate                                                    *)
(***************************************************************************)
HandleValidate(m) ==
    /\ m \in msgs /\ m.type=TypeValidate
    LET p == m.to
        id == m.body.id
        c == m.body.c
        D == m.body.D
        b == m.body.b
    IN
    /\ bal[p][id] = b
    /\ cmd' = [cmd EXCEPT ![p][id]=c]
    /\ initCmd' = [initCmd EXCEPT ![p][id]=c]
    /\ initDep' = [initDep EXCEPT ![p][id]=D]

    LET I ==
        { <<id2,phase[p][id2]>> :
            id2 \in CmdIds \ D /\
            ((phase[p][id2]="committed" =>
                cmd[p][id2]#"Nop" /\ id \notin dep[p][id2])
             /\ (phase[p][id2]#"committed" =>
                initCmd[p][id2]#"Nop" /\ id \notin initDep[p][id2])) }
    IN
    /\ msgs' =
         (msgs \ {m}) \cup
         { ValidateOKMsg(p,m.from,m.body.b,id,I) }

    /\ UNCHANGED << bal, abal, dep, phase >>

Next ==
    \/ \E p,id : StartRecover(p,id)
    \/ \E m : HandleRecover(m)
    \/ \E p,id,b : HandleRecoverOK(p,id,b)
    \/ \E p,id,b,c,D : HandleValidateOK(p,id,b,c,D)
    \/ \E m : HandleWaitingMsg(m)
    \/ \E m : HandleValidate(m)

Spec ==
    Init /\ [][Next]_<< bal,abal,cmd,initCmd,dep,initDep,phase,msgs >>

=============================================================================
