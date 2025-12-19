------------------------------ MODULE SMRspec ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Proc,        \* Set of processes
  Cmd         \* Set of unique commands


VARIABLES
  submitted,    \* Set of commands that have been submitted
  executed     \* Map from Proc to sequence of executed commands


vars == <<submitted, executed>>

Init ==
  /\ submitted = {}
  /\ executed = [p \in Proc |-> <<>>]


Submit(p, c) ==
  /\ p \in Proc
  /\ c \in Cmd
  /\ c \notin submitted
  /\ submitted' = submitted \cup {c}
  /\ UNCHANGED <<executed>>

IsConflicting(c1, c2) == 
  /\ c1 # c2  \* Commands are different
    /\ (c1 % 2) = (c2 % 2)  \* Commands have the same parity (both even or both odd)

  
IsExecuted(p, c) ==
  \E i \in 1..Len(executed[p]): executed[p][i] = c

CanExecute(p, c) ==
  /\ c \in submitted
  /\ ~IsExecuted(p, c)
  /\ \A d \in Cmd :
        IsConflicting(c, d) =>
        IF \E q \in Proc: IsExecuted(q, d)
            THEN IsExecuted(p, d)
        ELSE TRUE  
                 

Execute(p, c) ==
  /\ p \in Proc
  /\ c \in Cmd
  /\ CanExecute(p, c)
  /\ executed' = [executed EXCEPT ![p] = Append(@, c)]
  /\ UNCHANGED submitted

Next ==
  \E p \in Proc:
    \E c \in Cmd:
       /\ \/ (Submit(p, c) /\ Print(<<"Submit", p, c >> ,TRUE)) 
          \/ (Execute(p, c) /\ Print(<<"Execute", p, c >> ,TRUE))
       /\ Print(<<executed' >> ,TRUE)


Validity == \A p \in Proc: \A i \in 1..Len(executed[p]): executed[p][i] \in submitted
Integrity == \A p \in Proc: \A i \in 1..Len(executed[p]): \A j \in 1..Len(executed[p]): executed[p][i] = executed[p][j] => i = j
Consistency ==
  \A p1, p2 \in Proc:
    \A c1, c2 \in Cmd:
      /\ IsConflicting(c1, c2)
      /\ IsExecuted(p1, c1) /\ IsExecuted(p1, c2)
      /\ IsExecuted(p2, c1) /\ IsExecuted(p2, c2)
      =>
        LET
          i1 == CHOOSE i \in 1..Len(executed[p1]): executed[p1][i] = c1
          j1 == CHOOSE j \in 1..Len(executed[p1]): executed[p1][j] = c2
          i2 == CHOOSE i \in 1..Len(executed[p2]): executed[p2][i] = c1
          j2 == CHOOSE j \in 1..Len(executed[p2]): executed[p2][j] = c2
        IN
          (i1 < j1) <=> (i2 < j2)
\* pas ordre partiel, avec vivacité ok. Peut améliorer


Liveness ==
    \A c \in Cmd:
      (c \in submitted \/ \E p \in Proc: IsExecuted(p, c)) =>
        \A p \in Proc: <> IsExecuted(p, c)

Invariants == Validity /\ Integrity /\ Consistency


Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)




=============================================================================
