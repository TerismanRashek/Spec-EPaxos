---------------- MODULE EPaxosExecution ----------------
EXTENDS EPaxosState

IsExecuted(p, c) ==
        \E i \in 1..Len(executed[p]): executed[p][i] = c

    IsExecutedSCC(p, C) ==
        \A c \in C : IsExecuted(p, c)

    IsConflicting(c, d) ==
        /\ c /= d
        /\ (c % d) = 0


    ConflictsWith(c) ==
        { d \in CmdIds : IsConflicting(c, d) } 


    \* Submit a command
    Submit(c) ==
        /\ c \in CmdIds
        /\ c \notin submitted
        /\ submitted' = submitted \cup {c}
        /\ UNCHANGED <<dep, executed>>

    \* Commit a command with dependencies
    Commit(c) ==
        /\ c \in submitted
        /\ dep' = [dep EXCEPT ![c] = ConflictsWith(c)]
        /\ UNCHANGED <<submitted, executed>>


    \* The set of committed commands (dep known)
    CommittedCmds == {c \in CmdIds : dep[c] # {UnknownDep}}

    IsCommittedSubset(g) ==
        /\ g \subseteq CommittedCmds
            
    \* Recursive operator to compute all nodes reachable from c in graph G , visited to avoid cycles going infinite loop
    RECURSIVE ReachableRec(_, _, _)
    ReachableRec(G, c, visited) ==
        IF c \in visited THEN {}
        ELSE
            LET deps == {d \in dep[c] : d \in G}
                newVisited == visited \cup {c}
            IN {c} \cup UNION {ReachableRec(G, d, newVisited) : d \in deps}

    Reachable(G, c) == ReachableRec(G, c, {})

    MutuallyReachable(G, c) == {c} \cup { d \in G : c \in Reachable(G, d) /\ d \in Reachable(G, c) }

    \* SCCs of G: collect all mutually reachable sets
    SCCs(G) == {MutuallyReachable(G, c) : c \in G}

    \* Permutations2: recursive definition renamed because of name conflict with TLC library
    RECURSIVE Permutations2(_)
    Permutations2(S) ==
        IF S = {} THEN
            { <<>> } 
        ELSE
            UNION { { Append(seq, x) : seq \in Permutations2(S \ {x}) } : x \in S }
                
    \* Convert a sequence to the set of its elements
    SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }


    RECURSIVE SetToSeq(_)

    SetToSeq(set) == IF set = {} THEN <<>> ELSE
    LET x == CHOOSE x \in set: TRUE
        IN <<x>> \o SetToSeq(set \ {x})



    \* G1 < G2 if some node in G2 depends on a node in G1
    TopoOrder(SCCSet) ==
        CHOOSE seq \in Permutations2(SCCSet) :
            \A i, j \in 1..Len(seq) :
                i < j => \A c \in seq[j], d \in seq[i] : d \notin dep[c]


    \* A command is ready if all its dependencies are executed at process p
    ReadyToExecute(p, c) ==
        /\ c \in CommittedCmds
        /\ ~IsExecuted(p, c)
    (*     /\ Print(<<"dep[c]", dep[c]>>, FALSE)
        /\ Print(<<"executed[p]", executed[p]>>, FALSE) *)
        /\ dep[c] \subseteq SeqToSet(executed[p])

    ExternalDeps(c, C) == dep[c] \ C

    ReadySCC(p, C) ==
        /\ ~IsExecutedSCC(p, C)
        /\ \A c \in C : ExternalDeps(c, C) \subseteq SeqToSet(executed[p])

            

    Execute(p) ==
        LET G == CmdIds
            SCCSet == SCCs(G)
            orderedSCCs == TopoOrder(SCCSet)
            committedSCCs == { C \in SeqToSet(orderedSCCs) : IsCommittedSubset(C) }
        IN IF ~(\E C \in committedSCCs : ReadySCC(p, C)) THEN
            UNCHANGED <<executed, submitted, dep>>
        ELSE
            \* Pick any ready SCC deterministically
                    LET nextSCC == CHOOSE C \in committedSCCs : ReadySCC(p, C)
                    IN
                        /\ executed' = [executed EXCEPT ![p] = executed[p] \o SetToSeq(nextSCC)]
                        /\ UNCHANGED <<submitted, dep>>

=============================================================================