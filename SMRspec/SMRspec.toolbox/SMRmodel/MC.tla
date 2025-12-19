---- MODULE MC ----
EXTENDS SMRspec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1
----

\* MV CONSTANT definitions Proc
const_176112291881538000 == 
{p1, p2}
----

\* MV CONSTANT definitions Cmd
const_176112291881539000 == 
{c1}
----

\* CONSTANT definitions @modelParameterConstants:2Conflict
const_176112291881540000 == 
{}
----

=============================================================================
\* Modification History
\* Created Wed Oct 22 10:48:38 CEST 2025 by terisman
