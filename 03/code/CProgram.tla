---- MODULE CProgram ----
EXTENDS Integers
VARIABLE i, pc

Init == /\ i = 0 
        /\ pc = "start"

Next == \/ /\ pc = "start"
           /\ i' \in 0..1000
           /\ pc' = "middle"
        \/ /\ pc = "middle"
           /\ i' = i + 1
           /\ pc' = "end"

TypeOK == /\ pc \in {"start", "middle", "end"}
          /\ i \in 0..1001
====