---- MODULE CProgramDraft ----
EXTENDS Integers

VARIABLE i, pc

Init == i = 0 /\ pc = "start"

StartToMiddle == /\ pc = "start" 
                 /\ i' \in 0..1000 
                 /\ pc' = "middle"

MiddleToEnd == /\ pc = "middle" 
               /\ i' = i + 1 
               /\ pc' = "end"

Next == \/ StartToMiddle
        \/ MiddleToEnd

TypeOK == /\ pc \in {"start", "middle", "end"} 
          /\ i \in 0..1001

(*

i: 0      -> i: 10     -> i: 11   -> i: 11   
pc: start    pc: middle   pc: end    pc: end

i: 0 -> i: 1 -> i: 2 -> ... -> i: 1000 -> i: 1001 -> ...

*)
====