---- MODULE CProgramPlusCal ----
EXTENDS Integers

(*--algorithm CProgramPlusCal
variables i = 0

define
    TypeOK == i \in 0..1001
end define;

begin
start:
    with iv \in 1..1000 do
        i := iv;
    end with;
middle:
    i := i + 1;
end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "9d5f4cf7" /\ chksum(tla) = "81cb77a2")
VARIABLES i, pc

(* define statement *)
TypeOK == i \in 0..1001


vars == << i, pc >>

Init == (* Global variables *)
        /\ i = 0
        /\ pc = "start"

start == /\ pc = "start"
         /\ \E iv \in 1..1000:
              i' = iv
         /\ pc' = "middle"

middle == /\ pc = "middle"
          /\ i' = i + 1
          /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == start \/ middle
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
