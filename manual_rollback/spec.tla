---- MODULE spec ----
EXTENDS TLC

VARIABLES pc, db_state, k8s_state

vars == <<pc, db_state, k8s_state>>

Init ==
    /\ pc = "write_to_db"
    /\ db_state = "ok"
    /\ k8s_state = "ok"

WriteToDb ==
    /\ pc = "write_to_db"
    /\ db_state' = "modified"
    /\ pc' = "write_to_k8s"
    /\ UNCHANGED <<k8s_state>>

FailAfterModifyingDBAndRollback ==
    /\ pc = "write_to_k8s"
    /\ db_state = "modified"
    /\ db_state' = "ok"
    /\ pc = "write_to_db"
    /\ UNCHANGED <<db_state, k8s_state>>

WriteToK8s ==
    /\ pc = "write_to_k8s"
    /\ \/ 
         /\ k8s_state' = "modified"
         /\ pc' = "done"
         /\ UNCHANGED <<db_state>>
       \/
         /\ k8s_state' = "failed"
         /\ pc' = "rollback_k8s"
         /\ UNCHANGED <<db_state>>
    
RollBackK8s ==
    /\ pc = "rollback_k8s"
    /\ \/
          /\ k8s_state' = "ok"
            
          /\ UNCHANGED <<db_state>>
       \/ 
          /\ UNCHANGED <<k8s_state, db_state>>
    /\ pc' = "done"' 

Terminating == 
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ WriteToDb
    \/ FailAfterModifyingDBAndRollback
    \/ WriteToK8s
    \/ RollBackK8s
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

StoresAreAlwaysConsistent == <>[](db_state = "ok" /\ k8s_state = "ok" /\ pc = "done")
====