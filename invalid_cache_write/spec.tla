---- MODULE spec ----
EXTENDS TLC, FiniteSets, Naturals, Sequences

CONSTANTS NULL, MaxWrites, Processes

ASSUME MaxWrites \in Nat
ASSUME IsFiniteSet(Processes)

VARIABLES memory, cache, db_value, values_written_to_cache

vars == <<memory, cache, db_value, values_written_to_cache>>

Init ==
    /\ memory = [p \in Processes |-> NULL]
    /\ cache = NULL
    /\ db_value = 0
    /\ values_written_to_cache = <<>>

ReadFromDb(self) ==
    /\ memory' = [memory EXCEPT ![self] = db_value]
    /\ UNCHANGED <<cache, db_value, values_written_to_cache>>

WriteToCache(self) ==
    /\ memory[self] /= NULL
    /\ cache' = memory[self]
    /\ memory' = [memory EXCEPT ![self] = NULL]
    /\ values_written_to_cache' = Append(values_written_to_cache, memory[self])
    /\ UNCHANGED <<db_value>>

WriteToDb ==
    /\ Len(values_written_to_cache) < MaxWrites
    /\ db_value' = db_value + 1
    /\ UNCHANGED <<memory, cache, values_written_to_cache>>

Next ==
    \E proc \in Processes:
        \/ ReadFromDb(proc)
        \/ WriteToCache(proc)
        \/ WriteToDb

Spec == Init /\ [][Next]_vars

Cache_NewestValueIsNeverOverwritten ==
    PrintT(values_written_to_cache) /\
    \A i \in 1..Len(values_written_to_cache) - 1:
        values_written_to_cache[i] <= values_written_to_cache[i + 1]
====