---- MODULE spec ----
EXTENDS TLC, FiniteSets, Integers, Sequences

CONSTANTS Accounts, InitialBalance, NumConcurrentRequests

ASSUME IsFiniteSet(Accounts)
ASSUME InitialBalance \in Nat
ASSUME NumConcurrentRequests \in Nat

VARIABLE pc, db_balances

vars == <<pc, db_balances>>

Init == 
    /\ pc = [n \in 1..NumConcurrentRequests |-> "CheckBalance"]
    /\ db_balances = [acc \in Accounts |-> InitialBalance]

CheckBalance(self) ==
    /\ PrintT(<<"CheckBalance ff>ch", self>>)
    /\ pc[self] = "CheckBalance"
    \* Read my balance from the db. If there's enough money, move to transfer the money.
    /\ db_balances["alice"] >= 1
    /\ pc' = [pc EXCEPT ![self] = "UpdateDb"]
    /\ UNCHANGED <<db_balances>>

UpdateDb(self) == 
    /\ pc[self] = "UpdateDb"
    /\ PrintT(<<"UpdateDb", self>>)
    /\ db_balances' = [db_balances EXCEPT 
                                        !["alice"] = @ - 1,
                                        !["bob"] = @ + 1]
    /\ pc' = [pc EXCEPT ![self] = "Done"]

Terminating(request_id) ==
    /\ pc[request_id] = "Done"
    /\ UNCHANGED vars

Wire(request_id) == 
    \/ CheckBalance(request_id)
    \/ UpdateDb(request_id)
    \/ Terminating(request_id)
        
Next == 
    \E request_id \in 1..NumConcurrentRequests:
        Wire(request_id)

Spec == Init /\ [][Next]_vars


RECURSIVE SumBalances(_, _)
SumBalances(s, acc) ==
    IF s = {} THEN 
        acc
    ELSE 
        LET x == CHOOSE x \in s: TRUE IN
            SumBalances(s \ {x}, db_balances[x] + acc)

TotalBalanceIsSumOfBalances ==
    \* The sum of the balances in the database.
    \* Should equal the sum of the initial balance for each account.
    /\ SumBalances(Accounts, 0) = InitialBalance * Cardinality(Accounts)

BalanceIsAlwaysZeroOrMore ==
    \A acc \in Accounts:
        db_balances[acc] >= 0
====