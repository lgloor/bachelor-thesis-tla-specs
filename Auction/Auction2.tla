------------------------------ MODULE Auction2 ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NULL, Participants, MaxAmount, UNKNOWN, NONE

VARIABLES initialMoney, lastBid, bid, round, passed, winner

A2vars == <<initialMoney, lastBid, bid, round, passed, winner>>

\* p is ready to act once all others have passed or caught up.
readyForAction(p) == 
    \A p2 \in Participants:
      \/ passed[p2]
      \/ round[p] = round[p2]

---------------------------------------------------------------

A2Init ==
    /\ lastBid = [ p \in Participants |-> 0 ]
    /\ bid = [ p \in Participants |-> NULL ]
    /\ round = [ p \in Participants |-> 1 ]
    /\ passed = [ p \in Participants |-> FALSE ]
    /\ initialMoney \in [Participants -> 0..MaxAmount]
    /\ winner = [ p \in Participants |-> UNKNOWN ]
    
A2Bid == \E p \in Participants:
    /\ winner[p] = UNKNOWN
    /\ \neg passed[p]
    /\ bid[p] = NULL
    /\ \E p2 \in Participants \ {p} :round[p2] = round[p]
    /\ readyForAction(p)
    /\ \E newBid \in (lastBid[p] + 1)..initialMoney[p]:
        /\ \A p2 \in Participants: newBid > lastBid[p2]
        /\ bid' = [bid EXCEPT ![p] = newBid]
    /\ UNCHANGED <<lastBid, round, passed, initialMoney, winner>>

A2Stand == \E p \in Participants:
    /\ winner[p] = UNKNOWN
    /\ \neg passed[p]
    /\ bid[p] = NULL
    /\ \E p2 \in Participants \ {p} : round[p2] = round[p]
    /\ \A p2 \in Participants \ {p} : lastBid[p2] < lastBid[p]
    /\ readyForAction(p)
    /\ bid' = [bid EXCEPT ![p] = lastBid[p]]
    /\ UNCHANGED <<lastBid, round, passed, initialMoney, winner>>
    
A2Pass == \E p \in Participants:
    /\ winner[p] = UNKNOWN
    /\ \neg passed[p]
    /\ readyForAction(p)
    /\ bid[p] = NULL
    /\ \E p2 \in Participants \ {p} :round[p2] = round[p]
    /\ passed' = [passed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<bid, lastBid, round, initialMoney, winner>>
    
A2NextRound == \E p \in Participants:
    /\ winner[p] = UNKNOWN
    /\ Cardinality({p2 \in Participants: \neg passed[p2]}) # 0
    /\ bid[p] # NULL
    /\ \A p2 \in Participants:
         \/ passed[p2]
         \/ IF round[p] = round[p2]
            THEN bid[p2] # NULL
            ELSE round[p2] > round[p]
    /\ lastBid' = [ lastBid EXCEPT ![p] = bid[p] ]
    /\ bid' = [ bid EXCEPT ![p] = NULL ]
    /\ round' = [ round EXCEPT ![p] = @ + 1 ]
    /\ UNCHANGED <<passed, initialMoney, winner>>
    
A2ChooseWinner == \E p \in Participants:
    /\ winner[p] = UNKNOWN
    /\ \/ /\ \A p2 \in Participants: passed[p2]
          /\ winner' = [ winner EXCEPT ![p] = NONE ] 
       \/ \E p2 \in Participants:
          /\ \neg passed[p2]
          /\ \A p3 \in (Participants \ {p2}): passed[p3]
          /\ \A p3 \in (Participants \ {p2}): lastBid[p2] > lastBid[p3]
          /\ \A p3 \in (Participants \ {p2}): round[p2] > round[p3]
          /\ winner' = [winner EXCEPT ![p] = p2]
    /\ UNCHANGED <<bid, lastBid, passed, round, initialMoney>>
    
A2Next ==
    \/ A2Bid
    \/ A2Stand
    \/ A2Pass
    \/ A2NextRound
    \/ A2ChooseWinner
    
A2TypeOK ==
    /\ lastBid \in [ Participants -> 0..MaxAmount ]
    /\ bid \in [ Participants -> 1..MaxAmount  \union { NULL } ]
    /\ round \in [ Participants -> Nat \ { 0 } ]
    /\ passed \in [ Participants -> BOOLEAN ]
    /\ winner \in [ Participants -> {UNKNOWN, NONE} \union Participants ]
    /\ initialMoney \in [ Participants -> 0..MaxAmount ]
    
InvIncreasingBids == \A p \in Participants :
    \/ bid[p] = NULL
    \/ /\ \A p2 \in Participants \ {p} : 
            round[p] = round[p2] => bid[p] > lastBid[p2]
       /\ bid[p] >= lastBid[p]

A2FairSpec ==
    /\ A2Init
    /\ [][A2Next]_A2vars
    /\ WF_A2vars(A2Pass)
    /\ WF_A2vars(A2NextRound)
    /\ WF_A2vars(A2ChooseWinner)
    
INSTANCE Auction1

THEOREM A2FairSpec => A1FairSpec

=============================================================================
\* Modification History
\* Last modified Sat Jun 07 07:36:20 CEST 2025 by luca
\* Created Wed Apr 16 13:15:21 CEST 2025 by luca
