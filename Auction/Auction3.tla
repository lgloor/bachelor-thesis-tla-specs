------------------------------ MODULE Auction3 ------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS NULL, Participants, MaxAmount, UNKNOWN, NONE, PASS, CHANGE

VARIABLES msgs, frontiers, initialMoney, lastBid, bid, round, passed, winner

A3vars == <<msgs, frontiers, initialMoney, lastBid, bid, round, passed, winner>>

----
max(n1, n2) == IF n1 > n2 THEN n1 ELSE n2

knowsHasPassed(p, p2) ==
    /\ LET lastMsgIdx == frontiers[p][p2]
       IN IF lastMsgIdx = 0 THEN FALSE
          ELSE msgs[p2][lastMsgIdx] = PASS

knownLastBid(p, p2) ==
    LET frontier == frontiers[p]
    IN IF frontier[p2] = 0 THEN 0
       ELSE LET lastKnownMsg == msgs[p2][frontier[p2]]
            IN IF lastKnownMsg = PASS
               THEN IF frontier[p2] = 1 THEN 0
                    ELSE msgs[p2][frontier[p2] - 2]
               ELSE IF lastKnownMsg \in Nat
                    THEN lastKnownMsg
                    ELSE msgs[p2][frontier[p2] - 1]
               
count(el, seq) == 
    LET RECURSIVE helper(_)
        helper(s) ==
            IF s = <<>> THEN 0
            ELSE IF Head(s) = el
                 THEN 1 + helper(Tail(s))
                 ELSE helper(Tail(s))
    IN helper(seq)
               
knownRound(p, p2) == 
    LET lastMsgIdx == frontiers[p][p2]
    IN IF lastMsgIdx = 0 THEN 1
       ELSE count(CHANGE, SubSeq(msgs[p2], 1, lastMsgIdx)) + 1
       
noActionInCurrentRound(p) ==
    LET lastMsgIdx == frontiers[p][p]
    IN IF lastMsgIdx = 0 THEN TRUE
       ELSE msgs[p][lastMsgIdx] = CHANGE
               
A3readyForAction(p) ==
    \A p2 \in Participants:
        \/ knowsHasPassed(p, p2)
        \/ round[p] = knownRound(p, p2)
        
addMsg(p, msg) ==
    /\ frontiers' = [frontiers EXCEPT ![p][p] = @ + 1]
    /\ msgs' = [msgs EXCEPT ![p] = @ \o <<msg>>]

----

A3Init ==
    /\ msgs = [p \in Participants |-> <<>>]
    /\ frontiers = [p \in Participants |-> [pa \in Participants |-> 0]]
    /\ lastBid = [ p \in Participants |-> 0 ]
    /\ bid = [ p \in Participants |-> NULL ]
    /\ round = [ p \in Participants |-> 1 ]
    /\ passed = [ p \in Participants |-> FALSE ]
    /\ initialMoney \in [Participants -> 0..MaxAmount]
    /\ winner = [ p \in Participants |-> UNKNOWN ]
    
A3Bid == \E p \in Participants:
    /\ winner[p] = UNKNOWN
    /\ noActionInCurrentRound(p)
    /\ A3readyForAction(p)
    /\ \E p2 \in Participants \ {p}: knownRound(p, p2) = round[p]
    /\ \E newBid \in (lastBid[p] + 1)..initialMoney[p]:
        /\ \A p2 \in Participants: newBid > knownLastBid(p, p2)
        /\ bid' = [bid EXCEPT ![p] = newBid]
        /\ addMsg(p, newBid)
    /\ UNCHANGED <<lastBid, round, passed, initialMoney, winner>>
    
A3Stand == \E p \in Participants:
    /\ winner[p] = UNKNOWN
    /\ noActionInCurrentRound(p)
    /\ \E p2 \in Participants \ {p} : knownRound(p, p2) = round[p]
    /\ \A p2 \in Participants \ {p} : knownLastBid(p, p2) < lastBid[p]
    /\ A3readyForAction(p)
    /\ bid' = [bid EXCEPT ![p] = lastBid[p]]
    /\ addMsg(p, lastBid[p])
    /\ UNCHANGED <<lastBid, round, passed, initialMoney, winner>>

A3Pass == \E p \in Participants:
    /\ winner[p] = UNKNOWN
    /\ noActionInCurrentRound(p)
    /\ \E p2 \in Participants \ {p}: knownRound(p, p2) = round[p]
    /\ A3readyForAction(p)
    /\ passed' = [passed EXCEPT ![p] = TRUE]
    /\ addMsg(p, PASS)
    /\ UNCHANGED <<bid, lastBid, round, initialMoney, winner>>
    
A3NextRound == \E p \in Participants:
    /\ winner[p] = UNKNOWN
    /\ Cardinality({p2 \in Participants: \neg knowsHasPassed(p, p2)}) # 0
    /\ bid[p] # NULL
    /\ \A p2 \in Participants:
        \/ knowsHasPassed(p, p2)
        \/ IF round[p] = knownRound(p, p2)
           THEN IF frontiers[p][p2] = 0 THEN FALSE
                ELSE msgs[p2][frontiers[p][p2]] \in Nat
           ELSE knownRound(p, p2) > round[p]
    /\ lastBid' = [lastBid EXCEPT ![p] = bid[p]]
    /\ bid' = [bid EXCEPT ![p] = NULL]
    /\ round' = [ round EXCEPT ![p] = @ + 1 ]
    /\ addMsg(p, CHANGE)
    /\ UNCHANGED <<passed, initialMoney, winner>>

A3Merge == \E sender, receiver \in Participants:
    /\ LET sFrontier == frontiers[sender]
           rFrontier == frontiers[receiver]
           newRFrontier == [p \in  Participants |-> max(sFrontier[p], rFrontier[p])]
       IN frontiers' = [frontiers EXCEPT ![receiver] = newRFrontier]
    /\ UNCHANGED <<initialMoney, msgs, bid, lastBid, passed, round, winner>>
    
A3ChooseWinner == \E p \in Participants:
    /\ winner[p] = UNKNOWN
    /\ \/ /\ \A p2 \in Participants: knowsHasPassed(p, p2)
          /\ winner' = [winner EXCEPT ![p] = NONE]
       \/ \E p2 \in Participants:
          /\ \neg knowsHasPassed(p, p2)
          /\ \A p3 \in (Participants \ {p2}): 
               /\ knowsHasPassed(p, p3)
               /\ knownLastBid(p, p2) > knownLastBid(p, p3)
               /\ knownRound(p, p2) > knownRound(p, p3)
          /\ winner' = [winner EXCEPT ![p] = p2]
    /\ UNCHANGED <<msgs, frontiers, bid, lastBid, passed, round, initialMoney>>

A3Next ==
    \/ A3Bid
    \/ A3Stand
    \/ A3Pass
    \/ A3NextRound
    \/ A3Merge
    \/ A3ChooseWinner
    
A3FairSpec ==
    /\ A3Init
    /\ [][A3Next]_A3vars
    /\ WF_A3vars(A3Pass)
    /\ WF_A3vars(A3NextRound)
    /\ WF_A3vars(A3Merge)
    /\ WF_A3vars(A3ChooseWinner)
        
INSTANCE Auction2

THEOREM A3FairSpec => A2FairSpec

=============================================================================
