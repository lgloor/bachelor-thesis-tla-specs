------------------------------ MODULE Auction1 ------------------------------
EXTENDS Naturals

CONSTANTS UNKNOWN, NONE, Participants, MaxAmount

VARIABLES initialMoney, lastBid, winner

A1vars == <<initialMoney, lastBid, winner>>

A1Bid ==
  /\ \A p \in Participants : winner[p] = UNKNOWN 
  /\ \E p \in Participants :
       \E newBid \in (lastBid[p]+1)..initialMoney[p] :
          lastBid' = [ lastBid EXCEPT ![p] = newBid ]
  /\ UNCHANGED <<winner, initialMoney>>
  
A1FirstChooseWinner == 
  /\ \A p \in Participants : winner[p] = UNKNOWN
  /\ \/ \E p,p2 \in Participants : 
          /\ \A p3 \in Participants \ {p} : lastBid[p] > lastBid[p3]
          /\ winner' = [ winner EXCEPT ![p2] = p ]
     \/ \E p \in Participants : winner' = [ winner EXCEPT ![p] = NONE ] 
  /\ UNCHANGED <<lastBid, initialMoney>>

A1OthersChooseWinner ==
  /\ \E p,p2 \in Participants : 
    /\ winner[p]  # UNKNOWN
    /\ winner[p2] = UNKNOWN
    /\ winner' = [ winner EXCEPT ![p2] = winner[p] ]
  /\ UNCHANGED <<lastBid, initialMoney>> 

A1Init == 
  /\ initialMoney \in [ Participants -> 0..MaxAmount ]
  /\ lastBid = [ p \in Participants |-> 0 ]
  /\ winner = [ p \in Participants |-> UNKNOWN ]
                   
A1Next == 
  \/ A1Bid
  \/ A1FirstChooseWinner
  \/ A1OthersChooseWinner

A1TypeOK == 
  /\ initialMoney \in [ Participants -> 0..MaxAmount ]
  /\ lastBid \in [ Participants -> Nat ]
  /\ winner \in [ Participants ->  
                  Participants \union { UNKNOWN, NONE } ]
                  
winnerStaysSame == \A p \in Participants: winner[p] # UNKNOWN => winner'[p] = winner[p]

terminated == \A p \in Participants : winner[p] # UNKNOWN

agreed == \A p,p2 \in Participants : 
            \/ winner[p] = UNKNOWN
            \/ winner[p2] = UNKNOWN
            \/ winner[p] = winner[p2]

solvable == \A p \in Participants: 
    lastBid[p] \in 0..(initialMoney[p])

winWithHigherBid == \A p, p2 \in Participants:
    winner[p2] = p => lastBid[p] > lastBid[p2] \/ p = p2
            
valid == solvable /\ winWithHigherBid
            
termination == <>[]terminated (*liveness*)
agreement == []agreed (*safety*)
validity == []valid (*safety*)
integrity == [][winnerStaysSame]_A1vars

A1FairSpec ==
  /\ A1Init
  /\ [][A1Next]_A1vars
  /\ WF_A1vars(A1OthersChooseWinner)
  /\ WF_A1vars(A1FirstChooseWinner)

=============================================================================
