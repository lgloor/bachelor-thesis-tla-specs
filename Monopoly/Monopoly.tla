------------------------------ MODULE Monopoly ------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NULL, \* Model value because TLA+ does not have built in support for null
          NumPlayers, \* Number of players participating
          StartingMoney, \* Amount of money that each player starts with
          TotalMoney, \* Total money available
          DiceMax, \* Highest number one die can show
          JailFine, \* Fine for getting out of jail
          BaseRailRent, \* Rent when owning 1 railroad
          PassGoReward \* Reward for passing Go

VARIABLES positions, \* Board position of each player
          money,  \* Cash amount of each player
          inJail, \* Jail status of each player
          jailTime, \* Amount of rounds that each player is already in jail for
          isBankrupt, \* Bankruptcy status of each player
          board, \* Current status of the board (e.g. owner of properties, current level of properties etc.)
          turnPlayer, \* Player taking turn at the moment
          phase, \* Current phase of the game (determines the possible actions)
          bankMoney, \* Amount of money is left in the bank
          goojfChOwner, \* Owner of the "Get out of Jail free" card of the Chance deck
          goojfCcOwner, \* Owner of the "Get out of Jail free" card of the Community Chest deck
          doublesCount, \* Number of consecutive doubles rolled by the current player
          free4AllOrder, \* Order of players in free-4-all phase
          debt, \* Debt of a player in bankruptcy-prevention phase
          chanceCards, \* Will never change, more transparent than constant
          communityChestCards, \* Will never change
          jailIndex \* Index of jail square on board, will never change
          
vars == <<positions, money, inJail, jailTime, isBankrupt, board, 
  turnPlayer, phase, bankMoney, goojfChOwner, goojfCcOwner, 
  doublesCount, free4AllOrder, debt, chanceCards, 
  communityChestCards, jailIndex>>
          
------------------------------------------------------------------------------------------------------
abs(n) == IF n < 0 THEN -n ELSE n

RECURSIVE SeqSum(_)
SeqSum(sq) == IF sq = <<>> THEN 0
              ELSE Head(sq) + SeqSum(Tail(sq))

incrCirc(initial, amount, maxIdx) == ((initial + amount - 1) % maxIdx) + 1
             
currentSquare == board[positions[turnPlayer]]

isProperty(field) == field.type \in {"street", "rail", "util"}
    
PayBank(player, amount) == 
    /\ amount \in 0..money[player]
    /\ money' = [money EXCEPT ![player] = @ - amount]
    /\ bankMoney' = bankMoney + amount
    
CollectFromBank(player, amount) == 
    /\ amount > 0
    /\ IF bankMoney >= amount
       THEN /\ money' = [money EXCEPT ![player] = @ + amount]
            /\ bankMoney' = bankMoney - amount
       ELSE /\ money' = [money EXCEPT ![player] = @ + bankMoney]
            /\ bankMoney' = 0
    
ownedPropertyIdxs(player) ==
    {i \in 1..Len(board): 
        IF ~isProperty(board[i])
        THEN FALSE
        ELSE board[i].owner = player}
            
noStreetFromSameSetHasBuildings(strIdx) ==
    LET p_set == board[strIdx].set
    IN Cardinality(
        {i \in 1..Len(board):
            IF ~board[i].type = "street"
            THEN FALSE
            ELSE /\ board[i].level > 1
                 /\ board[i].set = p_set
    }) = 0
    
ownsAllOfSet(owner, set) ==
    \A idx \in DOMAIN board:
        IF board[idx].type /= "street"
        THEN TRUE
        ELSE board[idx].set = set => board[idx].owner = owner  
        
permutationSequences(S) ==
    {p \in UNION {[1..Cardinality(S) -> S]}:
        \A i1, i2 \in DOMAIN p:
          i1 /= i2 => p[i1] /= p[i2]}
        
initializeFree4All ==
    /\ phase' = "free-4-all"
    /\ \E order \in permutationSequences({p \in 1..NumPlayers: ~isBankrupt[p]}):
          free4AllOrder' = order

terminated ==
    Cardinality({i \in 1..NumPlayers: ~isBankrupt[i]}) = 1
    
------------------------------------------------------------------------------------------------------

EndPreRoll == 
    /\ ~terminated
    /\ phase = "pre-roll"
    /\ phase' = "roll"
    /\ UNCHANGED <<positions, money, inJail, isBankrupt, board, turnPlayer, 
       bankMoney, goojfCcOwner, goojfChOwner, doublesCount, jailTime,
       chanceCards, communityChestCards, debt, free4AllOrder, jailIndex>>
       
PlayGoojfCh ==
    /\ ~terminated
    /\ phase = "pre-roll"
    /\ goojfChOwner = turnPlayer
    /\ inJail[turnPlayer]
    /\ inJail' = [inJail EXCEPT ![turnPlayer] = FALSE]
    /\ jailTime' = [jailTime EXCEPT ![turnPlayer] = 0]
    /\ goojfChOwner' = NULL
    /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, debt, 
                   doublesCount, free4AllOrder, goojfCcOwner, isBankrupt, 
                   jailIndex, money, phase, positions, turnPlayer>>
    
PlayGoojfCc ==
    /\ ~terminated
    /\ phase = "pre-roll"
    /\ goojfCcOwner = turnPlayer
    /\ inJail[turnPlayer]
    /\ inJail' = [inJail EXCEPT ![turnPlayer] = FALSE]
    /\ jailTime' = [jailTime EXCEPT ![turnPlayer] = 0]
    /\ goojfCcOwner' = NULL
    /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, debt, 
                   doublesCount, free4AllOrder, goojfChOwner, isBankrupt, 
                   jailIndex, money, phase, positions, turnPlayer>>
    
PayJailFine == 
    /\ ~terminated
    /\ inJail[turnPlayer]
    /\ money[turnPlayer] >= JailFine
    /\ PayBank(turnPlayer, JailFine)
    /\ inJail' = [inJail EXCEPT ![turnPlayer] = FALSE]
    /\ jailTime' = [jailTime EXCEPT ![turnPlayer] = 0]
    /\ UNCHANGED <<board, chanceCards, communityChestCards, debt, 
                   doublesCount, free4AllOrder, goojfCcOwner, goojfChOwner, 
                   isBankrupt, jailIndex, phase, positions, turnPlayer>>
    
UnmortgageProperty(player) == \E idx \in ownedPropertyIdxs(player):
    /\ board[idx].mortgaged
    /\ LET mortgageValue == board[idx].value \div 2
           unmortgageCost == mortgageValue + (mortgageValue \div 10)
       IN /\ money[player] >= unmortgageCost
          /\ board' = [board EXCEPT ![idx].mortgaged = FALSE]
          /\ PayBank(player, unmortgageCost)
          
MortgageProperty(player) == \E idx \in ownedPropertyIdxs(player):
    /\ ~board[idx].mortgaged
    /\ board[idx].type = "street" => noStreetFromSameSetHasBuildings(idx)
    /\ LET mortgageValue == board[idx].value \div 2
       IN /\ board' = [board EXCEPT ![idx].mortgaged = TRUE]
          /\ CollectFromBank(player, mortgageValue)
          
          
allFromSetAreHigherOrEqualLevel(set, level) ==
    \A idx \in DOMAIN board:
        IF board[idx].type /= "street"
        THEN TRUE
        ELSE board[idx].set = set => board[idx].level >= level          

UpgradeStreet(player) == \E idx \in ownedPropertyIdxs(player):
    /\ IF ~board[idx].type = "street"
       THEN FALSE
       ELSE LET street == board[idx]
            IN /\ ~street.mortgaged
               /\ ownsAllOfSet(player, street.set)
               /\ street.level < Len(board[idx].rent)
               /\ allFromSetAreHigherOrEqualLevel(street.set, street.level)
               /\ money[player] >= street.houseCost
               /\ board' = [board EXCEPT ![idx].level = @ + 1]
               /\ PayBank(player, street.houseCost)
               
allFromSetAreLowerOrEqualLevel(set, level) ==
    \A idx \in DOMAIN board:
        IF board[idx].type /= "street"
        THEN TRUE
        ELSE board[idx].set = set => board[idx].level <= level
               
DowngradeStreet(player) == \E idx \in ownedPropertyIdxs(player):
    /\ IF ~board[idx].type = "street"
       THEN FALSE
       ELSE LET street == board[idx]
            IN /\ street.level > 1
               /\ allFromSetAreLowerOrEqualLevel(street.set, street.level)
               /\ board' = [board EXCEPT ![idx].level = @ - 1]
               /\ CollectFromBank(player, street.houseCost \div 2)
          
PreRollUnmortgage ==
    /\ ~terminated
    /\ phase = "pre-roll"
    /\ UnmortgageProperty(turnPlayer)
    /\ UNCHANGED <<chanceCards, communityChestCards, debt, 
                   doublesCount, free4AllOrder, goojfCcOwner, 
                   goojfChOwner, inJail, isBankrupt, jailIndex, 
                   jailTime, phase, positions, turnPlayer>>
    
PreRollMortgage ==
    /\ ~terminated
    /\ phase = "pre-roll"
    /\ MortgageProperty(turnPlayer)
    /\ UNCHANGED <<chanceCards, communityChestCards, debt, 
                   doublesCount, free4AllOrder, goojfCcOwner, 
                   goojfChOwner, inJail, isBankrupt, jailIndex, 
                   jailTime, phase, positions, turnPlayer>>
    
PreRollUpgrade ==
    /\ ~terminated
    /\ phase = "pre-roll"
    /\ UpgradeStreet(turnPlayer)
    /\ UNCHANGED <<chanceCards, communityChestCards, debt, doublesCount, 
                   free4AllOrder, goojfCcOwner, goojfChOwner, inJail, 
                   isBankrupt, jailIndex, jailTime, phase, positions, turnPlayer>>
    
PreRollDowngrade ==
    /\ ~terminated
    /\ phase = "pre-roll"
    /\ DowngradeStreet(turnPlayer)
    /\ UNCHANGED <<chanceCards, communityChestCards, debt, doublesCount, 
                   free4AllOrder, goojfCcOwner, goojfChOwner, inJail, 
                   isBankrupt, jailIndex, jailTime, phase, positions, turnPlayer>>
                   
TakePreRollAction == 
    \/ EndPreRoll
    \/ PlayGoojfCh
    \/ PlayGoojfCc
    \/ PayJailFine
    \/ PreRollUnmortgage
    \/ PreRollMortgage
    \/ PreRollUpgrade
    \/ PreRollDowngrade

ChangeOwnerOfProperties(from, to) == 
    /\ board' = [i \in DOMAIN board |-> 
                 LET field == board[i]
                 IN IF isProperty(field)
                    THEN IF field.owner = from 
                         THEN [field EXCEPT !.owner = to]
                         ELSE field
                    ELSE field]
    /\ IF goojfCcOwner = from
       THEN goojfCcOwner' = to
       ELSE UNCHANGED <<goojfCcOwner>>
    /\ IF goojfChOwner = from
       THEN goojfChOwner' = to
       ELSE UNCHANGED <<goojfChOwner>>                           
    
CollectIfPassGo ==
    IF positions'[turnPlayer] < positions[turnPlayer]
    THEN CollectFromBank(turnPlayer, PassGoReward)
    ELSE UNCHANGED <<money, bankMoney>>

MoveAfterRoll(amount) ==
    /\ positions' = [positions EXCEPT ![turnPlayer] = incrCirc(@, amount, Len(board))]
    /\ CollectIfPassGo
    
GoToJail == 
    /\ inJail' = [inJail EXCEPT ![turnPlayer] = TRUE]
    /\ doublesCount' = 0
    /\ positions' = [positions EXCEPT ![turnPlayer] = jailIndex]
    /\ initializeFree4All

RollAndMove == 
    \E d1,d2 \in 1..DiceMax :
      /\ ~terminated
      /\ phase = "roll"
      /\ inJail[turnPlayer] = FALSE
      /\ IF d1 /= d2 
         THEN /\ MoveAfterRoll(d1+d2)
              /\ doublesCount' = 0
              /\ phase' = "post-roll"
              /\ UNCHANGED <<inJail, free4AllOrder>>
         ELSE IF doublesCount = 2 \* Current throw is 3rd consecutive doubles
              THEN /\ GoToJail
                   /\ UNCHANGED <<bankMoney, money>>
              ELSE /\ MoveAfterRoll(d1+d2)
                   /\ doublesCount' = doublesCount + 1
                   /\ phase' = "post-roll"
                   /\ UNCHANGED <<inJail, free4AllOrder>>
      /\ UNCHANGED <<board, chanceCards, communityChestCards, debt, goojfCcOwner, 
                    goojfChOwner, isBankrupt, jailIndex, jailTime, turnPlayer>>
      
RollInJail ==
    \E d1,d2 \in 1..DiceMax :
      /\ ~terminated
      /\ phase = "roll"
      /\ inJail[turnPlayer] = TRUE
      /\ IF d1 /= d2
         THEN IF jailTime[turnPlayer] = 2 \* has missed doubles for the 3rd time
              THEN /\ MoveAfterRoll(d1+d2)
                   /\ jailTime' = [jailTime EXCEPT ![turnPlayer] = 0]
                   /\ inJail' = [inJail EXCEPT ![turnPlayer] = FALSE]
                   /\ IF money[turnPlayer] >= JailFine
                      THEN /\ PayBank(turnPlayer, JailFine)
                           /\ phase' = "post-roll"
                           /\ UNCHANGED <<debt>>
                      ELSE /\ phase' = "bankruptcy-prevention"
                           /\ debt' = [creditor |-> NULL,
                                       amount |-> JailFine,
                                       nextPhase |-> "post-roll"]
                   /\ UNCHANGED <<free4AllOrder>>
              ELSE /\ jailTime' = [jailTime EXCEPT ![turnPlayer] = @ + 1]
                   /\ initializeFree4All
                   /\ UNCHANGED <<money, bankMoney, positions, inJail, debt>>
         ELSE /\ MoveAfterRoll(d1+d2) \* Player will not get to roll again even if they rolled doubles.
              /\ jailTime' = [jailTime EXCEPT ![turnPlayer] = 0]
              /\ inJail' = [inJail EXCEPT ![turnPlayer] = FALSE]
              /\ phase' = "post-roll"
              /\ UNCHANGED <<free4AllOrder, debt>>
      /\ UNCHANGED <<board, chanceCards, communityChestCards, doublesCount, 
                    goojfCcOwner, goojfChOwner, isBankrupt, jailIndex, turnPlayer>>
         
TakeRollAction == \/ RollAndMove
                  \/ RollInJail
   
BuyProperty == 
    IF ~isProperty(currentSquare)
    THEN FALSE
    ELSE /\ ~terminated
         /\ phase = "post-roll"
         /\ currentSquare.owner = NULL
         /\ money[turnPlayer] >= currentSquare.value
         /\ PayBank(turnPlayer, currentSquare.value)
         /\ board' = [board EXCEPT ![positions[turnPlayer]].owner = turnPlayer]
         /\ phase' = "doubles-check"
         /\ UNCHANGED <<inJail, positions, turnPlayer, doublesCount, jailTime, 
                        isBankrupt, goojfCcOwner, goojfChOwner, chanceCards, 
                        communityChestCards, debt, free4AllOrder, jailIndex>>
             
PayPlayer(from, to, amount) == 
    money' = [money EXCEPT ![from] = @ - amount,
                           ![to] = @ + amount]
                
getStreetRent(street) ==
    IF street.level > 1
    THEN street.rent[street.level]
    ELSE IF ownsAllOfSet(street.owner, street.set)
         THEN street.rent[1] * 2
         ELSE street.rent[1]
                   
PayStreetRent == 
    IF currentSquare.type /= "street"
    THEN FALSE
    ELSE /\ ~terminated
         /\ phase = "post-roll"
         /\ LET rentCost == getStreetRent(currentSquare)
                owner == currentSquare.owner
            IN /\ owner \notin {NULL, turnPlayer}
               /\ ~currentSquare.mortgaged
               /\ money[turnPlayer] >= rentCost
               /\ PayPlayer(turnPlayer, owner, rentCost)
               /\ phase' = "doubles-check"
         /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, 
                        debt, doublesCount, free4AllOrder, goojfCcOwner, goojfChOwner, 
                        inJail, isBankrupt, jailIndex, jailTime, positions, turnPlayer>>
               
PreventBankruptcyOnStreetRent ==
    IF currentSquare.type /= "street"
    THEN FALSE
    ELSE /\ ~terminated
         /\ phase = "post-roll"
         /\ LET rentCost == getStreetRent(currentSquare)
                owner == currentSquare.owner
            IN /\ owner \notin {NULL, turnPlayer}
               /\ ~currentSquare.mortgaged
               /\ money[turnPlayer] < rentCost
               /\ debt = NULL
               /\ debt' = [creditor |-> owner,
                           amount |-> rentCost,
                           nextPhase |-> "doubles-check"]
               /\ phase' = "bankruptcy-prevention"
        /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, doublesCount, 
                       free4AllOrder, goojfCcOwner, goojfChOwner, inJail, isBankrupt, 
                       jailIndex, jailTime, money, positions, turnPlayer>>
               
getRailRent(owner) ==
    LET ownedRails == Cardinality({
        i \in DOMAIN board:
            IF ~board[i].type = "rail"
            THEN FALSE
            ELSE board[i].owner = owner
        })
    IN BaseRailRent * 2 ^ (ownedRails - 1)
              
PayRailRent == 
    IF currentSquare.type /= "rail"
    THEN FALSE
    ELSE /\ ~terminated
         /\ phase = "post-roll"
         /\ LET owner == currentSquare.owner
                rentCost == getRailRent(owner)
            IN /\ owner \notin {NULL, turnPlayer}
               /\ ~currentSquare.mortgaged
               /\ money[turnPlayer] >= rentCost
               /\ PayPlayer(turnPlayer, owner, rentCost)
               /\ phase' = "doubles-check"
         /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, debt, 
                       doublesCount, free4AllOrder, goojfCcOwner, goojfChOwner, inJail, 
                       isBankrupt, jailIndex, jailTime, positions, turnPlayer>>
               
PreventBankruptcyOnRailRent ==
    IF currentSquare.type /= "rail"
    THEN FALSE
    ELSE /\ ~terminated
         /\ phase = "post-roll"
         /\ LET owner == currentSquare.owner
                rentCost == getRailRent(owner)
            IN /\ owner \notin {NULL, turnPlayer}
               /\ ~currentSquare.mortgaged
               /\ money[turnPlayer] < rentCost
               /\ debt = NULL
               /\ debt' = [creditor |-> owner,
                           amount |-> rentCost,
                           nextPhase |-> "doubles-check"]
               /\ phase' = "bankruptcy-prevention"
        /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, doublesCount, 
                       free4AllOrder, goojfCcOwner, goojfChOwner, inJail, isBankrupt, jailIndex, 
                       jailTime, money, positions, turnPlayer>>

ownsBothUtilities(owner) ==
    LET ownedUtils == Cardinality({
        i \in DOMAIN board:
            IF board[i].type /= "util"
            THEN FALSE
            ELSE board[i].owner = owner
        })
    IN ownedUtils = 2

TryPayUtilRent == 
    IF currentSquare.type /= "util"
    THEN FALSE
    ELSE \E d1,d2 \in 1..DiceMax :
           /\ ~terminated
           /\ phase = "post-roll"
           /\ LET owner == currentSquare.owner
                  multiplier == IF ownsBothUtilities(owner) THEN 10 ELSE 4
                  rentCost == (d1 + d2) * multiplier
              IN /\ owner \notin {NULL, turnPlayer}
                 /\ IF money[turnPlayer] >= rentCost
                    THEN /\ PayPlayer(turnPlayer, owner, rentCost)
                         /\ phase' = "doubles-check"
                         /\ UNCHANGED <<debt>>
                    ELSE /\ debt = NULL
                         /\ debt' = [creditor |-> owner,
                                     amount |-> rentCost,
                                     nextPhase |-> "doubles-check"]
                         /\ phase' = "bankruptcy-prevention"
                         /\ UNCHANGED <<money>>
           /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, doublesCount, 
                         free4AllOrder, goojfCcOwner, goojfChOwner, inJail, isBankrupt, 
                         jailIndex, jailTime, positions, turnPlayer>>
                
PayTax == 
    IF currentSquare.type /= "tax"
    THEN FALSE
    ELSE /\ ~terminated
         /\ phase = "post-roll"
         /\ money[turnPlayer] >= currentSquare.value
         /\ PayBank(turnPlayer, currentSquare.value)
         /\ phase' = "doubles-check"
         /\ UNCHANGED <<board, chanceCards, communityChestCards, debt, 
                        doublesCount, free4AllOrder, goojfCcOwner, goojfChOwner, 
                        inJail, isBankrupt, jailIndex, jailTime, positions, turnPlayer>>
         
PreventBankruptcyOnTax ==
    IF currentSquare.type /= "tax"
    THEN FALSE
    ELSE /\ ~terminated
         /\ phase = "post-roll"
         /\ money[turnPlayer] < currentSquare.value
         /\ debt' = [creditor |-> NULL,
                     amount |-> currentSquare.value,
                     nextPhase |-> "doubles-check"]
         /\ phase' = "bankruptcy-prevention"
         /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, 
                        doublesCount, free4AllOrder, goojfCcOwner, goojfChOwner, 
                        inJail, isBankrupt, jailIndex, jailTime, money, positions, turnPlayer>>

AuctionProperty == 
    IF ~isProperty(currentSquare)
    THEN FALSE
    ELSE /\ ~terminated
         /\ phase = "post-roll"
         /\ currentSquare.owner = NULL
         /\ \/ \E winner \in 1..NumPlayers:
               \E bid \in {1, 5, 10}: \* should theoretically be 1..money[winner] but this makes state space explode
                  /\ money[winner] >= bid \* would be unnecessary with 1..money[winner]
                  /\ ~isBankrupt[winner]
                  /\ PayBank(winner, bid)
                  /\ board' = [board EXCEPT ![positions[turnPlayer]].owner = winner]
            \/ UNCHANGED <<board, bankMoney, money>>
         /\ phase' = "doubles-check"
         /\ UNCHANGED <<chanceCards, communityChestCards, debt, doublesCount, 
                        free4AllOrder, goojfCcOwner, goojfChOwner, inJail, isBankrupt,
                        jailIndex, jailTime, positions, turnPlayer>>
            
LandOnGoToJail ==
    /\ ~terminated
    /\ currentSquare.type = "go-to-jail"
    /\ GoToJail
    /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, 
                  debt, goojfCcOwner, goojfChOwner, isBankrupt, jailIndex, 
                  jailTime, money, turnPlayer>>
    
                  
AdvanceTo(destinationIdx) ==
    /\ positions' = [positions EXCEPT ![turnPlayer] = destinationIdx]
    /\ CollectIfPassGo
    
    
ExecuteCard(card) ==
    LET type == card.type
    IN CASE type = "collect" -> /\ CollectFromBank(turnPlayer, card.amount)
                                /\ phase' = "doubles-check"
                                /\ UNCHANGED <<debt, positions, goojfCcOwner, goojfChOwner, 
                                               doublesCount, inJail, free4AllOrder>>
         [] type = "pay" -> IF money[turnPlayer] >= card.amount
                            THEN /\ PayBank(turnPlayer, card.amount) 
                                 /\ phase' = "doubles-check" 
                                 /\ UNCHANGED <<debt, positions, goojfCcOwner, goojfChOwner, 
                                                doublesCount, inJail, free4AllOrder>>
                            ELSE /\ debt' = [creditor |-> NULL,
                                            amount |-> card.amount,
                                            nextPhase |-> "doubles-check"]
                                 /\ phase' = "bankruptcy-prevention" 
                                 /\ UNCHANGED <<money, bankMoney, goojfCcOwner, 
                                                goojfChOwner, positions, doublesCount, 
                                                inJail, free4AllOrder>>
         [] type = "advance" -> /\ AdvanceTo(card.square) 
                                /\ UNCHANGED <<debt, goojfCcOwner, goojfChOwner, phase,
                                               doublesCount, inJail, free4AllOrder>>
         [] type = "go-to-jail" -> /\ GoToJail
                                   /\ UNCHANGED <<debt, goojfCcOwner, goojfChOwner, 
                                                  money, bankMoney>>
         [] type = "goojf-cc" -> /\ goojfCcOwner' = turnPlayer
                                 /\ phase' = "doubles-check" 
                                 /\ UNCHANGED <<money, bankMoney, positions, goojfChOwner,
                                               debt, doublesCount, inJail, free4AllOrder>>
         [] type = "goojf-ch" -> /\ goojfChOwner' = turnPlayer
                                 /\ phase' = "doubles-check"
                                 /\ UNCHANGED <<money, bankMoney, positions, goojfCcOwner,
                                                debt, doublesCount, inJail, free4AllOrder>>


DrawAndExecuteChanceCard ==
    IF currentSquare.type /= "chance"
    THEN FALSE
    ELSE /\ ~terminated
         /\ phase = "post-roll"
         /\ \E cardIdx \in IF goojfChOwner = NULL 
                  THEN 1..Len(chanceCards) 
                  ELSE 1..(Len(chanceCards)-1) :
              LET card == chanceCards[cardIdx]
              IN ExecuteCard(card)
         /\ UNCHANGED <<board, chanceCards, communityChestCards, isBankrupt, 
                        jailIndex, jailTime, turnPlayer>>
              
DrawAndExecuteCommunityChestCard ==
    IF currentSquare.type /= "community-chest"
    THEN FALSE
    ELSE /\ ~terminated
         /\ phase = "post-roll"
         /\ \E cardIdx \in IF goojfCcOwner = NULL 
                  THEN 1..Len(communityChestCards) 
                  ELSE 1..(Len(communityChestCards)-1) :
              LET card == communityChestCards[cardIdx]
              IN ExecuteCard(card)
         /\ UNCHANGED <<board, chanceCards, communityChestCards, isBankrupt, 
                        jailIndex, jailTime, turnPlayer>>

EndPostRoll ==
    /\ phase = "post-roll"
    /\ phase' = "doubles-check"  

DoNothingOnOwnProperty == 
    IF ~isProperty(currentSquare)
    THEN FALSE
    ELSE /\ ~terminated
         /\ currentSquare.owner = turnPlayer
         /\ EndPostRoll
         /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, debt, 
                        doublesCount, free4AllOrder, goojfCcOwner, goojfChOwner, inJail, 
                        isBankrupt, jailIndex, jailTime, money, positions, turnPlayer>>


DoNothingOnJailSquare ==
    /\ ~terminated
    /\ currentSquare.type = "jail"
    /\ EndPostRoll
    /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, debt, 
                        doublesCount, free4AllOrder, goojfCcOwner, goojfChOwner, inJail, 
                        isBankrupt, jailIndex, jailTime, money, positions, turnPlayer>>
   

DoNothingOnGo ==
    /\ ~terminated
    /\ currentSquare.type = "go"
    /\ EndPostRoll
    /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, debt, 
                        doublesCount, free4AllOrder, goojfCcOwner, goojfChOwner, inJail, 
                        isBankrupt, jailIndex, jailTime, money, positions, turnPlayer>>
    
            
DoNothingOnFreeParking ==
    /\ ~terminated
    /\ currentSquare.type = "free-parking"
    /\ EndPostRoll
    /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, debt, 
                        doublesCount, free4AllOrder, goojfCcOwner, goojfChOwner, inJail, 
                        isBankrupt, jailIndex, jailTime, money, positions, turnPlayer>>

            
DoNothingOnMortgagedProperty ==
    IF ~isProperty(currentSquare)
    THEN FALSE
    ELSE /\ ~terminated
         /\ currentSquare.owner /= turnPlayer
         /\ currentSquare.mortgaged
         /\ EndPostRoll
         /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, debt, 
                        doublesCount, free4AllOrder, goojfCcOwner, goojfChOwner, inJail, 
                        isBankrupt, jailIndex, jailTime, money, positions, turnPlayer>>
     
TakePostRollAction == 
    \/ DoNothingOnOwnProperty
    \/ DoNothingOnJailSquare
    \/ DoNothingOnGo
    \/ DoNothingOnFreeParking
    \/ DoNothingOnMortgagedProperty
    \/ PayStreetRent
    \/ PayRailRent
    \/ PreventBankruptcyOnStreetRent
    \/ PreventBankruptcyOnRailRent
    \/ TryPayUtilRent
    \/ BuyProperty
    \/ AuctionProperty
    \/ PayTax
    \/ PreventBankruptcyOnTax
    \/ LandOnGoToJail
    \/ DrawAndExecuteChanceCard
    \/ DrawAndExecuteCommunityChestCard

DoublesCheck ==
    /\ ~terminated
    /\ phase = "doubles-check"
    /\ IF doublesCount > 0
       THEN /\ phase' = "pre-roll"
            /\ UNCHANGED <<free4AllOrder>>
       ELSE initializeFree4All
    /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, debt, 
                   doublesCount, goojfCcOwner, goojfChOwner, inJail, isBankrupt, 
                   jailIndex, jailTime, money, positions, turnPlayer>>
        
PayOffDebt ==
    IF phase /= "bankruptcy-prevention"
    THEN FALSE
    ELSE /\ ~terminated
         /\ money[turnPlayer] >= debt.amount
         /\ IF debt.creditor = NULL
            THEN PayBank(turnPlayer, debt.amount)
            ELSE /\ PayPlayer(turnPlayer, debt.creditor, debt.amount)
                 /\ UNCHANGED <<bankMoney>>
         /\ phase' = debt.nextPhase
         /\ debt' = NULL
         /\ UNCHANGED <<board, chanceCards, communityChestCards, doublesCount, 
                       free4AllOrder, goojfCcOwner, goojfChOwner, inJail, isBankrupt, 
                       jailIndex, jailTime, positions, turnPlayer>>
         
BankruptcyPreventionMortgage ==
    IF phase /= "bankruptcy-prevention"
    THEN FALSE
    ELSE /\ ~terminated
         /\ money[turnPlayer] < debt.amount
         /\ MortgageProperty(turnPlayer)
         /\ UNCHANGED <<chanceCards, communityChestCards, debt, 
                        doublesCount, free4AllOrder, goojfCcOwner, 
                        goojfChOwner, inJail, isBankrupt, jailIndex, 
                        jailTime, phase, positions, turnPlayer>>
         
BankruptcyPreventionDowngrade ==
    IF phase /= "bankruptcy-prevention"
    THEN FALSE
    ELSE /\ ~terminated
         /\ money[turnPlayer] < debt.amount
         /\ DowngradeStreet(turnPlayer)
         /\ UNCHANGED <<chanceCards, communityChestCards, debt, 
                        doublesCount, free4AllOrder, goojfCcOwner, 
                        goojfChOwner, inJail, isBankrupt, jailIndex, 
                        jailTime, phase, positions, turnPlayer>>

RECURSIVE BoardAfterBankruptcyToBank(_)
BoardAfterBankruptcyToBank(currentBoard) ==
    IF currentBoard = <<>> THEN <<>>
    ELSE LET field == Head(currentBoard)
         IN IF ~isProperty(field)
            THEN <<field>> \o BoardAfterBankruptcyToBank(Tail(currentBoard))
            ELSE IF field.owner = turnPlayer
                 THEN LET newField == [field EXCEPT !.owner = NULL,
                                                    !.mortgaged = FALSE]
                      IN <<newField>> \o BoardAfterBankruptcyToBank(Tail(currentBoard))
                 ELSE <<field>> \o BoardAfterBankruptcyToBank(Tail(currentBoard))
         
TransferAllAssetsToBank ==
    /\ PayBank(turnPlayer, money[turnPlayer])
    /\ IF goojfChOwner = turnPlayer
       THEN goojfChOwner' = NULL
       ELSE UNCHANGED <<goojfChOwner>>
    /\ IF goojfCcOwner = turnPlayer
       THEN goojfCcOwner' = NULL
       ELSE UNCHANGED <<goojfCcOwner>>
    /\ board' = BoardAfterBankruptcyToBank(board)
    
RECURSIVE BoardAfterBankruptcyToPlayer(_, _)
BoardAfterBankruptcyToPlayer(creditor, currentBoard) ==
    IF currentBoard = <<>> THEN <<>>
    ELSE LET field == Head(currentBoard)
         IN IF ~isProperty(field)
            THEN <<field>> \o BoardAfterBankruptcyToPlayer(creditor, Tail(currentBoard))
            ELSE IF field.owner = turnPlayer
                 THEN LET newField == [field EXCEPT !.owner = creditor]
                      IN <<newField>> \o BoardAfterBankruptcyToPlayer(creditor, Tail(currentBoard))
                 ELSE <<field>> \o BoardAfterBankruptcyToPlayer(creditor, Tail(currentBoard))

TransferAllAssetsToPlayer(creditor) ==
    /\ PayPlayer(turnPlayer, creditor, money[turnPlayer])
    /\ IF goojfChOwner = turnPlayer
       THEN goojfChOwner' = creditor
       ELSE UNCHANGED <<goojfChOwner>>
    /\ IF goojfCcOwner = turnPlayer
       THEN goojfCcOwner' = creditor
       ELSE UNCHANGED <<goojfCcOwner>>
    /\ board' = BoardAfterBankruptcyToPlayer(creditor, board)
    
RECURSIVE GiveTurnToNextLivePlayer(_)
GiveTurnToNextLivePlayer(curr) ==
    /\ LET next == incrCirc(curr, 1, NumPlayers)
       IN IF isBankrupt[next]
               THEN GiveTurnToNextLivePlayer(next)
               ELSE /\ turnPlayer' = next
                    /\ doublesCount' = 0
                    /\ free4AllOrder' = NULL
                    /\ phase' = "pre-roll"
       
GoBankrupt ==
    IF phase /= "bankruptcy-prevention"
    THEN FALSE
    ELSE /\ ~terminated
         /\ money[turnPlayer] < debt.amount
         /\ \A idx \in DOMAIN board:
                IF ~isProperty(board[idx]) THEN TRUE
                ELSE board[idx].owner = turnPlayer => board[idx].mortgaged
         /\ IF debt.creditor = NULL
            THEN TransferAllAssetsToBank
            ELSE /\ TransferAllAssetsToPlayer(debt.creditor)
                 /\ UNCHANGED <<bankMoney>>
         /\ isBankrupt' = [isBankrupt EXCEPT ![turnPlayer] = TRUE]
         /\ GiveTurnToNextLivePlayer(turnPlayer)
         /\ UNCHANGED <<chanceCards, communityChestCards, debt, inJail, 
                        jailIndex, jailTime, positions>>
       
TakeBankruptcyPreventionAction ==
    \/ PayOffDebt
    \/ BankruptcyPreventionMortgage
    \/ BankruptcyPreventionDowngrade
    \/ GoBankrupt
    
ConcludeFree4AllActions ==
    /\ ~terminated
    /\ phase = "free-4-all"
    /\ IF free4AllOrder = <<>>
       THEN FALSE
       ELSE /\ free4AllOrder' = Tail(free4AllOrder)
            /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, 
                           debt, doublesCount, goojfCcOwner, goojfChOwner, inJail, 
                           isBankrupt, jailIndex, jailTime, money, phase, 
                           positions, turnPlayer>>
       
F4AUnmortgage ==
    /\ ~terminated
    /\ phase = "free-4-all"
    /\ IF free4AllOrder = <<>>
       THEN FALSE
       ELSE LET player == Head(free4AllOrder)
            IN UnmortgageProperty(player)
    /\ UNCHANGED <<chanceCards, communityChestCards, debt, doublesCount, 
                   free4AllOrder, goojfCcOwner, goojfChOwner, inJail, isBankrupt, 
                   jailIndex, jailTime, phase, positions, turnPlayer>>
       
F4AMortgage ==
    /\ ~terminated
    /\ phase = "free-4-all"
    /\ IF free4AllOrder = <<>>
       THEN FALSE
       ELSE LET player == Head(free4AllOrder)
            IN MortgageProperty(player)
    /\ UNCHANGED <<chanceCards, communityChestCards, debt, doublesCount, 
                   free4AllOrder, goojfCcOwner, goojfChOwner, inJail, isBankrupt, 
                   jailIndex, jailTime, phase, positions, turnPlayer>>
            
F4AUpgrade ==
    /\ ~terminated
    /\ phase = "free-4-all"
    /\ IF free4AllOrder = <<>>
       THEN FALSE
       ELSE LET player == Head(free4AllOrder)
            IN UpgradeStreet(player)
    /\ UNCHANGED <<chanceCards, communityChestCards, debt, doublesCount, 
                   free4AllOrder, goojfCcOwner, goojfChOwner, inJail, isBankrupt, 
                   jailIndex, jailTime, phase, positions, turnPlayer>>
            
F4ADowngrade ==
    /\ ~terminated
    /\ phase = "free-4-all"
    /\ IF free4AllOrder = <<>>
       THEN FALSE
       ELSE LET player == Head(free4AllOrder)
            IN DowngradeStreet(player)
    /\ UNCHANGED <<chanceCards, communityChestCards, debt, doublesCount, 
                   free4AllOrder, goojfCcOwner, goojfChOwner, inJail, isBankrupt, 
                   jailIndex, jailTime, phase, positions, turnPlayer>>
            
EndTurn ==
    /\ ~terminated
    /\ phase = "free-4-all"
    /\ free4AllOrder = <<>>
    /\ GiveTurnToNextLivePlayer(turnPlayer)
    /\ UNCHANGED <<bankMoney, board, chanceCards, communityChestCards, 
                   debt, goojfCcOwner, goojfChOwner, inJail, isBankrupt, 
                   jailIndex, jailTime, money, positions>>
                     
TakeFree4AllAction == 
    \/ ConcludeFree4AllActions
    \/ F4AUnmortgage
    \/ F4AMortgage
    \/ F4AUpgrade
    \/ F4ADowngrade
    \/ EndTurn

Init == /\ turnPlayer = 1
        /\ positions = [i \in 1..NumPlayers |-> 1]
        /\ money = [i \in 1..NumPlayers |-> StartingMoney]
        /\ inJail = [i \in 1..NumPlayers |-> FALSE]
        /\ jailTime = [i \in 1..NumPlayers |-> 0]
        /\ isBankrupt = [i \in 1..NumPlayers |-> FALSE]
        /\ phase = "pre-roll"
        /\ bankMoney = TotalMoney - (NumPlayers * StartingMoney)
        /\ goojfChOwner = NULL
        /\ goojfCcOwner = NULL
        /\ doublesCount = 0
        /\ board = <<
            [type |-> "go"],
            [type |-> "street", value |-> 20, owner |-> NULL, set |-> 1, level |-> 1,
                  rent |-> <<1, 4, 10>>, houseCost |-> 10, mortgaged |-> FALSE],
            [type |-> "street", value |-> 22, owner |-> NULL, set |-> 1, level |-> 1,
                  rent |-> <<2, 8, 20>>, houseCost |-> 12, mortgaged |-> FALSE],
            [type |-> "community-chest"],
            [type |-> "chance"],
            [type |-> "tax", value |-> 20],
            [type |-> "rail", value |-> 25, owner |-> NULL, mortgaged |-> FALSE],
            [type |-> "jail"],
            [type |-> "rail", value |-> 25, owner |-> NULL, mortgaged |-> FALSE],
            [type |-> "free-parking"],
            [type |-> "util", value |-> 21, owner |-> NULL, mortgaged |-> FALSE],
            [type |-> "util", value |-> 21, owner |-> NULL, mortgaged |-> FALSE],
            [type |-> "go-to-jail"]>>
         /\ jailIndex = 8
         /\ free4AllOrder = NULL
         /\ debt = NULL
         /\ chanceCards = <<
             [type |-> "collect", amount |-> 10],
             [type |-> "pay", amount |-> 30],
             [type |-> "advance", square |-> 7],
             [type |-> "go-to-jail"],
             [type |-> "goojf-ch"]>>
         /\ communityChestCards = <<
             [type |-> "collect", amount |-> 20],
             [type |-> "pay", amount |-> 20],
             [type |-> "advance", square |-> 1],
             [type |-> "go-to-jail"],
             [type |-> "goojf-cc"]>>

Next == \/ TakePreRollAction
        \/ TakeRollAction
        \/ TakePostRollAction
        \/ DoublesCheck
        \/ TakeBankruptcyPreventionAction
        \/ TakeFree4AllAction
    
FairSpec == 
    /\ Init 
    /\ [][Next]_vars
    /\ WF_vars(Next)

TypeOK == /\ turnPlayer \in 1..NumPlayers
          /\ \A p \in 1..NumPlayers : 
                /\ positions[p] \in 1..Len(board)
                /\ money[p] \in 0..TotalMoney
                /\ inJail[p] \in BOOLEAN
                /\ isBankrupt[p] \in BOOLEAN
                /\ jailTime[p] \in 0..2
          /\ phase \in {"pre-roll", "roll", "post-roll", "bankruptcy-prevention" , 
                         "doubles-check", "free-4-all"}
          /\ bankMoney \in 0..TotalMoney
          /\ \A i \in DOMAIN board: 
               /\ board[i].type \in {"go", "street", "community-chest", 
                                     "chance", "tax", "rail", "jail", 
                                     "free-parking", "util", "go-to-jail"}
               /\ isProperty(board[i]) => /\ board[i].value \in Nat
                                          /\ board[i].owner \in 1..NumPlayers \cup {NULL}
                                          /\ board[i].mortgaged \in BOOLEAN
               /\ board[i].type = "street" => /\ board[i].set \in Nat
                                              /\ \A j \in DOMAIN board[i].rent: j \in Nat
                                              /\ board[i].level \in DOMAIN board[i].rent
                                              /\ board[i].houseCost \in Nat
               /\ board[i].type = "tax" => board[i].value \in Nat
          /\ goojfChOwner \in 1..NumPlayers \cup {NULL}
          /\ goojfCcOwner \in 1..NumPlayers \cup {NULL}
          /\ doublesCount \in 0..2
          /\ free4AllOrder \in {NULL} \cup Seq(1..NumPlayers)
          /\ free4AllOrder /= NULL => 
                 \A i1, i2 \in DOMAIN free4AllOrder:
                     \/ i1 = i2
                     \/ free4AllOrder[i1] /= free4AllOrder[i2]
          /\ debt \in {NULL} \cup [creditor : {NULL} \cup 1..NumPlayers,
                                   amount : Nat,
                                   nextPhase: {"pre-roll", "roll", "post-roll", 
                                              "doubles-check", "free-4-all"}]
          /\ \A i \in DOMAIN chanceCards:
               /\ chanceCards[i].type \in {"collect", "pay", "advance", 
                                           "go-to-jail", "goojf-ch"}
               /\ chanceCards[i].type \in {"collect", "pay"} 
                       => chanceCards[i].amount \in Nat
               /\ chanceCards[i].type = "advance" => chanceCards[i].square \in DOMAIN board
          /\ \A i \in DOMAIN communityChestCards:
               /\ communityChestCards[i].type \in {"collect", "pay", "advance", 
                                                   "go-to-jail", "goojf-cc"}
               /\ communityChestCards[i].type \in {"collect", "pay"} 
                       => communityChestCards[i].amount \in Nat
               /\ communityChestCards[i].type = "advance" 
                       => chanceCards[i].square \in DOMAIN board
          /\ jailIndex \in DOMAIN board       
             
InvNoPossessionsIfBankrupt ==
    \A p \in 1..NumPlayers:
        isBankrupt[p] => /\ Cardinality(ownedPropertyIdxs(p)) = 0
                         /\ money[p] = 0
                         /\ goojfChOwner /= p
                         /\ goojfCcOwner /= p
                         
InvNoActionsPossibleIfBankrupt ==
    \A p \in 1..NumPlayers:
        isBankrupt[p] => /\ turnPlayer /= p
                         /\ free4AllOrder /= NULL 
                              => \A i \in DOMAIN free4AllOrder: free4AllOrder[i] /= p

InvNoDebtToBankruptPlayer ==
    IF debt = NULL
    THEN TRUE
    ELSE debt.creditor /= NULL => ~isBankrupt[debt.creditor]
    
InvConservationOfMoney ==
    bankMoney + SeqSum(money) = TotalMoney
    
InvStreetLevelRange ==
    \A i1, i2 \in DOMAIN board:
      IF board[i1].type /= "street" \/ board[i2].type /= "street"
      THEN TRUE
      ELSE board[i1].set = board[i2].set 
         => abs(board[i1].level - board[i2].level) <= 1
             
=============================================================================
