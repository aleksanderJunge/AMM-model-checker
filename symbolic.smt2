( declare-datatype Token ( ( t0 ) ( t1 ) ( t2 ) ))

( declare-datatype TokenAmount (
    ( amount ( t Token ) (v Real) )
))

( declare-datatype Amm (
    ( amm (r0 TokenAmount) (r1 TokenAmount) )
))


( declare-datatype Txn 
    (( tx ( user String ) ( from TokenAmount ) ( to TokenAmount))
))

(declare-datatypes ( (Pair 2) ) (
(par (X Y) ( (pair (fst X) (snd Y)) ))))

( define-fun swaplr ((users (Array String (Array Token Real)))
                    (swp   Txn)
                    (inAmm Amm))
                    (Pair Amm (Array String (Array Token Real)))
(
    let ((payout (/ (* (v (from swp)) (v (r1 inAmm)))
                    (+ (v (from swp)) (v (r0 inAmm))))))
         (ite (and (<= 0      (v (to swp)))
                   (<= (v (to swp)) payout))
              (let ((oldBal (select users (user swp))))
                (
                let ((newBal
                        (store
                            (store oldBal
                                   (t (to swp))
                                   (+ (select oldBal (t (to swp))) payout)
                            )
                            (t (from swp)) 
                            (- (select oldBal (t (from swp)))
                               (v (from swp)))))
                     (newAmm (amm
                              (amount (t (from swp)) (+ (v (r0 inAmm)) (v (from swp))))
                              (amount (t (to swp)  ) (- (v (r1 inAmm)) payout))
                              ))
                     )
                (pair
                    newAmm
                    (store users (user swp) newBal)
                    )))
              (pair inAmm users)
        )
))

( define-fun swaprl ((users (Array String (Array Token Real)))
                    (swp   Txn)
                    (inAmm Amm))
                    (Pair Amm (Array String (Array Token Real)))
(
    let ((payout (/ (* (v (from swp)) (v (r0 inAmm)))
                    (+ (v (from swp)) (v (r1 inAmm))))))
         (ite (and (<= 0      (v (to swp)))
                   (<= (v (to swp)) payout))
              (let ((oldBal (select users (user swp))))
                (
                let ((newBal
                        (store
                            (store oldBal
                                   (t (to swp))
                                   (+ (select oldBal (t (to swp))) payout)
                            )
                            (t (from swp)) 
                            (- (select oldBal (t (from swp)))
                               (v (from swp)))))
                     (newAmm (amm
                              (amount (t (to   swp)) (- (v (r0 inAmm)) payout))
                              (amount (t (from swp)) (+ (v (r1 inAmm)) (v (from swp))))
                              ))
                     )
                (pair
                    newAmm
                    (store users (user swp) newBal)
                    )))
              (pair inAmm users)
        )
))

( define-fun getBal ((users (Array String (Array Token Real)))
                     (name String)
                     (tau  Token)) 
                      Real 
(
    select (select users name) tau
))

(define-fun baseUsers () (Array String (Array Token Real))
((as const (Array String (Array Token Real)))
         ((as const (Array Token Real)) 0.0)))

(define-fun baseWal () (Array Token Real)
((as const (Array Token Real)) 0.0))

( declare-const txn0 Txn)
( declare-const txn1 Txn)

( declare-const users0 (Array String (Array Token Real)))
( declare-const users1 (Array String (Array Token Real)))
( declare-const users2 (Array String (Array Token Real)))

( declare-const t0t1_0 Amm)
( declare-const t1t2_0 Amm)

( declare-const t0t1_1 Amm)
( declare-const t1t2_1 Amm)

( declare-const t0t1_2 Amm)
( declare-const t1t2_2 Amm)


;######## Symbolic assertions ############

; TOO DEMANDING IN TERMS OF COMPUTE
;(assert (forall ((user String))
;    (=> (not (= user "A"))
;        (= (select users0 user) baseWal))))

; BETTER:
( declare-const walletA (Array Token Real))

(assert (= users0 
    (store baseUsers "A" walletA)
))

; AMMs have distinct tokens
(assert (distinct (t (r0 t0t1_0)) 
                  (t (r1 t0t1_0))))

(assert (distinct (t (r0 t1t2_0)) 
                  (t (r1 t1t2_0))))

; TODO: determine if this is hensigtsmæssigt when it comes to symbolic... how much should Haskell vs. Z3 do?
; swapping from/to fields match the input AMM!
(assert (= (t (from txn0)) (t (r0 t0t1_0))))
(assert (= (t (to   txn0)) (t (r1 t0t1_0))))
(assert (= (t (from txn1)) (t (r0 t1t2_1))))
(assert (= (t (to   txn1)) (t (r1 t1t2_1))))

; AMMs have positive reserves
(assert (and
    (< 0 (v (r0 t0t1_0)))
    (< 0 (v (r1 t0t1_0)))))

(assert (and
    (< 0 (v (r0 t1t2_0)))
    (< 0 (v (r1 t1t2_0)))))

; Transactions aren't rejected:
(assert (not (= t0t1_0 t0t1_1)))
(assert (not (= t1t2_1 t1t2_2)))
; This is assuming that we know the AMMs that transactions are made on, from Haskell

;######### 'Chain' Assertions ############

(assert (> (v (from txn0)) 0))
(assert (= (user txn0) "A"))
(assert (= (t (from txn0)) t0))
(assert (= (t (to   txn0)) t1))

(assert (> (v (from txn1)) 0))
(assert (= (user txn1) "A"))
(assert (= (t (from txn1)) t1))
(assert (= (t (to   txn1)) t2))

(assert (= users1 (snd (swaplr users0 txn0 t0t1_0))))
(assert (= t0t1_1 (fst (swaplr users0 txn0 t0t1_0))))
(assert (= t1t2_1 t1t2_0))

(assert (>= (select (select users1 "A") t0) 0)) ; swapped out, but never back in... thus must be > 0
(assert (>= (select (select users1 "A") t1) 0)) ; let's just assume a green state / normal AMM
(assert (>= (select (select users1 "A") t2) 0)) ; let's just assume a green state / normal AMM

(assert (= users2 (snd (swaplr users1 txn1 t1t2_1))))
(assert (= t0t1_2 t0t1_1))
(assert (= t1t2_2 (fst (swaplr users1 txn1 t1t2_1))))

(assert (>= (select (select users2 "A") t0) 0)) ; swapped out, but never back in... thus must be > 0
(assert (>= (select (select users2 "A") t1) 0)) ; swapped out, but never back in... thus must be > 0
(assert (>= (select (select users2 "A") t2) 0)) ; last swap... all user balances must be clean


; ############ Goals #############
(assert (>= (select (select users2 "A") t0) (/ 4 1)))

(check-sat)
;(get-value (t0t1_0))
;(get-value (t1t2_0))
;(get-value (t0t1_1))
;(get-value (t1t2_1))
;(get-value (t0t1_2))
;(get-value (t1t2_2))
(get-value (walletA))
(get-value (users2))
;(get-model)
;(get-value (txn0))
;(get-value (txn1))
