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

( declare-const t0t1_0 Amm)

( declare-const users0 (Array String (Array Token Real)))


;######## Symbolic assertions ############

; Only solving for user A's wallet:
( declare-const walletA (Array Token Real))

(assert (= users0 
    (store baseUsers "A" walletA)
))

; AMMs have distinct tokens
(assert (distinct (t (r0 t0t1_0)) 
                  (t (r1 t0t1_0))))

; swapping from/to fields match the input AMM!
(assert (= (t (from txn0)) (t (r0 t0t1_0))))
(assert (= (t (to   txn0)) (t (r1 t0t1_0))))

; AMMs have positive reserves
(assert (and
    (< 0 (v (r0 t0t1_0)))
    (< 0 (v (r1 t0t1_0)))))


;############ base case ################

(push 1)

(assert 
    (or 
        (> 0 (v (r0 t0t1_0)))
        (> 0 (v (r1 t0t1_0)))
    )
)
(check-sat)

(pop 1)


;######### Induction case ############

(push 1)

( declare-const witness Txn)
( declare-const witness_amm Amm)

(assert (= witness_amm (fst (swaplr users0 witness t0t1_0))))

; Transaction isn't rejected:
(assert (not (= t0t1_0 witness_amm)))

; swapping from/to fields match the input AMM!
(assert (= (t (from witness)) (t (r0 t0t1_0))))
(assert (= (t (to   witness)) (t (r1 t0t1_0))))

( assert (= (user witness) "A"))
( assert (> (v (from witness)) 0 ))

; ############ search for witness #############

(assert 
    (or 
        (> 0 (v (r0 witness_amm)))
        (> 0 (v (r1 witness_amm)))
    )
)

(check-sat)
(get-value (witness))
(get-value (witness_amm))
(pop 1)
