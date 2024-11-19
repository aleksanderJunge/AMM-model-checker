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
( declare-const t0t1_1 Amm)
( declare-const t0t1_2 Amm)


;######## Symbolic assertions ############

; Only solving for user A's wallet:
( declare-const walletA (Array Token Real))

(assert (= users0 
    (store baseUsers "A" walletA)
))

; AMMs have distinct tokens TODO: try adding this for next states too if problems
(assert (distinct (t (r0 t0t1_0)) 
                  (t (r1 t0t1_0))))

; from/to fields of txns matches the AMM to swap on!
; TODO: use this to assert the direction on the swaps? Or use haskell to direct search
(assert 
    (xor
        (and
            (= (t (from txn0)) (t (r0 t0t1_0)))
            (= (t (to   txn0)) (t (r1 t0t1_0)))
        )
        (and
            (= (t (to   txn0)) (t (r0 t0t1_0)))
            (= (t (from txn0)) (t (r1 t0t1_0)))
        )
    )
)
;TODO: add more for next swaps

(assert (= (t (from txn0)) (t (r0 t0t1_0))))
(assert (= (t (to   txn0)) (t (r1 t0t1_0))))

; AMMs have positive reserves
(assert (and
    (< 0 (v (r0 t0t1_0)))
    (< 0 (v (r1 t0t1_0)))))

; Transactions aren't rejected:
(assert (not (= t0t1_0 t0t1_1)))

;######### 'Chain' Assertions ############

(assert (> (v (from txn0)) 0))
(assert (= (user txn0) "A"))
(assert (= (t (from txn0)) t0))
(assert (= (t (to   txn0)) t1))

(assert (= users1 (snd (swaplr users0 txn0 t0t1_0))))
(assert (= t0t1_1 (fst (swaplr users0 txn0 t0t1_0))))

(assert (>= (select (select users1 "A") t0) 0))
(assert (>= (select (select users1 "A") t1) 0))
(assert (>= (select (select users1 "A") t2) 0))


( declare-const witness Txn)
( declare-const resultingAmm Amm)
( assert (= t0t1_1 (fst (swaprl users1 witness t0t1_1))))

; ############ search for witness #############

( assert (= (user witness) "A"))
( assert (= (t (from witness)) t1))
( assert (= (t (to   witness)) t0))
( assert (> (v (from witness)) 0 ))
( assert (> (v (to   witness)) 0 ))

; maybe assert distinctness? (add constraint to query?)
(declare-const witness_t0 Token)
(declare-const witness_t1 Token)

; current state
(declare-const witness_v0_s0 Real)
(declare-const witness_v1_s0 Real)

; next state
(declare-const witness_v0_s1 Real)
(declare-const witness_v1_s1 Real)



(assert 
    (exists (not 
        (=>
            (and
                (= (select (select users0 "A") witness_t0) witness_v0_s0)
                (= (select (select users0 "A") witness_t1) witness_v1_s0)
                (= (select (select users1 "A") witness_t0) witness_v0_s1)
                (= (select (select users1 "A") witness_t1) witness_v1_s1)
                (> witness_v1_s0 witness_v1_s1)
                (< witness_v0_s0 witness_v0_s1)
            )
            (exists

        
;(assert 
;    (exists ((v0 Real) (v1 Real))
;        (not 
;            (and
;                (= v0 (v (from txn0)))
;                (= v1 (v (to   txn0)))
;                (exists ((v2 Real) (v3 Real))
;                    (and
;                        (= v2 (v (from witness)))
;                        (= v3 (v (to   witness)))
;                        (= (pair t0t1_0 users0)
;                           (swaprl users1 
;                                   witness
;                                   t0t1_1)
;                        )
;                        (= resultingAmm (fst (swaprl users1 witness t0t1_1)))
;                   )
;                )
;            )
;        )
;    )
;)


(check-sat)
(get-value (t0t1_0))
(get-value (t0t1_1))
(get-value (txn0))
(get-value (witness))
(get-value (resultingAmm))
