;(set-option :interactive-mode true)
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
( declare-const txn2 Txn)
( declare-const txn3 Txn)

( declare-const users0 (Array String (Array Token Real)))
( declare-const users1 (Array String (Array Token Real)))
( declare-const users2 (Array String (Array Token Real)))
( declare-const users3 (Array String (Array Token Real)))
( declare-const users4 (Array String (Array Token Real)))

( declare-const t0t1_0 Amm)
( declare-const t1t2_0 Amm)

( declare-const t0t1_1 Amm)
( declare-const t1t2_1 Amm)

( declare-const t0t1_2 Amm)
( declare-const t1t2_2 Amm)

( declare-const t0t1_3 Amm)
( declare-const t1t2_3 Amm)

( declare-const t0t1_4 Amm)
( declare-const t1t2_4 Amm)

(assert (= users0
(store (store baseUsers "A" (store (store (store baseWal t0 (/ 0 1)) t1 (/ 0 1)) t2 (/ 4 1))) "B" (store (store (store baseWal t0 (/ 4 1)) t1 (/ 0 1)) t2 (/ 0 1)))
))

(assert (= t0t1_0 (amm (amount t0 (/ 12 1)) (amount t1 (/ 12 1)))))
(assert (= t1t2_0 (amm (amount t1 (/ 12 1)) (amount t2 (/ 12 1)))))

(assert (> (v (from txn0)) 0))
(assert (= (user txn0) "A"))
(assert (= (t (from txn0)) t2))
(assert (= (t (to   txn0)) t1))

(assert (> (v (from txn1)) 0))
(assert (= (user txn1) "B"))
(assert (= (t (from txn1)) t0))
(assert (= (t (to   txn1)) t1))

(assert (> (v (from txn2)) 0))
(assert (= (user txn2) "A"))
(assert (= (t (from txn2)) t1))
(assert (= (t (to   txn2)) t0))

(assert (> (v (from txn3)) 0))
(assert (= (user txn3) "B"))
(assert (= (t (from txn3)) t1))
(assert (= (t (to   txn3)) t2))

(assert (= users1 (snd (swaprl users0 txn0 t1t2_0))))
(assert (= t0t1_1 t0t1_0))
(assert (= t1t2_1 (fst (swaprl users0 txn0 t1t2_0))))

(assert (>= (select (select users1 "A") t2) 0)) ; swapped out, but never back in... thus must be > 0

(assert (= users2 (snd (swaplr users1 txn1 t0t1_1))))
(assert (= t0t1_2 (fst (swaplr users1 txn1 t0t1_1))))
(assert (= t1t2_2 t1t2_1))

(assert (>= (select (select users2 "B") t0) 0)) ; swapped out, but never back in... thus must be > 0
(assert (>= (select (select users2 "A") t2) 0)) ; swapped out, but never back in... thus must be > 0

(assert (= users3 (snd (swaprl users2 txn2 t0t1_2))))
(assert (= t0t1_3 (fst (swaprl users2 txn2 t0t1_2))))
(assert (= t1t2_3 t1t2_2))

(assert (>= (select (select users3 "A") t1) 0)) ; swapped out, but never back in... thus must be > 0
(assert (>= (select (select users3 "B") t0) 0)) ; swapped out, but never back in... thus must be > 0
(assert (>= (select (select users3 "A") t2) 0)) ; swapped out, but never back in... thus must be > 0
(assert (>= (select (select users3 "A") t0) 0)) ; last swap... all user's balances must be gt0

(assert (= users4 (snd (swaplr users3 txn3 t1t2_3))))
(assert (= t0t1_4 t0t1_3))
(assert (= t1t2_4 (fst (swaplr users3 txn3 t1t2_3))))

(assert (>= (select (select users4 "B") t1) 0)) ; swapped out, but never back in... thus must be > 0
(assert (>= (select (select users4 "A") t1) 0)) ; swapped out, but never back in... thus must be > 0
(assert (>= (select (select users4 "B") t0) 0)) ; swapped out, but never back in... thus must be > 0
(assert (>= (select (select users4 "A") t2) 0)) ; swapped out, but never back in... thus must be > 0
(assert (>= (select (select users4 "B") t2) 0)) ; last swap... all user's balances must be gt0
(assert (>= (select (select users3 "A") t0) 0)) ; last swap... all user's balances must be gt0

; Goals
(assert (>= (select (select users4 "A") t0) (/ 4 1)))
(assert (>= (select (select users4 "B") t2) (/ 4 1)))

(check-sat)
;(get-value (txn0))
;(get-value (txn1))
;(get-value (txn2))
;(get-value (txn3))
;(get-assertions)
