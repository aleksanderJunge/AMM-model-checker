(declare-datatype Token ((t0) (t1) (t2)))
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

(define-fun baseUsers () (Array String (Array Token Real))
((as const (Array String (Array Token Real)))
         ((as const (Array Token Real)) 0.0)))

( declare-const users0 (Array String (Array Token Real)))

( declare-const txn1 Txn)
( declare-const users1 (Array String (Array Token Real)))
( declare-const t2t0_1 Amm)
( declare-const t1t2_1 Amm)
( declare-const t0t1_1 Amm)


( declare-const txn2 Txn)
( declare-const users2 (Array String (Array Token Real)))
( declare-const t2t0_2 Amm)
( declare-const t1t2_2 Amm)
( declare-const t0t1_2 Amm)


( declare-const txn3 Txn)
( declare-const users3 (Array String (Array Token Real)))
( declare-const t2t0_3 Amm)
( declare-const t1t2_3 Amm)
( declare-const t0t1_3 Amm)


(declare-const t0t1_0 Amm)
(declare-const t1t2_0 Amm)
(declare-const t2t0_0 Amm)
(declare-const aleks (Array Token Real))
(assert (= (/ 18 1) (v (r0 t0t1_0))))
(assert (= (/ 8 1) (v (r1 t0t1_0))))
(assert (= t0 (t (r0 t0t1_0))))
(assert (= t1 (t (r1 t0t1_0))))
(assert (distinct (t (r0 t0t1_0)) (t (r1 t0t1_0))))
(assert (= (/ 18 1) (v (r0 t1t2_0))))
(assert (= (/ 8 1) (v (r1 t1t2_0))))
(assert (= t1 (t (r0 t1t2_0))))
(assert (= t2 (t (r1 t1t2_0))))
(assert (distinct (t (r0 t1t2_0)) (t (r1 t1t2_0))))
(assert (= (/ 18 1) (v (r0 t2t0_0))))
(assert (= (/ 8 1) (v (r1 t2t0_0))))
(assert (= t2 (t (r0 t2t0_0))))
(assert (= t0 (t (r1 t2t0_0))))
(assert (distinct (t (r0 t2t0_0)) (t (r1 t2t0_0))))
(assert (= (select aleks t0) (/ 6 1)))
(assert (= (select aleks t1) (/ 6 1)))
(assert (= (select aleks t2) (/ 6 1)))
(assert (= users0 (store baseUsers "aleks" aleks)))
(assert (>= (select (select users0 "aleks") t0) 0))
(assert (>= (select (select users0 "aleks") t1) 0))
(assert (>= (select (select users0 "aleks") t2) 0))
(assert (>= (select (select users1 "aleks") t0) 0))
(assert (>= (select (select users1 "aleks") t1) 0))
(assert (>= (select (select users1 "aleks") t2) 0))
(assert (>= (select (select users2 "aleks") t0) 0))
(assert (>= (select (select users2 "aleks") t1) 0))
(assert (>= (select (select users2 "aleks") t2) 0))
(assert (>= (select (select users3 "aleks") t0) 0))
(assert (>= (select (select users3 "aleks") t1) 0))
(assert (>= (select (select users3 "aleks") t2) 0))
(assert (> (v (from txn1)) 0))
(assert (= (user txn1) "aleks"))
(assert (= (t (from txn1)) t2))
(assert (= (t (to   txn1)) t1))
(assert (> (v (from txn2)) 0))
(assert (= (user txn2) "aleks"))
(assert (= (t (from txn2)) t0))
(assert (= (t (to   txn2)) t2))
(assert (> (v (from txn3)) 0))
(assert (= (user txn3) "aleks"))
(assert (= (t (from txn3)) t1))
(assert (= (t (to   txn3)) t0))

(assert (= users1 (snd (swaprl users0 txn1 t1t2_0))))
(assert (= t1t2_1 (fst (swaprl users0 txn1 t1t2_0))))
(assert (= t2t0_1 t2t0_0))
(assert (= t0t1_1 t0t1_0))

(assert (= users2 (snd (swaprl users1 txn2 t2t0_1))))
(assert (= t2t0_2 (fst (swaprl users1 txn2 t2t0_1))))
(assert (= t1t2_2 t1t2_1))
(assert (= t0t1_2 t0t1_1))

(assert (= users3 (snd (swaprl users2 txn3 t0t1_2))))
(assert (= t0t1_3 (fst (swaprl users2 txn3 t0t1_2))))
(assert (= t2t0_3 t2t0_2))
(assert (= t1t2_3 t1t2_2))

(define-fun totalBal ((bal (Array Token Real)))
                      (Real)
    (+
        (select bal t0)
        (select bal t1)
        (select bal t2))
)

;(assert (not (exists ((txnprime Txn))
;    (>
;        (totalBal (select (snd (swaprl users2 txnprime t0t1_2)) "aleks"))
;        (totalBal (select users3 "aleks"))
;    )
;)))
;(assert (= (select (select users3 "aleks") t0) 8))
;(assert (= (select (select users3 "aleks") t1) 8))
;(assert (= (select (select users3 "aleks") t2) 8))
(assert (= 24 (totalBal (select users3 "aleks"))))

;(assert (and (and (= (select (select users3 "aleks") t0) (/ 8 1)) (= (select (select users3 "aleks") t1) (/ 8 1))) (= (select (select users3 "aleks") t2) (/ 8 1))))
(check-sat)
(get-value (txn1))
(get-value (txn2))
(get-value (txn3))
