(declare-datatype Token ((t0) (t1)))
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
( declare-const t0t1_1 Amm)


( declare-const txn2 Txn)
( declare-const users2 (Array String (Array Token Real)))
( declare-const t0t1_2 Amm)


( declare-const txn3 Txn)
( declare-const users3 (Array String (Array Token Real)))
( declare-const t0t1_3 Amm)


( declare-const txn4 Txn)
( declare-const users4 (Array String (Array Token Real)))
( declare-const t0t1_4 Amm)


(declare-const t0t1_0 Amm)
(declare-const alberto (Array Token Real))
(declare-const aleks (Array Token Real))
(assert (= (/ 100 1) (v (r0 t0t1_0))))
(assert (= (/ 10 1) (v (r1 t0t1_0))))
(assert (= t0 (t (r0 t0t1_0))))
(assert (= t1 (t (r1 t0t1_0))))
(assert (distinct (t (r0 t0t1_0)) (t (r1 t0t1_0))))
(assert (= (select alberto t0) (/ 1000 1)))
(assert (= (select alberto t1) (/ 1000 1)))
(assert (= (select aleks t0) (/ 1000 1)))
(assert (= (select aleks t1) (/ 1000 1)))
(assert (= users0 (store (store baseUsers "alberto" alberto) "aleks" aleks)))
(assert (>= (select (select users0 "aleks") t0) 0))
(assert (>= (select (select users0 "aleks") t1) 0))
(assert (>= (select (select users0 "alberto") t0) 0))
(assert (>= (select (select users0 "alberto") t1) 0))
(assert (>= (select (select users1 "aleks") t0) 0))
(assert (>= (select (select users1 "aleks") t1) 0))
(assert (>= (select (select users1 "alberto") t0) 0))
(assert (>= (select (select users1 "alberto") t1) 0))
(assert (>= (select (select users2 "aleks") t0) 0))
(assert (>= (select (select users2 "aleks") t1) 0))
(assert (>= (select (select users2 "alberto") t0) 0))
(assert (>= (select (select users2 "alberto") t1) 0))
(assert (>= (select (select users3 "aleks") t0) 0))
(assert (>= (select (select users3 "aleks") t1) 0))
(assert (>= (select (select users3 "alberto") t0) 0))
(assert (>= (select (select users3 "alberto") t1) 0))
(assert (>= (select (select users4 "aleks") t0) 0))
(assert (>= (select (select users4 "aleks") t1) 0))
(assert (>= (select (select users4 "alberto") t0) 0))
(assert (>= (select (select users4 "alberto") t1) 0))
(assert (>= (v (from txn1)) 0))
(assert (= (user txn1) "aleks"))
(assert (= (t (from txn1)) t0))
(assert (= (t (to   txn1)) t1))
(assert (>= (v (from txn2)) 0))
(assert (= (user txn2) "alberto"))
(assert (= (t (from txn2)) t0))
(assert (= (t (to   txn2)) t1))
(assert (>= (v (from txn3)) 0))
(assert (= (user txn3) "aleks"))
(assert (= (t (from txn3)) t1))
(assert (= (t (to   txn3)) t0))
(assert (>= (v (from txn4)) 0))
(assert (= (user txn4) "alberto"))
(assert (= (t (from txn4)) t0))
(assert (= (t (to   txn4)) t1))
;(assert (< (v (from txn4)) 1))

(assert (= users1 (snd (swaplr users0 txn1 t0t1_0))))
(assert (= t0t1_1 (fst (swaplr users0 txn1 t0t1_0))))
(assert (= users2 (snd (swaprl users1 txn2 t0t1_1))))
(assert (= t0t1_2 (fst (swaprl users1 txn2 t0t1_1))))
(assert (= users3 (snd (swaplr users2 txn3 t0t1_2))))
(assert (= t0t1_3 (fst (swaplr users2 txn3 t0t1_2))))
(assert (= users4 (snd (swaplr users3 txn4 t0t1_3))))
(assert (= t0t1_4 (fst (swaplr users3 txn4 t0t1_3))))

(assert 

(and 
    (and 
        (= 
            (select (select users4 "aleks") t1)
            (/ 990 1)
        ) 
        (> 
            (select (select users4 "aleks") t0) 
            (/ 1000 1)
        )
    ) 
    (> 
        (+ 
            (select (select users4 "alberto") t0) 
            (select (select users4 "alberto") t1)
        ) 
        (/ 2050 1)
    )
))

(check-sat)
(get-value (txn1))
(get-value (txn2))
(get-value (txn3))
(get-value (txn4))
