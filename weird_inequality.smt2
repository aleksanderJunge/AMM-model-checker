( declare-datatype Token ( ( t0 ) ( t1 ) ( t2 ) ))

( declare-datatype TokenAmount (
    ( amount ( t Token ) (v Real) )
))

( declare-datatype Amm (
    ( amm (r0 TokenAmount) (r1 TokenAmount) )
))

( declare-datatypes (( Maybe 1 )) (
( par ( X ) ( ( nothing ) ( just ( val X ))))))

( declare-datatype State (
    (pair (amms  (Array Token (Array Token (Maybe Amm))))
          (users (Array String (Array Token Real)))
    )
))

( declare-datatype Txn (( tx ( user String ) ( from TokenAmount ) ( to TokenAmount))))

( define-fun swap ((state State)
                   (swp   Txn))
                   State
(
     ite (> 0 (v (from swp))) state
    (let ((foundAmm (select (select (amms state) (t (from swp))) (t (to swp)))))
        ( match foundAmm ((nothing state) ((just foundAmmX)
        (let ((swappingAmm (
            ite (= (t (r0 foundAmmX)) (t (from swp)))
                   foundAmmX
                   (amm (r1 foundAmmX) (r0 foundAmmX)))))
        (let ((payout (/ (* (v (from swp)) (v (r1 swappingAmm)))
                         (+ (v (from swp)) (v (r0 swappingAmm))))))
             (ite (and (<= 0      (v (to swp)))
                       (<= (v (to swp)) payout))
                  (let ((oldBal (select (users state) (user swp))))
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
                                  (amount (t (from swp)) (+ (v (r0 swappingAmm)) (v (from swp))))
                                  (amount (t (to swp)  ) (- (v (r1 swappingAmm)) payout))
                                  ))
                         )
                    (pair
                        (let ((oldTFromAmms (select (amms state) (t (from swp))))
                              (oldTToAmms   (select (amms state) (t (to swp)  ))))
                             (let ((tmpamms (store (amms state ) (t (from swp))
                                (store oldTFromAmms (t (to swp)) (just newAmm)))))
                              (store tmpamms (t (to swp)) (store oldTToAmms (t (from swp)) (just newAmm)))))
                        (store (users state) (user swp) newBal)
                        )))
                  state
            )
    )
)))))))
( define-fun getBal ((state State)
                     (name String)
                     (tau  Token)) 
                      Real 
(
    select (select (users state) name) tau
))
(define-fun lempt () (Array Token (Maybe Amm))
((as const (Array Token (Maybe Amm))) nothing))
(define-fun hempt () (Array Token (Array Token (Maybe Amm)))
((as const (Array Token (Array Token (Maybe Amm)))) lempt))
(define-fun baseUsers () (Array String (Array Token Real))
((as const (Array String (Array Token Real)))
         ((as const (Array Token Real)) 0.0)))
(define-fun baseWal () (Array Token Real)
((as const (Array Token Real)) 0.0))
( declare-const state0 State)

( declare-const txn0 Txn)
( declare-const state1 State)

( declare-const txn1 Txn)
( declare-const state2 State)

( declare-const txn2 Txn)
( declare-const state3 State)

( declare-const txn3 Txn)
( declare-const state4 State)

(assert (= (users state0) 
(store (store baseUsers "A" (store (store (store baseWal t0 (/ 0 1)) t1 (/ 0 1)) t2 (/ 4 1))) "B" (store (store (store baseWal t0 (/ 4 1)) t1 (/ 0 1)) t2 (/ 0 1)))
))

(assert (= (amms state0) 
(store (store (store hempt t0 (store lempt t1 (just (amm (amount t0 (/ 12 1)) (amount t1 (/ 12 1)))))) t1 (store (store lempt t0 (just (amm (amount t0 (/ 12 1)) (amount t1 (/ 12 1))))) t2 (just (amm (amount t1 (/ 12 1)) (amount t2 (/ 12 1)))))) t2 (store lempt t1 (just (amm (amount t1 (/ 12 1)) (amount t2 (/ 12 1))))))
))

(assert (and
  (= (user txn0) "A")
  (= (t (from txn0)) t1)
  (= (t (to   txn0)) t0)
  (>= (v (from txn0)) 0 )
  ;(< (v (from txn0)) 7 )
))

(assert (and
  (= (user txn1) "B")
  (= (t (from txn1)) t0)
  (= (t (to   txn1)) t1)
  (> (v (from txn1)) 0 )
  ;(< (v (from txn1)) 7 )

))

(assert (and
  (= (user txn2) "B")
  (= (t (from txn2)) t1)
  (= (t (to   txn2)) t2)
  (> (v (from txn2)) 0 )
  ;(< (v (from txn2)) 7 )

))


(assert (and
  (= (user txn3) "A")
  (= (t (from txn3)) t0)
  (= (t (to   txn3)) t1)
  (> (v (from txn3)) 0 )
  ;(< (v (from txn3)) 7 ) 
))


(assert (= state1 (swap state0 txn0)))
(assert (= state2 (swap state1 txn1)))
(assert (= state3 (swap state2 txn2)))
(assert (= state4 (swap state3 txn3)))

(assert (forall ((tau Token)) (>= (getBal state3 "B" tau) 0)))
(assert (forall ((tau Token)) (>= (getBal state4 "A" tau) 0)))

(assert (>= (select (select (users state4) "A") t0) (/ 4 1)))
(assert (>= (select (select (users state4) "B") t2) (/ 4 1)))



(check-sat)
(get-value (txn0))
(get-value (txn1))
(get-value (txn2))
(get-value (txn3))
