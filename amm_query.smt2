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
    let ((foundAmm (select (select (amms state) (t (from swp))) (t (to swp)))))
        ( match foundAmm ((nothing state) ((just foundAmmX)
        (let ((swappingAmm (
            ite (= (t (r0 foundAmmX)) (t (from swp)))
                   foundAmmX
                   (amm (r1 foundAmmX) (r0 foundAmmX)))))
        ; Calculate payout
        (let ((payout (/ (* (v (from swp)) (v (r1 swappingAmm)))
                         (+ (v (from swp)) (v (r0 swappingAmm))))))
              ; If swap withing x-rate, then execute, otherwise leave state unchanged
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
                    ; return new state
                    (pair
                        (let ((oldTFromAmms (select (amms state) (t (from swp))))
                              (oldTToAmms   (select (amms state) (t (to swp)  ))))
                              ; update lookup corresponding to selecting t0 -> t1
                             (let ((tmpamms (store (amms state ) (t (from swp))
                                (store oldTFromAmms (t (to swp)) (just newAmm)))))
                              (store tmpamms (t (to swp)) (store oldTToAmms (t (from swp)) (just newAmm)))))
                        (store (users state) (user swp) newBal)
                        )))
                  state
            )
    )
))))))
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
( declare-const state1 State)
( declare-const state2 State)
( declare-const state3 State)
( declare-const state4 State)

( declare-const txn0 Txn)
( declare-const txn1 Txn)
( declare-const txn2 Txn)
( declare-const txn3 Txn)

(assert (= (users state0) ...))
(assert (= (amms state0) ...))
(store (store baseUsers "A" (store (store (store baseWal t0 (/ 0 1)) t1 (/ 0 1)) t2 (/ 4 1))) "B" (store (store (store baseWal t0 (/ 4 1)) t1 (/ 0 1)) t2 (/ 0 1)))
))

(store (store (store hempt t0 (store lempt t1 (just (amm (amount t0 (/ 12 1)) (amount t1 (/ 12 1)))))) t1 (store (store lempt t0 (just (amm (amount t0 (/ 12 1)) (amount t1 (/ 12 1))))) t2 (just (amm (amount t1 (/ 12 1)) (amount t2 (/ 12 1)))))) t2 (store lempt t1 (just (amm (amount t1 (/ 12 1)) (amount t2 (/ 12 1))))))
))


(assert (> (v (from txn0)) 0 ))
(assert (> (v (from txn1)) 0 ))
(assert (> (v (from txn2)) 0 ))
(assert (> (v (from txn3)) 0 ))

(assert (and
  ;(= (user txn0) "A")
  (= (user txn0) "B")
  (= (v (from txn0)) 6)
  (= (t (from txn0)) t1)
  ;(= (t (to txn0)) t2)
))

(assert (and
  (= (user txn1) "A")
  ;(= (v (from txn1)) 6)
  (= (t (from txn1)) t1)
  ;(= (t (from txn1)) t0)
  ;(= (user txn1) "B")
))

(assert
  (= (user txn2) "A")
  ;(= (user txn2) "B")
)

(assert 
  ;(= (user txn3) "A")
  (= (user txn3) "B")
)

(assert (distinct (t (from txn0)) (t (to txn0))))
(assert (distinct (t (from txn1)) (t (to txn1))))
(assert (distinct (t (from txn2)) (t (to txn2))))
(assert (distinct (t (from txn3)) (t (to txn3))))

(assert (forall ((tau1 Token) (tau2 Token))
(and 
    (= (select (select (amms state0) tau1) tau2) 
       (select (select (amms state0) tau2) tau1))
    (match (select (select (amms state0) tau1) tau2) ((nothing true)
    ((just a) (distinct (t (r0 a)) (t (r1 a))))))
    (match (select (select (amms state0) tau1) tau2) ((nothing true)
    ((just a) (and (< 0 (v (r0 a))) (< 0 (v (r1 a)))))))
    (match (select (select (amms state0) tau1) tau2) ((nothing true)
    ((just a)  
        (xor (and (= (t (r0 a)) tau1) (= (t (r1 a)) tau2)) 
             (and (= (t (r1 a)) tau1) (= (t (r0 a)) tau2)))))))))

(assert (= state1 (swap state0 txn0)))
(assert (= state2 (swap state1 txn1)))
(assert (= state3 (swap state2 txn2)))
(assert (= state4 (swap state3 txn3)))

(assert (>= (select (select (users state4) "A") t0) (/ 3 1)))

(assert (forall ((tau Token))
(and
(>= (getBal state4 "A" tau) 0)
(>= (getBal state4 "B" tau) 0)
)))
(assert (exists ((tau Token))
(xor
    (< (getBal state1 "A" tau) 0)
    (< (getBal state1 "B" tau) 0)
)))
(assert (exists ((tau Token))
(or
    (< (getBal state2 "A" tau) 0)
    (< (getBal state2 "B" tau) 0)
)))
(assert (exists ((tau Token))
(or
    (< (getBal state3 "A" tau) 0)
    (< (getBal state3 "B" tau) 0)
)))

(check-sat)
(get-value (txn0))
(get-value (txn1))
(get-value (txn2))
(get-value (txn3))
