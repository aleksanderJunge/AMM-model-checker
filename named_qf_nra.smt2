(set-logic QF_NRA)
(set-option :produce-unsat-cores true)


( declare-const a_t0_0   Real)
( declare-const a_t1_0   Real)
( declare-const a_t2_0   Real)
( declare-const l_t0t1_0 Real)
( declare-const r_t0t1_0 Real)
( declare-const l_t1t2_0 Real)
( declare-const r_t1t2_0 Real)
( declare-const l_t2t0_0 Real)
( declare-const r_t2t0_0 Real)

( declare-const a_t0_1   Real)
( declare-const a_t1_1   Real)
( declare-const a_t2_1   Real)
( declare-const l_t2t0_1 Real)
( declare-const r_t2t0_1 Real)
( declare-const l_t1t2_1 Real)
( declare-const r_t1t2_1 Real)
( declare-const l_t0t1_1 Real)
( declare-const r_t0t1_1 Real)
( declare-const from_1   Real)
( declare-const   to_1   Real)
( declare-const payout_1 Real)

( declare-const a_t0_2   Real)
( declare-const a_t1_2   Real)
( declare-const a_t2_2   Real)
( declare-const l_t2t0_2 Real)
( declare-const r_t2t0_2 Real)
( declare-const l_t1t2_2 Real)
( declare-const r_t1t2_2 Real)
( declare-const l_t0t1_2 Real)
( declare-const r_t0t1_2 Real)
( declare-const from_2   Real)
( declare-const   to_2   Real)
( declare-const payout_2 Real)

( declare-const a_t0_3   Real)
( declare-const a_t1_3   Real)
( declare-const a_t2_3   Real)
( declare-const l_t2t0_3 Real)
( declare-const r_t2t0_3 Real)
( declare-const l_t1t2_3 Real)
( declare-const r_t1t2_3 Real)
( declare-const l_t0t1_3 Real)
( declare-const r_t0t1_3 Real)
( declare-const from_3   Real)
( declare-const   to_3   Real)
( declare-const payout_3 Real)

; user assertions
(assert (! ( = a_t0_0 (/ 6 1)) :named f1))
(assert (! ( = a_t1_0 (/ 6 1)) :named f2))
(assert (! ( = a_t2_0 (/ 6 1)) :named f3))
(assert (! (>= a_t0_1 0) :named f4))
(assert (! (>= a_t1_1 0) :named f5))
(assert (! (>= a_t2_1 0) :named f6))
(assert (! (>= a_t0_2 0) :named f7))
(assert (! (>= a_t1_2 0) :named f8))
(assert (! (>= a_t2_2 0) :named f9))
(assert (! (>= a_t0_3 0) :named f10))
(assert (! (>= a_t1_3 0) :named f11))
(assert (! (>= a_t2_3 0) :named f12))

;(assert (= a_t0_3 8))
;(assert (= a_t1_3 8))
;(assert (= a_t2_3 8))
(assert (! (= (+ a_t0_3 a_t1_3 a_t2_3) 24) :named a1))
;(assert (= (+ a_t0_3 a_t1_3 a_t2_3) 24))
;(assert (= (+ a_t0_3 a_t1_3 a_t2_3) 24))

;(assert (= (select (select users3 0) t0) 8))
;(assert (= (select (select users3 0) t1) 8))
;(assert (= (select (select users3 0) t2) 8))
;(assert (= 24 (totalBal (select users3 0))))

; amm assertions
(assert (! (= (/ 18 1) l_t0t1_0) :named amm1))
(assert (! (= (/ 8 1)  r_t0t1_0) :named amm2))
(assert (! (= (/ 18 1) l_t1t2_0) :named amm3))
(assert (! (= (/ 8 1)  r_t1t2_0) :named amm4))
(assert (! (= (/ 18 1) l_t2t0_0) :named amm5))
(assert (! (= (/ 8 1)  r_t2t0_0) :named amm6))

;txn assertions
(assert (! (> from_1 0) :named t1))
(assert (! (> from_2 0) :named t2))
(assert (! (> from_3 0) :named t3))
(assert (! (> to_1 0) :named t4))
(assert (! (> to_2 0) :named t5))
(assert (! (> to_3 0) :named t6))

(assert (! (= 
            payout_1
            (/ 
               (* from_1 l_t1t2_0)
               (+ from_1 r_t1t2_0))
        ) :named p1)
)
(assert (! (ite 
    (and (>= to_1 0) (<= to_1 payout_1))
    (and 
        (= l_t1t2_1 (- l_t1t2_0 payout_1))
        (= r_t1t2_1 (+ r_t1t2_0 from_1))
        (= a_t1_1 (+ a_t1_0 payout_1))
        (= a_t2_1 (- a_t2_0 from_1))
    )
    (and
        (= l_t1t2_1 l_t1t2_0 )
        (= r_t1t2_1 r_t1t2_0 )
        (= a_t1_1 a_t1_0 )
        (= a_t2_1 a_t2_0 )
    )
) :named c1))

(assert (! (= 
            payout_2
            (/ 
               (* from_2 l_t2t0_1)
               (+ from_2 r_t2t0_1))
        ) :named p2)
)
(assert (! (ite 
    (and (>= to_2 0) (<= to_2 payout_2))
    (and 
        (= l_t2t0_2 (- l_t2t0_1 payout_2))
        (= r_t2t0_2 (+ r_t2t0_1 from_2))
        (= a_t0_2 (- a_t0_1 from_2))
        (= a_t2_2 (+ a_t2_1 payout_2))
    )
    (and
        (= l_t2t0_2 l_t2t0_1 )
        (= r_t2t0_2 r_t2t0_1 )
        (= a_t0_2 a_t0_1 )
        (= a_t2_2 a_t2_1 )
    )
) :named c2))

(assert (! (= 
            payout_3
            (/ 
               (* from_3 l_t0t1_2)
               (+ from_3 r_t0t1_2))
        ) :named p3)
)
(assert (! (ite 
    (and (>= to_3 0) (<= to_3 payout_3))
    (and 
        (= l_t0t1_3 (- l_t0t1_2 payout_3))
        (= r_t0t1_3 (+ r_t0t1_2 from_3))
        (= a_t0_3 (+ a_t0_2 payout_3))
        (= a_t1_3 (- a_t1_2 from_3))
    )
    (and
        (= l_t0t1_3 l_t0t1_2 )
        (= r_t0t1_3 r_t0t1_2 )
        (= a_t1_3 a_t1_2 )
        (= a_t0_3 a_t0_2 )
    )
) :named c3))

; unchanged amms
(assert (! (= l_t2t0_1 l_t2t0_0) :named uc1))
(assert (! (= r_t2t0_1 r_t2t0_0) :named uc2))
(assert (! (= l_t0t1_1 l_t0t1_0) :named uc3))
(assert (! (= r_t0t1_1 r_t0t1_0) :named uc4))
                                            
(assert (! (= l_t1t2_2 l_t1t2_1) :named uc5))
(assert (! (= r_t1t2_2 r_t1t2_1) :named uc6))
(assert (! (= l_t0t1_2 l_t0t1_1) :named uc7))
(assert (! (= r_t0t1_2 r_t0t1_1) :named uc8))
                                            
(assert (! (= l_t2t0_3 l_t2t0_2) :named uc9))
(assert (! (= r_t2t0_3 r_t2t0_2) :named uc10))
(assert (! (= l_t1t2_3 l_t1t2_2) :named uc11))
(assert (! (= r_t1t2_3 r_t1t2_2) :named uc12))
                                            
; unchan(! ged user wals
(assert (! (= a_t0_1 a_t0_0) :named w1))
(assert (! (= a_t1_2 a_t1_1) :named w2))
(assert (! (= a_t2_3 a_t2_2) :named w3))


(check-sat)
(get-unsat-core)
;(get-value (from_1))
;(get-value (from_2))
;(get-value (from_3))
;(get-value (to_1))
;(get-value (to_2))
;(get-value (to_3))
;(get-value (payout_1))
;(get-value (payout_2))
;(get-value (payout_3))
;(get-value (a_t0_3))
;(get-value (a_t1_3))
;(get-value (a_t2_3))
