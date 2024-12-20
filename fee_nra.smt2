(set-logic QF_NRA)
(set-option :pp.decimal true)

( declare-const a_t0_0   Real)
( declare-const a_t1_0   Real)
( declare-const a_t2_0   Real)
( declare-const l_t0t1_0 Real)
( declare-const r_t0t1_0 Real)
( declare-const l_t1t2_0 Real)
( declare-const r_t1t2_0 Real)
( declare-const l_t2t0_0 Real)
( declare-const r_t2t0_0 Real)

( declare-const fee_t0t1 Real)
( declare-const fee_t1t2 Real)
( declare-const fee_t2t0 Real)

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

; fee assertions
( assert (= fee_t0t1 0))
( assert (= fee_t1t2 0))
( assert (= fee_t2t0 0))

; user assertions
(assert ( = a_t0_0 (/ 6 1)))
(assert ( = a_t1_0 (/ 6 1)))
(assert ( = a_t2_0 (/ 6 1)))
(assert (>= a_t0_1 0))
(assert (>= a_t1_1 0))
(assert (>= a_t2_1 0))
(assert (>= a_t0_2 0))
(assert (>= a_t1_2 0))
(assert (>= a_t2_2 0))
;(assert (>= a_t0_3 0))
;(assert (>= a_t1_3 0))
;(assert (>= a_t2_3 0))

(assert (= a_t0_3 8))
(assert (= a_t1_3 8))
(assert (= a_t2_3 8))

;(assert (= (select (select users3 0) t0) 8))
;(assert (= (select (select users3 0) t1) 8))
;(assert (= (select (select users3 0) t2) 8))
;(assert (= 24 (totalBal (select users3 0))))

; amm assertions
(assert (= (/ 18 1) l_t0t1_0))
(assert (= (/ 8 1)  r_t0t1_0))
(assert (= (/ 18 1) l_t1t2_0))
(assert (= (/ 8 1)  r_t1t2_0))
(assert (= (/ 18 1) l_t2t0_0))
(assert (= (/ 8 1)  r_t2t0_0))

;txn assertions
(assert (> from_1 0))
(assert (> from_2 0))
(assert (> from_3 0))
(assert (> to_1 0))
(assert (> to_2 0))
(assert (> to_3 0))

(assert (= 
            payout_1
            (/ 
               (* from_1 (- 1 fee_t1t2) l_t1t2_0)
               (+ (* from_1 (- 1 fee_t1t2)) r_t1t2_0))
        )
)
(assert (ite 
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
))

(assert (= 
            payout_2
            (/ 
               (* from_2 (- 1 fee_t2t0) l_t2t0_1)
               (+ (* from_2 (- 1 fee_t2t0)) r_t2t0_1))
        )
)
(assert (ite 
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
))

(assert (= 
            payout_3
            (/ 
               (* from_3 (- 1 fee_t0t1) l_t0t1_2)
               (+ (* from_3 (- 1 fee_t0t1)) r_t0t1_2))
        )
)
(assert (ite 
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
))

; unchanged amms
(assert (= l_t2t0_1 l_t2t0_0))
(assert (= r_t2t0_1 r_t2t0_0))
(assert (= l_t0t1_1 l_t0t1_0))
(assert (= r_t0t1_1 r_t0t1_0))

(assert (= l_t1t2_2 l_t1t2_1))
(assert (= r_t1t2_2 r_t1t2_1))
(assert (= l_t0t1_2 l_t0t1_1))
(assert (= r_t0t1_2 r_t0t1_1))

(assert (= l_t2t0_3 l_t2t0_2))
(assert (= r_t2t0_3 r_t2t0_2))
(assert (= l_t1t2_3 l_t1t2_2))
(assert (= r_t1t2_3 r_t1t2_2))

; unchanged user wals
(assert (= a_t0_1 a_t0_0))
(assert (= a_t1_2 a_t1_1))
(assert (= a_t2_3 a_t2_2))


(check-sat)
(get-value (from_1))
(get-value (from_2))
(get-value (from_3))
(get-value (to_1))
(get-value (to_2))
(get-value (to_3))
(get-value (payout_1))
(get-value (payout_2))
(get-value (payout_3))
(get-value (a_t0_3))
(get-value (a_t1_3))
(get-value (a_t2_3))
