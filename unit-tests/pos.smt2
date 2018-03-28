(set-logic UFLIA)
(declare-fun n (Int) Int)
(assert (forall ((x Int)) (>= (n x) 0)))
(assert (not (< 0 (+ (n 2) 1))))
(check-sat)