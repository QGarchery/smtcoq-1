(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (= (f x) 3)))
(assert (not (= (f 2) 4)))
(check-sat)
(exit)