(set-logic UFLIA)
(declare-fun x () Int)
(assert (<= (* x x) 0))
(assert (<= (* (- 2) (- 2)) 0))
(check-sat)
