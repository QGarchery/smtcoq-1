(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(assert (and (not (not (= a b))) (not (= a b))))
(check-sat)
(exit)
