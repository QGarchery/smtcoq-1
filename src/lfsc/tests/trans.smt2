(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)
(declare-fun e () U)
(declare-fun f () U)
(assert (and (= a b) (and (= b c) (and (= c d) (and (= c e) (and (= e f) (not (= a f))))))))
(check-sat)
(exit)
