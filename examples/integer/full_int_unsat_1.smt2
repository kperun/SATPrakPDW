(set-logic QF_LRA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert 
    (and
    	(< (+ (* a a) (* b b)) 1)
    	(> (* a b) 1)
    	(<= a 1000)
    	(>= a -1000)
    	(<= b 1000)
    	(>= b -1000)
    )
)
(check-sat)
(set-info :status unsat)
; unsat
(exit)
