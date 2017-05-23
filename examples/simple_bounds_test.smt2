(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert 
    (and
    	(> (* x x) 4)
    	(<= x 2)
    	(>= y -1000)
    	(<= y  1000)
    )
)
(check-sat)
; sat
(exit)
