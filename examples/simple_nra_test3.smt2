(set-logic QF_LRA)
(declare-fun x () Real) ; x = 3
(declare-fun y () Real) ; y = -4
(assert 
    (and
    	(= (+ (* x x) (* y y)) 25)
    	(<= (* x y) -10)
    	(<= x 10)
    	(>= x -10)
    	(<= y 10)
    	(>= y -10)
    )
)
(check-sat)
; sat
(exit)
