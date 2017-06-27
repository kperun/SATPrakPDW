(set-logic QF_LRA)
(declare-fun x () Int) ; x = -1
(declare-fun y () Int) ; y = 2
(assert 
    (and
    	(<= (+ (* x x) x) 0)
    	(<= (- (* -1 y y y) y) -10)
    	(<= (+ x y) 2)
    	(<= x 10)
    	(>= x -10)
    	(<= y 10)
    	(>= y -10)
    )
)
(set-info :status sat)
(check-sat)
; sat
(exit)
