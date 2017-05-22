(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert 
    (and
    		(< x (* 2 y))
        (> y 2)
        (< y 4)
        (> x 1)
        (< x 3)
    )
)
(check-sat)
(exit)
