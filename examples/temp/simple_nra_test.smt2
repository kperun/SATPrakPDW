(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert 
    (and
        (>= (* x y) 0)
        (< y 0)
    )
)
(set-info :status sat)
(check-sat)
(exit)
