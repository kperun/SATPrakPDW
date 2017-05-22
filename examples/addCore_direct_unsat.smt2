(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert 
    (and
        (>= x -1000)
        (<= x  1000)
        (>= y -1000)
        (<= y  1000)
        (or (<= y 0) (>= x 2000))
    )
)
(check-sat)
; unsat
(exit)
