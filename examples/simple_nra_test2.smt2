(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert 
    (and
        (>= (* x y) 0)
        (< y 0)
        (= (+ (* y y y) (* x x)) 0)
    )
)
(check-sat)
; unsat
(exit)
