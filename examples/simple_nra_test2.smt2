(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert 
    (and
        (>= (* x y) 0)
        (< y 0)
        (= (- (+ (* 2 y y y) (* -1 x x)) 5) 0)
    )
)
(check-sat)
; unsat
(exit)
