(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert 
    (and
        (>= (* x y) 0)
        (= (- (+ (* 2 y y y) (* -1 x x)) 5) 0)
        (<= y 0)
        (>= y -100.0)
        (<= x 100.0)
        (>= x -100.0)
    )
)
(check-sat)
; sat
(exit)
