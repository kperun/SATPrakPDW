(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert 
    (and
        (>= (* x y) 0)                         ; xy >= 0
        (= (- (+ (* 2 y y y) (* -1 x x)) 5) 0) ; 2y³ - x² = 5
        (<= y 0)
        (>= y -100.0)
        (<= x 100.0)
        (>= x -100.0)
    )
)
(set-info :status unsat)
(check-sat)
; unsat
(exit)
