(set-logic QF_NRA)

(declare-fun x () Real)
(assert (and (<= x 1000) (>= x (- 1000))))
(declare-fun y () Real)
(assert (and (<= y 1000) (>= y (- 1000))))

(assert
	(and
		(or (> (* x y) 1) (< (* x y) 1))
		(or (= (* x y) 1) (< (+ (* x x) (* y y)) 1))
	)
)

(set-info :status sat)
; model: x = 1, y = 1
(check-sat)

