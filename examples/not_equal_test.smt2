(set-logic QF_NRA)

(declare-fun x () Real)
(assert (and (<= x 1000) (>= x (- 1000))))
(declare-fun y () Real)
(assert (and (<= y 1000) (>= y (- 1000))))

(assert
	(and
		(!= x 0)
		(!= y 0)
	)
)

(set-info :status sat)
; model: x = 1, y = 1
(check-sat)

