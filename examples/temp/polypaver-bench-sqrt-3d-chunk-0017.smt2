(set-logic QF_NRA)

(declare-fun skoX () Real)
(assert (and (<= skoX 1000) (>= skoX (- 1000))))
(declare-fun skoY () Real)
(assert (and (<= skoY 1000) (>= skoY (- 1000))))
(declare-fun skoZ () Real)
(assert (and (<= skoZ 1000) (>= skoZ (- 1000))))
(assert (not (<= (* skoZ (* skoY (* skoX (- 1.)))) 0.)))
(set-info :status sat)
(check-sat)

