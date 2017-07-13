(set-logic QF_NRA)

(declare-fun skoCOSS () Real)
(assert (and (<= skoCOSS 1000) (>= skoCOSS (- 1000))))
(declare-fun skoSINS () Real)
(assert (and (<= skoSINS 1000) (>= skoSINS (- 1000))))
(declare-fun pi () Real)
(assert (and (<= pi 1000) (>= pi (- 1000))))
(declare-fun skoS () Real)
(assert (and (<= skoS 1000) (>= skoS (- 1000))))
(assert (and (not (= (* skoSINS skoSINS) (+ 1. (* skoCOSS (* skoCOSS (- 1.)))))) (and (not (<= (* pi (/ 1. 2.)) skoS)) (and (not (<= pi (/ 15707963. 5000000.))) (not (<= (/ 31415927. 10000000.) pi))))))
(set-info :status sat)
(check-sat)

