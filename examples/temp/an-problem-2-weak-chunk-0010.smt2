(set-logic QF_NRA)

(declare-fun skoT () Real)
(assert (and (<= skoT 1000) (>= skoT (- 1000))))
(declare-fun skoB () Real)
(assert (and (<= skoB 1000) (>= skoB (- 1000))))
(declare-fun skoA () Real)
(assert (and (<= skoA 1000) (>= skoA (- 1000))))
(declare-fun skoS () Real)
(assert (and (<= skoS 1000) (>= skoS (- 1000))))
(assert (and (not (= (* skoT (* skoT (+ (+ (* skoA (* skoA (- 1.))) (* skoB (* skoB (- 1.)))) (* skoT (* skoT (- 1.)))))) (+ (* skoB (* skoB (* skoA skoA))) (* skoS (* skoS (- 1.)))))) (and (<= 0. skoS) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA)))))))
(set-info :status sat)
(check-sat)

