(set-logic ALL)
(define-fun f ((_f2_1 Real) (_f2_0 (Seq Real))) Real _f2_1)
(declare-const x Real)
(assert (= x 0))
(assert (let ((_let1 (f 0.0 (seq.unit x)))) true))
(assert (let ((_let1 (f 0.0 (seq.unit 0)))) true))

