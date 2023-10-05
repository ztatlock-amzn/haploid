(set-option :global-declarations true)
(set-logic QF_ALL)
(set-option :produce-unsat-cores true)
(set-option :produce-models true)
(declare-const _x0 RoundingMode)
(declare-const _x1 Real)
(declare-const _x2 RoundingMode)
(declare-const _x3 Real)
(declare-const _x4 RoundingMode)
(declare-const _x5 RoundingMode)
(define-sort _s0 (_y0 _y0) _y0)
(define-fun _f6 ((_f6_0 Real) (_f6_1 Real)) Real _f6_0)
(assert (let ((_let0 (- 8221201347535170910980613)))(= _let0 _let0)))
(assert (let ((_let0 (- 8221201347535170910980613)))(> _let0 _let0 _let0)))
(assert (< _x3 941036871671.320725391117308142))
(assert (= 8221201347535170910980613 8221201347535170910980613 _x3))
(assert (let ((_let0 (- 8221201347535170910980613)))(set.subset (set.complement (set.singleton _x3)) (set.singleton (ite (> _let0 _let0 _let0) (+ 8221201347535170910980613 941036871671.320725391117308142) _let0)))))
(check-sat)
(exit)