(set-logic ALL)
(set-option :global-declarations true)
(set-option :produce-unsat-assumptions true)
(declare-const _x0 Real)
(declare-const _x1 Real)
(define-sort _s0 (_y0 _y1) _y0)
(define-fun _f2 ((_f2_0 (Seq Real)) (_f2_1 Real)) (Seq Real) (let ((_let0 (seq.unit _x1))) (let ((_let1 (seq.++ _f2_0 _let0 _let0))) (let ((_let2 (seq.replace_all _let1 _let1 _let0))) (let ((_let3 (seq.replace_all _let2 _let2 _let2))) (seq.replace_all (seq.++ _let3 _let3) _let1 _f2_0))))))
(define-sort _s1 (_y2 _y3) _y2)
(define-fun _f3 ((_f3_0 Bool) (_f3_1 Real)) Bool (let ((_let0 (/ 2089219607432745335649055758849047 _x1 2089219607432745335649055758849047 2089219607432745335649055758849047))) (let ((_let1 (is_int 2089219607432745335649055758849047))) (let ((_let2 (ite (= _x0 _x1 2089219607432745335649055758849047) _let1 _let1))) (let ((_let3 (_f2 (seq.unit _x1) _let0))) (let ((_let4 (ite (xor (seq.suffixof _let3 _let3) (or _f3_0 _let2 _let2 _let1 _let1)) 2089219607432745335649055758849047 _let0))) (xor (distinct _let3 _let3 _let3 _let3 _let3) (and (distinct _let4 _x1 _x1 _let4) (<= _let4 _f3_1) (not (< _f3_1 _f3_1))))))))))
(assert (= _x1 _x0))
(assert (= _x0 _x0))
(assert (= _x0 2089219607432745335649055758849047))
(assert (is_int 2089219607432745335649055758849047))
(assert (let ((_let0 (/ 2089219607432745335649055758849047 2089219607432745335649055758849047 2089219607432745335649055758849047 2089219607432745335649055758849047))) (let ((_let1 (> _let0 2089219607432745335649055758849047))) (let ((_let2 (_f2 (seq.unit 2089219607432745335649055758849047) _let0))) (let ((_let3 (is_int 2089219607432745335649055758849047))) (let ((_let4 true)) (let ((_let5 _let3)) (let ((_let6 (set.singleton _let5))) (let ((_let7 (and _let1 (and _let5 (and _let4 (distinct _let6 _let6 _let6)))))) (distinct (=> (_f3 _let7 2089219607432745335649055758849047) _let7) _let1 (seq.suffixof _let2 _let2) _let1))))))))))
(assert (let ((_let0 (/ 2089219607432745335649055758849047 2089219607432745335649055758849047 2089219607432745335649055758849047 2089219607432745335649055758849047))) (let ((_let1 (_f2 (seq.unit 2089219607432745335649055758849047) _let0))) (let ((_let2 (seq.suffixof _let1 _let1))) (let ((_let3 (> _let0 2089219607432745335649055758849047))) (let ((_let4 (is_int 2089219607432745335649055758849047))) (let ((_let5 true)) (let ((_let6 _let4)) (let ((_let7 (set.singleton _let6))) (let ((_let8 (and _let3 (and _let6 (and _let5 (distinct _let7 _let7 _let7)))))) (distinct (not (distinct (=> (_f3 _let8 2089219607432745335649055758849047) _let8) _let3 _let2 _let3)) (distinct _let1 _let1 _let1 _let1 _let1) _let2)))))))))))
(check-sat)
(exit)
