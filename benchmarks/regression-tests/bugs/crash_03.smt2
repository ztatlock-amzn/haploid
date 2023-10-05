(set-logic QF_ALL)
(assert (= (as bag.empty(Bag (_ BitVec 64)) ) (as bag.empty(Bag (_ BitVec 64)) ) (as bag.empty(Bag (_ BitVec 64)) )))
(check-sat)
(exit)

;; EXPECTED: (set-logic QF_ALL)
;; EXPECTED: (assert (= (as bag.empty (Bag (_ BitVec 64))) (as bag.empty (Bag (_ BitVec 64)))))
;; EXPECTED: (check-sat)
;; EXPECTED: (exit)