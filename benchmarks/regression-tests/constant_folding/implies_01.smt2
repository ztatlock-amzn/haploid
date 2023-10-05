(set-logic ALL)
(set-info :status unsat)
(assert (=> true false))
(check-sat)

;; EXPECTED: (set-logic ALL)
;; EXPECTED: (set-info :status unsat)
;; EXPECTED: (assert false)
;; EXPECTED: (check-sat)