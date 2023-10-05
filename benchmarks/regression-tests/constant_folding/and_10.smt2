(set-logic ALL)
(set-info :status unsat)
(assert (and false false true))
(check-sat)

;; EXPECTED: (set-logic ALL)
;; EXPECTED: (set-info :status unsat)
;; EXPECTED: (assert false)
;; EXPECTED: (check-sat)