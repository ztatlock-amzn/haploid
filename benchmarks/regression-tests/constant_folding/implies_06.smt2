(set-logic ALL)
(set-info :status sat)
(assert (=> true false true))
(check-sat)

;; EXPECTED: (set-logic ALL)
;; EXPECTED: (set-info :status sat)
;; EXPECTED: (check-sat)