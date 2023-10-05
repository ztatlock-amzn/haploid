(set-logic ALL)
(set-info :status sat)
(assert (or true))
(check-sat)

;; EXPECTED: (set-logic ALL)
;; EXPECTED: (set-info :status sat)
;; EXPECTED: (check-sat)