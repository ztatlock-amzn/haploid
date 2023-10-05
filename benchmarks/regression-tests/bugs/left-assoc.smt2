(set-logic ALL)
(declare-const a String)
(assert (= a (str.++ "Hello" " " "world" "!")))
(check-sat)

;; EXPECTED: (set-logic ALL)
;; EXPECTED: (declare-const a String)
;; EXPECTED: (assert (= a "Hello world!"))
;; EXPECTED: (check-sat)