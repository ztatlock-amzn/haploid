(declare-const enumVariable Int)
(assert (= enumVariable 0))

; 0 -> foo, 1 -> bar
(assert (and (<= 0 enumVariable) (<= enumVariable 1)))
(check-sat)
(get-model)
