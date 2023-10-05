(declare-const x4 Bool)
(assert (exists ((x String)) (ite false (bag.subbag (bag (set.singleton false) (set.card (set.singleton false))) (bag (set.singleton false) (set.card (set.singleton false)))) (= x (str.at (str.replace_all x x "") (mod (set.card (set.singleton false)) (set.card (set.complement (set.insert false (set.singleton x4))))))))))
(check-sat)
