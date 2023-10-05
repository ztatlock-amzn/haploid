(set-logic ALL)
(declare-const __ (_ BitVec 1))
(assert (fp.isSubnormal ((_ to_fp 5 11) roundNearestTiesToAway ((_ zero_extend 10) __))))
(check-sat)
