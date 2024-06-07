(declare-const c Real)
(assert (forall ((x Real) (i Real)) (=> (> i x) (> (+ 0 i) x))))
(check-sat)
(get-model)
