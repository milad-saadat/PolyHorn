(declare-const c_0 Int)
(declare-const c_1 Int)
(declare-const c_2 Int)
(declare-const c_3 Int)
(assert (< c_0 0))
(assert (and (>= 1 0)))
(assert  (=> (and (>= 1 0)) (>= (* 1 c_1 ) 0) ))
(assert  (=> (and (>= 1 0)) (>= (* 1 c_2 ) 0) ))
(assert  (=> (and (>= 1 0)) (>= (* 1 c_3 ) 0) ))
(assert  (=> (and (>= (* 1 1) 0) (>= (* 1 c_1 ) 0) (>= (* 1 c_2 ) 0) (>= (* 1 c_3 ) 0) ) (>= (* 1 c_1 ) 0) ))
(assert  (=> (and (>= (* 1 1) 0) (>= (* 1 c_1 ) 0) (>= (* 1 c_2 ) 0) (>= (* 1 c_3 ) 0) ) (>= (* 1 c_2 ) 0) ))
(assert  (=> (and (>= (* 1 1) 0) (>= (* 1 c_1 ) 0) (>= (* 1 c_2 ) 0) (>= (* 1 c_3 ) 0) ) (>= (* 1 c_3 ) 0) ))
(assert  (=> (and (>= (* (- 2) 1) 0) (>= (* 1 c_1 ) 0) (>= (* 1 c_2 ) 0) (>= (* 1 c_3 ) 0) ) (>= (* 1 c_0 ) 0) ))
(check-sat)
(get-model)
