(declare-const _a_0_ Real)
(declare-const _a_1_ Real)
(declare-const _a_2_ Real)
(declare-const _a_3_ Real)
(declare-const _a_4_ Real)
(declare-const _a_5_ Real)
(declare-const _a_6_ Real)
(declare-const _a_7_ Real)
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 a_0) (* -1. 1) ) 0)(>= (+ (* 1 err_0) (* 0 1) ) 0)) (and (>= (* 0.5 1)  0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 a_0) (* -1. 1) ) 0)(>= (+ (* 1 err_0) (* 0 1) ) 0)) (and (>= (+ (* 1 a_0) (* -1. 1) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 a_0) (* -1. 1) ) 0)(>= (+ (* 1 err_0) (* 0 1) ) 0)) (and (>= (+ (* 0 a_0) (* 0 1) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 a_0) (* -1. 1) ) 0)(>= (+ (* 1 err_0) (* 0 1) ) 0)) (and (>= (+ (* 0 1) (* 0 a_0) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 p_0) (* 0 1) ) 0)(>= (+ (* 1 r_0) (* 0 1) ) 0)(>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) (* -2. (* p_0 r_0)) ) 0)(>= (+ (* 1 (*  q_0   q_0  )) (* 2. (* p_0 r_0)) (* -1 a_0) ) 0)(>= (+ (* -2. (* p_0 r_0)) (* 1 err_0) ) 0)) (and (>= (+ (* 1 (*  q_0   q_0  )) (* -1 a_0) (* 1 err_0) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 p_0) (* 0 1) ) 0)(>= (+ (* 1 r_0) (* 0 1) ) 0)(>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) (* -2. (* p_0 r_0)) ) 0)(>= (+ (* 1 (*  q_0   q_0  )) (* 2. (* p_0 r_0)) (* -1 a_0) ) 0)(>= (+ (* -2. (* p_0 r_0)) (* 1 err_0) ) 0)) (and (>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 p_0) (* 0 1) ) 0)(>= (+ (* 1 r_0) (* 0 1) ) 0)(>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) (* -2. (* p_0 r_0)) ) 0)(>= (+ (* 1 (*  q_0   q_0  )) (* 2. (* p_0 r_0)) (* -1 a_0) ) 0)(>= (+ (* 2. (* p_0 r_0)) (* -1 err_0) ) 0)(>= (+ (* 2. r_0) (* -2. q_0) (* -1. p_0) (* 0 1) ) 0)) (and (>= (+ (* 0.5 p_0) (* 0 1) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 p_0) (* 0 1) ) 0)(>= (+ (* 1 r_0) (* 0 1) ) 0)(>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) (* -2. (* p_0 r_0)) ) 0)(>= (+ (* 1 (*  q_0   q_0  )) (* 2. (* p_0 r_0)) (* -1 a_0) ) 0)(>= (+ (* 2. (* p_0 r_0)) (* -1 err_0) ) 0)(>= (+ (* 2. r_0) (* -2. q_0) (* -1. p_0) (* 0 1) ) 0)) (and (>= (+ (* _a_0_ r_0) (* _a_1_ 1) (* _a_2_ q_0) (* _a_3_ p_0) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 p_0) (* 0 1) ) 0)(>= (+ (* 1 r_0) (* 0 1) ) 0)(>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) (* -2. (* p_0 r_0)) ) 0)(>= (+ (* 1 (*  q_0   q_0  )) (* 2. (* p_0 r_0)) (* -1 a_0) ) 0)(>= (+ (* 2. (* p_0 r_0)) (* -1 err_0) ) 0)(>= (+ (* 2. r_0) (* -2. q_0) (* -1. p_0) (* 0 1) ) 0)) (and (>= (+ (* 1 a_0) (* (+ -1 (* -1. _a_3_)) (*  p_0   p_0  )) (* (+ (* -2 _a_4_) (* -1. _a_1_)) p_0) (* (+ (* -2 _a_5_) (* -1. _a_2_)) (* p_0 q_0)) (* (* -1 (*  _a_4_   _a_4_  )) 1) (* (* -2 _a_4_ _a_5_) q_0) (* (* -1 (*  _a_5_   _a_5_  )) (*  q_0   q_0  )) (* (* -1. _a_0_) (* p_0 r_0)) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 p_0) (* 0 1) ) 0)(>= (+ (* 1 r_0) (* 0 1) ) 0)(>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) (* -2. (* p_0 r_0)) ) 0)(>= (+ (* 1 (*  q_0   q_0  )) (* 2. (* p_0 r_0)) (* -1 a_0) ) 0)(>= (+ (* 2. (* p_0 r_0)) (* -1 err_0) ) 0)(>= (+ (* 2. r_0) (* -2. q_0) (* -1. p_0) (* 0 1) ) 0)) (and (>= (+ (* (+ 1 (* 1. _a_3_)) (*  p_0   p_0  )) (* (+ (* 2 _a_4_) (* 1. _a_1_)) p_0) (* (+ (* 2 _a_5_) (* 1. _a_2_)) (* p_0 q_0)) (* (*  _a_4_   _a_4_  ) 1) (* (* 2 _a_4_ _a_5_) q_0) (* (*  _a_5_   _a_5_  ) (*  q_0   q_0  )) (* (* 1. _a_0_) (* p_0 r_0)) (* -1 a_0) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 p_0) (* 0 1) ) 0)(>= (+ (* 1 r_0) (* 0 1) ) 0)(>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) (* -2. (* p_0 r_0)) ) 0)(>= (+ (* 1 (*  q_0   q_0  )) (* 2. (* p_0 r_0)) (* -1 a_0) ) 0)(>= (+ (* 2. (* p_0 r_0)) (* -1 err_0) ) 0)(>= (+ (* -2. r_0) (* 2. q_0) (* 1. p_0) ) 0)) (and (>= (+ (* 0.5 p_0) (* 0 1) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 p_0) (* 0 1) ) 0)(>= (+ (* 1 r_0) (* 0 1) ) 0)(>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) (* -2. (* p_0 r_0)) ) 0)(>= (+ (* 1 (*  q_0   q_0  )) (* 2. (* p_0 r_0)) (* -1 a_0) ) 0)(>= (+ (* 2. (* p_0 r_0)) (* -1 err_0) ) 0)(>= (+ (* -2. r_0) (* 2. q_0) (* 1. p_0) ) 0)) (and (>= (+ (* _a_6_ r_0) (* _a_7_ 1) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 p_0) (* 0 1) ) 0)(>= (+ (* 1 r_0) (* 0 1) ) 0)(>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) (* -2. (* p_0 r_0)) ) 0)(>= (+ (* 1 (*  q_0   q_0  )) (* 2. (* p_0 r_0)) (* -1 a_0) ) 0)(>= (+ (* 2. (* p_0 r_0)) (* -1 err_0) ) 0)(>= (+ (* -2. r_0) (* 2. q_0) (* 1. p_0) ) 0)) (and (>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) (* (* -1. _a_6_) (* p_0 r_0)) (* (* -1. _a_7_) p_0) ) 0)))))
(assert (forall ((err_0 Real) (p_0 Real) (q_0 Real) (a_0 Real) (r_0 Real) ) (=> (and (>= (+ (* 1 p_0) (* 0 1) ) 0)(>= (+ (* 1 r_0) (* 0 1) ) 0)(>= (+ (* 1 a_0) (* -1 (*  q_0   q_0  )) (* -2. (* p_0 r_0)) ) 0)(>= (+ (* 1 (*  q_0   q_0  )) (* 2. (* p_0 r_0)) (* -1 a_0) ) 0)(>= (+ (* 2. (* p_0 r_0)) (* -1 err_0) ) 0)(>= (+ (* -2. r_0) (* 2. q_0) (* 1. p_0) ) 0)) (and (>= (+ (* 1 (*  q_0   q_0  )) (* (* 1. _a_6_) (* p_0 r_0)) (* (* 1. _a_7_) p_0) (* -1 a_0) ) 0)))))
(check-sat)
(get-model)
