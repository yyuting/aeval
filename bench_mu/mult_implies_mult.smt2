;; (neg_mult x y r) \/ (mult x y r)

(declare-fun G (Int Int Int) Bool)
(declare-fun NegMult (Int Int Int) Bool)
(declare-fun Mult (Int Int Int) Bool)
(declare-fun mu () Bool)
(declare-fun nu () Bool)

(assert (forall ((x Int) (y Int) (r Int)) (G x y r)))

(assert (forall ((x Int) (y Int) (r Int))
  (= (G x y r) (or (NegMult x y r) (Mult x y r)))))

(assert (and nu (forall ((x Int) (y Int) (r Int))
  (= (NegMult x y r) (and
    (or (not (= y 0)) (not (= r 0)))
    (or (= y 0) (NegMult x (- y 1) (- r x))))))))

(assert (and mu (forall ((x Int) (y Int) (r Int))
  (= (Mult x y r) (or
    (and (= y 0) (= r 0))
    (and (not (= y 0)) (Mult x (- y 1) (- r x))))))))


(check-sat)
