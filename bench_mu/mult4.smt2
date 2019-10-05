(declare-fun G (Int Int Int Int Int Int) Bool)
(declare-fun Dmult (Int Int Int) Bool)
(declare-fun Mult (Int Int Int) Bool)
(declare-fun mu () Bool)
(declare-fun nu () Bool)

(assert (forall ((x Int) (y Int) (v Int) (w Int) (z Int) (r Int)) (G x y v w z r)))

(assert (forall ((x Int) (y Int) (z Int) (v Int) (w Int) (r Int))
  (= (G x y v w z r) (or
    (Dmult (+ x y v w) z r)
    (exists ((s1 Int) (s2 Int) (s3 Int) (s4 Int)) (and (Mult x z s1) (Mult y z s2) (Mult v z s3) (Mult w z s4) (= r (+ s1 s2 s3 s4))))))))

(assert (and nu (forall ((x Int) (y Int) (r Int))
  (= (Dmult x y r) (and
    (or (not (= y 0)) (not (= r 0)))
    (or (= y 0) (Dmult x (- y 1) (- r x))))))))

(assert (and mu (forall ((x Int) (y Int) (r Int))
  (= (Mult x y r) (or
    (and (= y 0) (= r 0))
    (and (not (= y 0)) (Mult x (- y 1) (- r x))))))))

(check-sat)
