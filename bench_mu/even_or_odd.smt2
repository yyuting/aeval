(declare-fun G (Int) Bool)
(declare-fun Even (Int) Bool)
(declare-fun Odd (Int) Bool)
(declare-fun mu () Bool)
(declare-fun nu () Bool)

(assert (forall ((x Int)) (G x)))

(assert (forall ((x Int))
  (= (G x) (or (< x 0) (Even x) (Odd x)))))

(assert (and mu (forall ((x Int))
  (= (Even x) (or (= x 0) (Odd (- x 1)))))))

(assert (and mu (forall ((x Int))
  (= (Odd x) (Even (- x 1))))))

(check-sat)
