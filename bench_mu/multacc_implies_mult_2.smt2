;; r=mult x y implies r+a=multacc x y a
;; where mult and multacc are defined by:
;; mult x y = if y=0 then 0 else x+mult x (y-1)
;; multacc x y a = if y=0 then a else multacc x (y-1) (a+x) 

(declare-fun G (Int Int Int Int) Bool)
(declare-fun Mult (Int Int Int) Bool)
(declare-fun NegMultAcc (Int Int Int Int) Bool)
(declare-fun mu () Bool)
(declare-fun nu () Bool)

(assert (forall ((x Int) (y Int) (a Int) (r Int)) (G x y a r)))

(assert (forall ((x Int) (y Int) (a Int) (r Int))
  (= (G x y a r) (or (Mult x y r) (NegMultAcc x y a (+ r a))))))

(assert (and mu (forall ((x Int) (y Int) (r Int))
  (= (Mult x y r) (or
    (and (= y 0) (= r 0))
    (and (not (= y 0)) (Mult x (- y 1) (- r x))))))))

(assert (and nu (forall ((x Int) (y Int) (a Int) (r Int))
  (= (NegMultAcc x y a r) (and
    (or (not (= y 0)) (not (= r a)))
    (or (= y 0) (NegMultAcc x (- y 1) (+ a x) r)))))))

(check-sat)
