(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun R (Lst Int Int (Array Int Elem)) Bool)

(assert (forall ((n Int) (m Int) (A (Array Int Elem)))
    (= (R nil m n A) (= m n))))

(assert (forall ((xs Lst) (h Elem) (m Int) (n Int) (A (Array Int Elem)))
    (= (R (cons h xs) m n A)
    (and (< m n)
         (= h (select A (- n 1)))
         (R xs m (- n 1) A)))))

(assert (not (forall ((m Int) (n Int) (n1 Int) (xs Lst) (h Elem) (A (Array Int Elem)))
    (=> (and (>= n1 n) (R xs m n A)) (R xs m n (store A n1 h))))))

(check-sat)
