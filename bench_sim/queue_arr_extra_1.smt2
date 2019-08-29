(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun allbutlast (Lst) Lst)
(assert (forall ((x Elem)) (= (allbutlast (cons x nil)) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (allbutlast (cons x (cons y xs))) (cons x (allbutlast (cons y xs))))))

(declare-fun last (Lst) Elem)
(assert (forall ((x Elem)) (= (last (cons x nil)) x)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (last (cons x (cons y xs))) (last (cons y xs)))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Elem) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(assert (not (forall ((xs Lst)) (=> (not (= xs nil)) (= xs (append (allbutlast xs) (cons (last xs) nil)))))))

(check-sat)
