(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Elem)
(declare-fun out () Elem)
(declare-fun outb () Int)

(declare-fun num (Elem Lst) Int)
(assert (forall ((x Elem)) (= (num x nil) 0)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (num x (cons y xs)) (ite (= x y) (+ 1 (num x xs)) (num x xs)))))

(declare-fun removeall (Elem Lst) Lst)
(assert (forall ((x Elem)) (= (removeall x nil) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst))
  (= (removeall x (cons y xs)) (ite (= x y) (removeall x xs) (cons y (removeall x xs))))))

; extras

(assert (forall ((xs Lst) (a (Elem)) (b (Elem)))
  (=> (distinct a b) (= (num b (removeall a xs)) (num b xs)))))

(assert (forall ((s (Array Elem Int)) (a (Elem)) (b (Elem)))
  (=> (= (select s a) 0) (= (select (store s b 0) a) 0))))

(assert (forall ((s (Array Elem Int)) (a (Elem)) (b (Elem)))
  (=> (distinct a b) (= (select (store s a 0) b) (select s b)))))

(assert (forall ((s (Array Elem Int)) (a (Elem)) (b (Elem)) (c Int) (d Int))
  (=> (distinct a b) (= (store (store s a c) b d)  (store (store s b d) a c)))))

; init

(assert
  (= xs nil))

; num of elements

(assert
  (= outb (num in xs)))

; insert

(assert
  (= xs1 (cons in xs)))

; remove

(assert
  (= xs1 (removeall in xs)))
