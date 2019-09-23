(declare-sort Elem)

(declare-fun in () Elem)
(declare-fun out () Elem)
(declare-fun n () Int)
(declare-fun n1 () Int)
(declare-fun A () (Array Int Elem))
(declare-fun A1 () (Array Int Elem))

; isempty

(assert (= n 0))

; push

(assert
  (and
  (= A1 (store A n in))
  (= n1 (+ n 1))))

; pop

(assert
  (and
    (> n 0)
    (= n1 (- n 1))
    (= A1 A)
    (= out (select A (- n 1)))))

