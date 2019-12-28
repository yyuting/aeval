(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var len1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var len Int)

(declare-rel fail ())

(rule (=>
    (and (= x 0) (= len 1) (= y 0)) (inv x y len)
  )
)

(rule (=>
    (and
	(inv x y len)
        (< x len)
	(= len1 (- len 1))
  (= y1 (+ y 2))
    )
    (inv x y1 len1)
  )
)

(query fail :print-certificate true)
