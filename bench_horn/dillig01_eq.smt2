(declare-rel itp (Int Int))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(rule (=> (and (= x1 1) (= x3 1)) (itp x1 x3)
  )
)

(rule (=>
    (and
	(itp x1 x3)
	(= x2 (+ x1 x3))
	(= x4 x2)
    )
    (itp x2 x4)
  )
)
