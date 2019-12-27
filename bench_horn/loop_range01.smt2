(declare-rel inv (Int))
(declare-var x Int)

(rule (=>
    true (inv x)
  )
)

(rule (=>
    (and
	(inv x)
        (>= x 0)
	(< x 10))

    (inv x)
  )
)
