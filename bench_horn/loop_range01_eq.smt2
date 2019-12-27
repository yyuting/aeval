(declare-rel inv (Int))
(declare-var x Int)

(rule (=>
    true (inv x)
  )
)

(rule (=>
    (and
	(inv x)
  (xor (and (>= x 0)
           (< x 5))
      (and (>= x 5)
           (< x 10))
	   )
)

    (inv x)
  )
)
