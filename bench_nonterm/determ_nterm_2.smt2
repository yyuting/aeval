(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)
(declare-var y1 Int)

; requires --solver spacer

(rule (=> (and (= x -150) (= y 0)) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (not (= x 0))
        (= x1 (+ x y))
        (= y1 (+ y 1))
    )
    (inv x1 y1)
  )
)