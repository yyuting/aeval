(declare-rel inv (Int Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)

(rule (=> (and (> j d) (> d 1)) (inv j d)))

; 2 refinements needed
; maybe AE-VAL's limitation

(rule (=> 
    (and 
        (inv j d)
        (>= j 0)
        (or
          (= j1 (/ j d))
          (= j1 (- j d))
        )
    )
    (inv j1 d)
  )
)