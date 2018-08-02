(fn [x :integer
     y :integer]
  {}
  (set! x 4)
  (ite (gt x 3) (set! y 3) (set! y 0))
  (assert (eq y 3))
  )
