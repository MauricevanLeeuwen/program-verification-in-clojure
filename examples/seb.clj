(fn
  [x :integer
   y :integer
   z :integer
   i :integer]
  
  {:requires (gte y 0)}

  
  (set! x 0)
  (set! i (mul 1 y))
  (while (gt i 0)
    {:invariant (and (eq (mul y 2) (add (mul i 2) x)) (gte i 0))
     :decreases (mul 1 i)}
    (set! i (sub i 1))
    (set! x (add x (mul 1 2)))
    )
  (assert (eq (mul 1 x) (mul 2 y)))
  )

