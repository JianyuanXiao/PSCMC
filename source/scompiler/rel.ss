(define (rel)
 (define v1 (read))
 (cond
  ((eof-object? v1) 'done)
  (else (eval (macroexpand-all v1)) (rel))))
;(rel)
(let loop ((r1 (read)))
  (cond
    ((eof-object? r1) 'done)
    (else (eval (macroexpand-all r1)) (loop (read)))
    )
  )

