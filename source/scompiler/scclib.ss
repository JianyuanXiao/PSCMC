(define outfp current-output-port)
(defmacro write-def (name)
 `(begin
   (write-string "#define " outfp)
   (write (quote ,name) outfp)
   (write-string " " outfp)
   (write ,name)
   (write-string "\n")
 )
 )
(define (cat fp)
 (define l1 (read-line fp))
 (cond
  ((eof-object? l1) 'done)
  (else (write-string l1)(newline)(cat fp))))
;(define (convert-cc outfp infp)
 ;(define c-mode #f)
 ;(define (convert-cc-core)
  ;(define l1 (read-line infp))
;(define (convert-template-core str-list)
 ;(cond
  ;((null? str-list) ''done)
  ;(
(define (display-list-core lst-a)
 `(display ,lst-a outfp))
(defmacro display-list (lst)
    (cons 'begin (map display-list-core lst))
    )

(define beg_text "_PLAIN_TEXT")
(define end_text "_END_PLAIN_TEXT")
(define (convert-line l1) 
 (define l1-lst (string->list l1))
 (define final-ret '())
 ;(define l1-vec (list->vector l1-lst))
 (define (convert-line-core l1 current-parse mode) ;mode=plan scheme
  ;(write (list l1 current-parse mode)) (newline)
  (if (null? l1) (set! final-ret (cons (list->string (reverse current-parse)) final-ret))
   (begin 
  (define fstc (car l1))
  (cond
   ((eq? mode 'plan)
    (cond 
     ((eq? fstc #\`) 
      (cond 
       ((eq? (cadr l1) fstc) (convert-line-core (cddr l1) (cons fstc current-parse) mode))
       (else (set! final-ret (cons (list->string (reverse current-parse)) final-ret)) (convert-line-core (cdr l1) '() 'scheme))))
     (else (convert-line-core (cdr l1) (cons fstc current-parse) mode))))
   (else 
    (cond
     ((eq? fstc #\`)
      (set! final-ret (cons (list->string (reverse current-parse)) final-ret)) (convert-line-core (cdr l1) '() 'plan))
     (else (convert-line-core (cdr l1) (cons fstc current-parse) mode))))))))
 (convert-line-core l1-lst '() 'plan)
 ;(write 'final-ret=)
 ;(write final-ret)(newline)
 (reverse final-ret))

(define (plantext2list-write infp outfp)
 (define (write-or-write-string l1 wos)
  (cond
   ((null? l1) 'done)
   ((eq? wos 'w) (write (car l1) outfp) (write-string " " outfp) (write-or-write-string (cdr l1) 's))
   (else (write-string (car l1) outfp) (write-string " " outfp) (write-or-write-string (cdr l1) 'w))))
 (define (plantext2list-core)
  (define l1 (read-line infp))
  (cond
   ((eq? l1 end_text) 'done)
   (else 
    (write-string "(display-list (" outfp)
    (write-or-write-string (convert-line l1) 'w)
    (write-string " \"\\n\"))\n" outfp) 
    (plantext2list-core))))
 (write-string "(begin " outfp)
 (plantext2list-core)
 (write-string ")\n" outfp)
 )
(define (convert-final infp outfp)
 (define (convert-final-core)
  (define l1 (read-line infp))
  (cond
   ((eof-object? l1) 'done)
   ((eq? l1 beg_text) (plantext2list-write infp outfp) (convert-final-core))
   (else (write-string l1 outfp) 
     (write-string "\n" outfp) 
     (convert-final-core))))
 (convert-final-core))

