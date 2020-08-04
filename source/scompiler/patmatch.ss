(begin 
;(load "partial.ss")
(define (multi-bind? template patt) 
 (cond 
  ((pair? template)
   (cond 
    ((istag template 'quote) (equal? (cadr template) patt)); (multi-bind? (cdr template (cdr patt)))))
    ((pair? patt) (and (multi-bind? (car template) (car patt)) (multi-bind? (cdr template) (cdr patt))))
    (else #f)))
  ((symbol? template) #t)
  ((and (null? template) (null? patt)) #t)
  (else #f)))
(define (multi-bind-core-droped template patt) ;return an environment like list
 (cond 
  ((null? template) '())
  ((pair? template) (cons (multi-bind-core-droped (car patt) (car template)) (multi-bind-core-droped (cdr patt) (cdr template))))
  (else (cons (cons template patt) '()))))

(define (multi-bind-core-if template patt) ;return an environment like list
 ;(display patt)(newline)
 (if (null? template) '()
  (if (pair? template) 
   (if (istag template 'quote) '()
    (cons (multi-bind-core-if (car template) (car patt)) (multi-bind-core-if (cdr template) (cdr patt)))) 
   (cons (cons template (cons patt '())) '()))))

(define (multi-bind-core template patt) ;return an environment like list
 ;(display patt)(newline)
 (cond 
  ((null? template) '())
  ((istag template 'quote) '())
  ((pair? template) (cons (multi-bind-core (car template) (car patt)) (multi-bind-core (cdr template) (cdr patt))))
  (else (cons (cons template (cons patt '())) '()))))

(define (expand-multi-bind lst)
 ;(display lst)(newline)
 (cond 
  ((null? lst) '())
  ((pair? (car lst))
   (cond
    ((pair? (caar lst)) (append (expand-multi-bind (car lst)) (expand-multi-bind (cdr lst))))
    ((null? (caar lst)) (expand-multi-bind (cons (cdar lst) (cdr lst))))
    (else (cons (car lst) (expand-multi-bind (cdr lst))))))
  (else (expand-multi-bind (cdr lst)))))
    ;(else (expand-multi-bind (cdr lst)))))
(define (is-all-null? lst)
 (cond
  ((null? lst) #t)
  ((pair? lst) (and (is-all-null? (car lst)) (is-all-null? (cdr lst))))
  (else #f)))
  ;(else (let ((fst (expand-multi-bind (car lst)))) (cond ((null? fst) (expand-multi-bind (cdr lst))) (else (cons fst (expand-multi-bind (cdr lst)))))))))
(define (multi-bind template patt)
 (expand-multi-bind (multi-bind-core template patt)))

(define (build-multi-bind-exec-with-env fakeenv expr)
 (lcons 'let fakeenv expr))

(defmacro syntax-patmatch (patt . expr)
 (cond ((null? expr) (write "error in syntax-patmatch: empty last, no match found\n"))
  ((or (not (pair? expr)) (not (pair? (car expr)))) (write "error in patmatch: not pair\n"))
  ((multi-bind? (caar expr) patt) (build-multi-bind-exec-with-env (multi-bind (caar expr) patt) (cdar expr)))
  (else (syntax-patmatch patt (cdr expr)))))
(define fstevalbindcore
 `(define multi-bind-core-if ,(dump-lambda multi-bind-core-if)))

(defmacro patmatch (patt . expr)
 ;(display expr)(newline)
 (define tmp-patt-sym (gensym))
 (cond 
  ((null? expr) '(write-string "error in patmatch: no match found\n"))
  ((or (not (pair? expr)) (not (pair? (car expr)))) (write "error in patmatch: not pair\n"))
  (else 
   (define cdarexpr (cdar expr))
   (define guarded
    (cond 
     ((and (pair? (cadar expr)) (eq? (caadar expr) 'guard))
      (set! cdarexpr (cdr cdarexpr))
      `(patmatch ,tmp-patt-sym (,(caar expr) ,(cadr (cadar expr)))))
     (else #t)))
   (define myev (list 'begin fstevalbindcore `(multi-bind-core-if ,(cons 'quote (list (caar expr))) ,tmp-patt-sym)))
   ;(display guarded) (newline)
   ;(define evaled (build-multi-bind-exec-with-env (expand-multi-bind (eliminate-var-not-found (partial-eval-interface myev)))))
   ;(display evaled)(newline)(newline)
   `(let ((,tmp-patt-sym ,patt))
	   (cond 
	    ((and (multi-bind? (quote ,(caar expr)) ,tmp-patt-sym) ,guarded) ,(build-multi-bind-exec-with-env (expand-multi-bind (eliminate-var-not-found (partial-eval-interface myev))) cdarexpr))
	    (else (patmatch ,tmp-patt-sym . ,(cdr expr))))))))
)
