(define required-env '())
(define get-dep-core
 (named-lambda self (body env)
  ;(write (list body env) current-error-port)(write-string "\n" current-error-port)
  (patmatch body
   (('begin y) (self y env))
   (('begin y . z) (self (cons 'begin z) (self y env)))
   (('lambda vars . newbody)
    (if (not (list? vars)) (set! vars (pair2list vars)) 'done)
    (self (cons 'begin newbody) (append vars env))
    env)
   (('define var val)
    (define env-new (cons var env))
    (self val env-new)
    env-new)
   (('set! var val) (self val env) env)
   ((the-macro . y) (guard (and (symbol-binded? the-macro) (macro? (eval the-macro)))) (self (macroexpand body) env))
   (('qoute x) env)
   (('cond . y) (self (expandcond y) env) env)
   ((and/or . y) (guard (isinlst and/or '(and or)))
    (self (expandandoror body) env) env)
   (x (guard (constant? x)) env)
   (('if e0 e1 e2)
    (define env-new (self e0 env))
    (self e1 env-new)
    (self e2 env-new)
    env-new)
   ((x . y)
    ;(write body current-error-port)(write-string "\n" current-error-port)
    (map (lambda (x) (self x env)) body)
    env)
   (x (guard (symbol? x))
    (cond 
     ((or (isinlst x env) (isinlst x required-env)) env)
     (else (set! required-env (cons x required-env)) env)))
   (x env))))
(define (get-dep-lambda prog init-required-env)
  (set! required-env init-required-env)
  (get-dep-lambda-core prog)
  required-env)
(define (get-dep-lambda-core prog)
  (define arg (args-of-lambda prog))
  (set! arg (if (not (list? arg)) (pair2list arg) arg))
  ;(write arg current-error-port) (newline current-error-port)
  (get-dep-core (cons 'begin (body-of-lambda prog)) arg))
(define (get-dep-lambda-rec prog var-bounded)
  ;(define build-in build-in-syms)
  (define init-env (complement (get-dep-lambda (eval prog) (cons prog var-bounded)) var-bounded))
  ;(write-string "init-env=" current-error-port) (write init-env current-error-port) (newline current-error-port)
  ;(write-string "var-bound=" current-error-port) (write var-bounded current-error-port) (newline current-error-port)
  (define (get-dep-lambda-rec-core-symbol sym-env)
    (cond
      ((null? sym-env) 'done)
   ((and (symbol? (car sym-env)) (symbol-binded? (car sym-env)) (not (isinlst (car sym-env) var-bounded)) (lambda? (eval (car sym-env))))
    (define prog (eval (car sym-env)))
    ;(write (car sym-env) current-error-port)
    (define additional-env (complement (get-dep-lambda prog (list (car sym-env))) init-env))
    ;(write additional-env current-error-port) (newline current-error-port)
    (define new-sym-env (append sym-env additional-env))
    (set! init-env (append init-env additional-env))
    (get-dep-lambda-rec-core-symbol (cdr new-sym-env)))
   (else (get-dep-lambda-rec-core-symbol (cdr sym-env)))))
 (get-dep-lambda-rec-core-symbol init-env)
 init-env)
(define (write-deps-core lst fp)
 (map
  (lambda (x)
   (cond
    ((symbol-binded? x)
     (define proc (eval x))
     (cond
      ((lambda? proc) (write `(define ,x (lambda ,(args-of-lambda proc) . ,(body-of-lambda proc))) fp))
      ((or (constant? proc) (pair? proc)) (write `(define ,x (,'quote ,proc)) fp))
      (else ""))
     (write-string "\n" fp))
    ((symbol-binded? x) (write `(define ,x (eval x)) fp) (write-string "\n" fp))
    (else 'done))) lst)
 'done)
(define (dump-deps lst str)
 (define fp (open-output-file str))
 (write-deps-core lst fp)
 (close-output-port fp))
(define (get-defs str)
 (define prs (optload-core str))
 (map cadr (cdr prs)))
(define runpass1 '(begin 
(optload "get_dep.ss")
(define general-sym '(not write-char))
(define pass1-ori-sym (append general-sym (get-defs  "general_compiler_defs.ss")))
(dump-deps (complement (get-dep-lambda-rec 'pass1 pass1-ori-sym) pass1-ori-sym) "pass1_opt_compile.ss")
(define testcpl (macroexpand-all (cons 'begin (append (cdr (optload-core "general_compiler_defs.ss")) (cdr (optload-core "pass1_opt_compile.ss")) (cdr (optload-core "pass1_opt_compile_eval.ss"))))))
(begin (define opf (open-output-file "testcpl.ss")) (write testcpl opf) (close-output-port opf))
 ;(system "cat testcpl.ss | ./pass1_cped > passed1.ss")
 (define passed1 (pass1 testcpl))
 ))
(defmacro loadsym (sym) `(define ,sym (cadr (optload-core ,(symbol->string (concat sym ".ss"))))))
(defmacro savesym (sym) `(let () (define opf (open-output-file ,(symbol->string (concat sym ".ss")))) (write ,sym opf) (close-output-port opf)))
(define (concat-string a b)
  (symbol->string (concat (string->symbol a) b)))
(define (dumppass-for-machine-code thepasssym . rst)
  (define general-def-file-name (if (null? rst) "general_compiler_defs_amd64.ss" (car rst)))
  (define general-sym '(not write-char))
  (define the-ori-sym (append general-sym (get-defs general-def-file-name)))
  (define theoptfile-name (symbol->string (concat thepasssym "_opt_compile.ss")))
  (dump-deps (complement (get-dep-lambda-rec thepasssym the-ori-sym) the-ori-sym) theoptfile-name)
  (define testcpl (macroexpand-all (cons 'begin (append (cdr (optload-core general-def-file-name)) (cdr (optload-core theoptfile-name)) `(,thepasssym)))))
  (savesym testcpl)
  (system "cat testcpl.ss | ./pass1_cped > passed1.ss")
  ;(loadsym passed1)
  testcpl
)
(define (dumppass thepasssym . rst)
  (define general-def-file-name (if (null? rst) "general_compiler_defs.ss" (car rst)))
  (define general-sym '(not write-char))
  (define the-ori-sym (append general-sym (get-defs general-def-file-name)))
  (define theoptfile-name (symbol->string (concat thepasssym "_opt_compile.ss")))
  (dump-deps (complement (get-dep-lambda-rec thepasssym the-ori-sym) the-ori-sym) theoptfile-name)
  (define testcpl (macroexpand-all (cons 'begin (append (cdr (optload-core general-def-file-name)) (cdr (optload-core theoptfile-name)) (list `(,thepasssym (read_from_stdin)))))))
  (savesym testcpl)
  (system "cat testcpl.ss | ./pass1_cped > passed1.ss")
  ;(loadsym passed1)
  testcpl
)
(define dbgprog '((lambda (y) ((lambda (z) ((lambda (x) (* (+ x y) z)) 5)) 6)) 7))
;(begin (set! outfp (open-output-file "pass1_cped.c")) (define cop current-output-port) (set! current-output-port outfp) (pass-generate-c befgenc) (close-output-port outfp) (set! current-output-port cop))
;(define testc1 '(begin (define (p6)  (define a0 1)  (define a3 p6)  (define (p7 a1)   (a1 a3))  (define (p8)   (p7 p6))  p8)  p6))
(define testcallcc
  '(letrec
    ((call/cc/k (lambda (f k) (f (lambda (resultincallcc dummy) (k resultincallcc)) k))))
     ((lambda (GEN1) (call/cc/k GEN1 (lambda (x) x))) (lambda (x GEN5) ((lambda (GEN9) (x GEN9 (lambda (GEN7) (GEN5 3)))) 2)))))
(define testyinyang_uncallcc
  '(begin
    (define call/cc/k (lambda (f k) (f (lambda (resultincallcc dummy) (k resultincallcc)) k)))
   (define (reverse l) (define (iter in out) (if (pair? in) (iter (cdr in) (cons (car in) out)) out)) (iter l '()))
    (define (cps-prim f)
     (lambda args
      (let ((r (reverse args)))
       ((car r) (apply f (reverse (cdr r)))))))
    (define write-char/k (cps-prim (lambda (a b) (write-char a b))))
    (define k (lambda (x) x))
    (let ((current-output-port (get-build-in-ports 1)))
    ((lambda (GEN54) ((lambda (GEN56) ((lambda (GEN57) (call/cc/k GEN57 (lambda (GEN55) (GEN56 GEN55 (lambda (GEN53) (GEN54 GEN53 k)))))) (lambda (c GEN60) (GEN60 c)))) (lambda (cc GEN65) ((lambda (GEN69) (write-char/k GEN69 current-output-port (lambda (GEN67) (GEN65 cc)))) #\@)))) (lambda (yin GEN72) ((lambda (GEN75) ((lambda (GEN77) ((lambda (GEN78) (call/cc/k GEN78 (lambda (GEN76) (GEN77 GEN76 (lambda (GEN74) (GEN75 GEN74 GEN72)))))) (lambda (c GEN81) (GEN81 c)))) (lambda (cc GEN86) ((lambda (GEN90) (write-char/k GEN90 current-output-port (lambda (GEN88) (GEN86 cc)))) #\*)))) (lambda (yang GEN93) ((lambda (GEN95) (yin GEN95 GEN93)) yang))))))))
	
(define dbgprog 
  '(begin
(define (map proc . items)
 (define (map-core proc items)
  (if (null? items) '() (cons (proc (car items)) (map-core proc (cdr items)))))
 (if (null? items)
  (internal-write-string "Error: unable to map zero arguments" (get-build-in-ports 2))
  (if (null? (car items)) '() 
   (cons (apply proc (map-core (lambda (x) (car x)) items)) (apply map (cons proc (map-core (lambda (x) (cdr x)) items)))))))
     
    (define f1 
      (lambda (y) 
	(define p1 
	  (lambda (z) 
	    ;(define g1 (lambda (x) (* (+ x y) z)))
	    (* (+ 4 y) z)))
	(map p1 (list 6 7))))
    (map f1 (list 7 8))))