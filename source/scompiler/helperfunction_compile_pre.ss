(define current-input-port (get-build-in-ports 0))
(define current-output-port (get-build-in-ports 1))
(define current-error-port (get-build-in-ports 2))
(define write-string (lambda arg (cond ((null? (cdr arg)) (internal-write-string (car arg) current-output-port)) (else (internal-write-string (car arg) (cadr arg))))))
(define newline (lambda arg (apply write-string (cons "\n" arg))))
(define read (lambda arg (cond ((null? arg) (read_element current-input-port)) (else (read_element (car arg))))))
(define i-read-line (lambda (fp) (call-ffi 5 fp)))
(define read-line (lambda arg (cond ((null? arg) (i-read-line current-input-port)) (else (i-read-line (car arg))))))
(define eof-object? (lambda (x) (= (get_type x) 523)))
(define write (lambda arg (cond ((null? (cdr arg)) (internal-write (car arg) current-output-port)) (else (internal-write (car arg) (cadr arg))))))
(define open-input-file (lambda (str) (open_input_file str)))
(define open-output-file (lambda (str) (open_output_file str)))
(define close-input-port (lambda (str) (close_port str)))
(define close-output-port close-input-port)
(define length (lambda (items) (define iter (lambda (a count) (if (null? a) count (iter (cdr a) (+ 1 count))))) (iter items 0)))
(define cadr (lambda (x) (car (cdr x))))
(define cadar (lambda (x) (car (cdr (car x)))))
(define caddr (lambda (x) (car (cdr (cdr x)))))
(define cadddr (lambda (x) (car (cdr (cdr (cdr x))))))
(define cddddr (lambda (x) (cdr (cdr (cdr (cdr x))))))
(define cdddr (lambda (x) (cdr (cdr (cdr x)))))

(define append-core (lambda (list1 list2) (if (null? list1) list2 (cons (car list1) (append-core (cdr list1) list2)))))
(define append (lambda lsts
 ;(display lsts)
 (if (null? lsts) '()
  (append-core (car lsts) (apply append (cdr lsts))))))

(define cdar (lambda (x) (cdr (car x))))
(define caar (lambda (x) (car (car x))))
(define caadr (lambda (x) (car (car (cdr x)))))
(define cddr (lambda (x) (cdr (cdr x))))
(define map (lambda (proc . items) (define map-core (lambda (proc items) (if (null? items) (quote ()) (cons (proc (car items)) (map-core proc (cdr items)))))) (if (null? items) (write-string "Error: unable to map zero arguments\n" current-error-port) (if (null? (car items)) (quote ()) (cons (apply proc (map-core (lambda (x) (car x)) items)) (apply map (cons proc (map-core (lambda (x) (cdr x)) items))))))))
(define pairlen (lambda (l) (define (iter a count) (if (not (pair? a)) (+ count 1) (iter (cdr a) (+ 1 count)))) (iter l 0)))
(define var-not-bound-sym 'VAR-NOT-BOUND)
(define outfp current-output-port)
(define display (lambda (m1 fp) (cond ((char? m1) (write-char m1 fp)) ((string? m1) (write-string m1 fp)) (else (write m1 fp)))))
(define vector 
  (lambda x 
    (define lenx (length x))
    (define retvec (make-vector lenx))
    (define (loop num lst)
      (cond
	((null? lst) 0)
	(else 
	  (vector-set! retvec num (car lst))
	  (loop (+ num 1) (cdr lst)))))
    (loop 0 x)
    retvec))

(define init-vector (lambda (num initvar)
  (define ret (make-vector num))
  (letrec
    ((loop 
       (lambda (n)
	 (cond
	   ((= n num) ret)
	   (else 
	     (vector-set! ret n initvar)
	     (loop (+ n 1)))))))
    (loop 0))))
  (define 
    remainder (lambda (m n)
    (call-ffi 1 (cons m n))))
  (define integer-floor 
    (lambda (x)
      (call-ffi 4 x)
      ))
  (define 
    (hash-string str)
    (call-ffi 0 str))
  (define hash-not-found var-not-bound-sym)
  (define (make-empyt-hash-table n)
    (define len n)
    (define current-load 0)
    (define thevec (init-vector len '()))
    (define self
    (lambda (flag)
      (cond
	((eq? flag 0) len)
	((eq? flag 1) thevec)
	((eq? flag 2) 
	 (lambda (str val)
           (define shouldbe (remainder (hash-string str) len))
	   (define thevarval (vector-ref thevec shouldbe))
	   (cond 
	    ((null? thevarval) (vector-set! thevec shouldbe (list (cons str val))))
	    (else
	     (letrec
	      ((loop 
		(lambda (lst)
		 (cond
		  ((eq? (caar lst) str) (set-cdr! (car lst) val))
		  ((null? (cdr lst)) (set-cdr! lst (list (cons str val))))
		  (else (loop (cdr lst)))))))
	      (loop thevarval))))))
	((eq? flag 3)
	 (lambda (str) 
	   (define shouldbe (remainder (hash-string str) len))
	   (define thevarval (vector-ref thevec shouldbe))
	    (letrec 
	     ((loop 
	       (lambda (lst) 
		(cond 
		 ((null? lst) hash-not-found)
		 ((eq? (caar lst) str) (cdar lst))
		 (else (loop (cdr lst)))))))
	     (loop thevarval))))
	((eq? flag 4)
	 (letrec
	   ((loop 
	      (lambda (n lst)
		(cond
		  ((eq? n len) lst)
		  (else (loop (+ n 1) (append (vector-ref thevec n) lst)))))))
	   (loop 0 '())))
	((eq? flag 'rehash-new)
	 (lambda (newlen)
	   (define newhashtable (make-empyt-hash-table newlen))
	   (map (lambda (varval) (hash-set! newhashtable (car varval) (cdr varval))) (dump-hash self))
	   newhashtable))
	((eq? flag 'rehash)
	 (lambda x
	   (define newlen
	     (if (null? x) (* len 4) (car x))) 
	   (define newhstb (rehash-new self newlen))
	   (set! len newlen)
	   (set! thevec (get-vector-hstb newhstb))))
	((eq? flag 'hash-set!)
	 (lambda (str val)
	   (if (< current-load (* len 0.75)) 
	     (hash-set!-unsafe self str val)
	     (begin
	       (rehash self)
	       (hash-set!-unsafe self str val)))))
	((eq? flag 5)
	 (lambda (str)
	  (define shouldbe (remainder (hash-string str) len))
	  (define thevarval (vector-ref thevec shouldbe))
	  (cond
	   ((and (pair? thevarval) (eq? (caar thevarval) str)) (vector-set! thevec shouldbe (cdr thevarval)))
	   ((null? thevarval) hash-not-found)
	   (else
	  (letrec
	   ((loop
	     (lambda (lst)
	      (cond
	       ((null? (cdr lst)) hash-not-found)
	       ((eq? (caadr lst) str) (set-cdr! lst (cddr lst)))
	       (else (loop (cdr lst)))))))
	   (loop thevarval))))))
	 )))
    self)
  (define remove-binding-in-single-env (lambda (str hstb)
   ((hstb 5) str)))
  (define (get-length-hstb hstb)
    (hstb 0))
  (define (get-vector-hstb hstb)
    (hstb 1))
  (define (hash-set! hstb str val) 
    ((hstb 'hash-set!) str val))
  (define (hash-set!-unsafe hstb str val) 
    ((hstb 2) str val))
   (define (hash-ref hstb str)
     ((hstb 3) str))
   (define (dump-hash hstb)
     (hstb 4))
   (define (rehash hstb . x)
     (apply (hstb 'rehash) x))
   (define (rehash-new hstb newlen)
     ((hstb 'rehash-new) newlen))
   (define define-element-to-single-env 
    (lambda (var val env)
     (hash-set! env var val)))

   ;(define (make-hash-table-from-lsts vars vals) (define hstbtmp (make-empyt-hash-table 2)) (map (lambda (x y) (hash-set! hstbtmp x y)) vars vals) hstbtmp)
(define fast-make-single-env-from-var-and-val (lambda (varsvals) 
  (define len 8) 
  (define hstbtmp (make-empyt-hash-table (* 2 len))) 
  (define (make-single-env-core varsvals) (cond ((null? varsvals) hstbtmp) (else (define varvalpair (car varsvals)) (hash-set! hstbtmp (car varvalpair) (cdr varvalpair)) (if (pair? varsvals) (make-single-env-core (cdr varsvals)) hstbtmp)))) 
  (make-single-env-core varsvals)))
(define fast-find-var-in-single-env (lambda (var env) (hash-ref env var)))
(define add-binding-in-single-env (lambda (varval env) (define-element-to-single-env (car varval) (cdr varval) env)))

(define copy-single-env (lambda (x) (rehash-new x (get-length-hstb x))))
(define copy-pair-structure 
 (lambda (x)
  (list (copy-single-env (car x)))))
(define merge-3-env 
 (lambda (e0env e1env e2env)
     ;(write (dump-hash e0env))
  (define theenv (make-empyt-hash-table 20))
  (define thelist (dump-hash e0env))
  (define (merge-3-env-core e0envlst e1env e2env)
   (cond 
    ((null? e0envlst) 
     theenv)
    (else 
     (define caare0 (caar e0envlst))
     (define fe1 (fast-find-var-in-single-env caare0 e1env))
     (define fe2 (fast-find-var-in-single-env caare0 e2env))
     (cond 
      ((equal? fe1 fe2) 
       (define-element-to-single-env caare0 fe1 theenv)
       (merge-3-env-core (cdr e0envlst) e1env e2env))
      (else (merge-3-env-core (cdr e0envlst) e1env e2env))))))
  (merge-3-env-core thelist e1env e2env)))
	

(define ivtmp 'inner_var_G0)
(define GLOBAL_PREFIX "")
(define gengensym (lambda  (prefix n)
 (lambda () 
  (set! n (+ n 1))
  (concat prefix (number->string n))
  )))

(define gensym (gengensym 'MYGEN 0))
(define mygensym gensym)

(define output_method 'C)
(define generate_mode 'device)
(define infile 0)

(define expandcond (lambda (cdrexpr)
 (cond 
  ((null? cdrexpr) #f)
  ((eq? (caar cdrexpr) 'else)
   (cond 
    ((null? (cdr cdrexpr)) (cons 'begin (cdar cdrexpr)))
    (else (display "else clause is not the last cond->if\n"))))
  (else (cons 'if (cons (car (car cdrexpr)) (cons (cons 'begin (cdr (car cdrexpr))) (cons (expandcond (cdr cdrexpr)) '()))))))))
(define expandandoror (lambda (expr)
 (let ((carexpr (car expr))(cdrexpr (cdr expr)))
  (cond 
   ((eq? carexpr 'and) 
    (cond 
     ((null? cdrexpr) #t)
     (else `(if ,(car cdrexpr) ,(cons 'and (cdr cdrexpr)) #f))))
   ((eq? carexpr 'or) 
    (cond 
     ((null? cdrexpr) #f)
     (else
      (let ((tmpsym (mygensym)))
      `(let ((,tmpsym ,(car cdrexpr))) (if ,tmpsym ,tmpsym ,(cons 'or (cdr cdrexpr))))))))))))
(define kernel_fun_prefix "")
(define device_fun_prefix "")
(define kernel_arg_prefix "")
(define g_idx  0)
(define g_idy  0)
(define g_xlen 0)
(define g_ylen 0)
(define g_global_idx 0)
(define const_arg_endfix 'Cpointer)
(define g_current_compute_unit_id 0)
(define g_num_compute_unit 0)
(define g_stupid_compile_mode 0)

(define pre_eval_global 
  (lambda () 
    (define global-argv (cdr (get-argv)))
    ;(write global-argv)
    (set! output_method (string->symbol (car global-argv)))
    (set! generate_mode (string->symbol (cadr global-argv)))
    ;(set! infile (open-input-file (caddr global-argv)))
    (set! GLOBAL_PREFIX (string->symbol (caddr global-argv)))
    (set! infile current-input-port)
    (cond
      ((and (pair? (cdddr global-argv )) (not (eq? (cadddr global-argv) "-")))
	(set! current-output-port (open-output-file (cadddr global-argv)))
	)
      (else 0)
      )
    (set! outfp current-output-port) 
    (cond
      ((eq? output_method 'CUDA) 
	(begin
	  (set! kernel_fun_prefix '__global__)
	  (set! device_fun_prefix '__device__)
	  (set! kernel_arg_prefix ""))
	(set! g_idx '(+ threadIdx.x (* threadIdx.y blockDim.x)))
	(set! g_idy '(+ blockIdx.x (* blockIdx.y gridDim.x)))
	(set! g_xlen '(* blockDim.x blockDim.y))
	(set! g_ylen '(* gridDim.x gridDim.y))
	(set! g_global_idx '(+ __idx (* __idy __xlen)))
	)
      ((eq? output_method 'OpenCL) 
	(set! kernel_fun_prefix '__kernel)
	(set! device_fun_prefix "")
	(set! kernel_arg_prefix '__global)
	(set! g_idx '(get_local_id 0))
	(set! g_idy '(get_group_id 0))
	(set! g_xlen '(get_local_size 0))
	(set! g_ylen '(get_num_groups 0))
	(set! g_global_idx '(+ __idx (* __idy __xlen))))
      ((eq? output_method 'SWMC)
	(set! g_idx 0)
	(set! g_idy 'swmc_idy) ;`(athread_get_id -1)
	(set! g_xlen 1)
	(set! g_ylen `scmc_internal_g_ylen)

	(set! g_global_idx '(+ __idx (* __idy __xlen)))
	)
      (else 
	(set! g_idx 0)
	(set! g_idy 'scmc_internal_g_idy)
	(set! g_xlen 1)
	(set! g_ylen 'scmc_internal_g_ylen)
	(set! g_global_idx '(+ __idx (* __idy __xlen)))
	))
   (cond 
      ((or (eq? output_method 'OpenCL) (eq? output_method 'CUDA))
	(set! g_current_compute_unit_id g_idy)
	(set! g_num_compute_unit g_ylen)
	)
      ((eq? output_method 'SWMC)
	(set! g_current_compute_unit_id `(athread_get_id -1))
	(set! g_num_compute_unit 64)
	)
      ((or (eq? output_method 'OpenMP) (eq? output_method 'COI))
	;(write output_method current-error-port)
	(set! g_current_compute_unit_id '(omp_get_thread_num))
	(set! g_num_compute_unit '(omp_get_num_threads))
	)
      (else
	(set! g_current_compute_unit_id 0)
	(set! g_num_compute_unit 1)
	;(write output_method current-error-port) (write (list g_current_compute_unit_id g_num_compute_unit) current-error-port) (newline current-error-port)
	)
      )
   ;(write-string "gscm=" current-error-port) (write g_stupid_compile_mode current-error-port ) (write-string "\n" current-error-port)
   )
)
(define g_use_icc_simd #t)

(define boolean-op-map-no-env '((or . "||") (not . "!") (and . "&&") (> . >) (< . <) (>= . >=) (+= . +=) (-= . -=) (*= . *=) (/= . /=) (<= . <=) (== . ==) (neq? . "!=") (eq? . "==")))
(define boolean-op-map (fast-make-single-env-from-var-and-val boolean-op-map-no-env))
(define integer-ops '((shift-l . "<<") (shift-r . ">>") (b-and . "&") (b-or . "|") (b-xor . "^") (b-not . "~") (remainder . "%")))
(define operator-booleans (map (lambda (x) (car x)) boolean-op-map-no-env))
(define operator-2s-no-env (append  '((+ .  +) (- . -) (* . *) (/ . /) (semicolon . ";")) integer-ops boolean-op-map-no-env))
(define operator-2s-lst (map (lambda (x) (car x)) operator-2s-no-env))
(define operator-2s (fast-make-single-env-from-var-and-val operator-2s-no-env))

(define simple-type-map 
  (fast-make-single-env-from-var-and-val 
    '((fixnum long) (float double) (string char*) (boolean int)))
)
(define varnotbound 'VAR-NOT-BOUND)

(define make_let_var_list 
 (lambda (paras input)
 (cond 
  ((null? input) (reverse paras))
  (else (make_let_var_list (cons (car (car input)) paras) (cdr input))))))
(define make_let_val_list 
 (lambda (paras input)
 (cond 
  ((null? input) (reverse paras))
  (else (make_let_val_list (cons (car (cdr (car input))) paras) (cdr input))))))
(define prim-macros '(let letrec))

(define expandlet 
 (lambda (input)
  (cons (cons 'lambda (cons (make_let_var_list '() (car input)) (cdr input))) (make_let_val_list '() (car input)))))
(define let_var_to_values_form 
 (lambda (lst)
 ;(display lst)(newline)
 (cond 
  ((null? lst) '(() ()))
  (else 
   (let ((transformed (let_var_to_values_form (cdr lst))))
    (list (cons (caar lst) (car transformed)) (cons (cadar lst) (cadr transformed))))))))

(define letrec-proc 
 (lambda (oldbidings varnames)
 (cond
  ((null? oldbidings) varnames)
  ((and (pair? (caar oldbidings)) (eq? (caaar oldbidings) 'DUMMY))
    (letrec-proc (cdr oldbidings) varnames)
    )
  (else (letrec-proc (cdr oldbidings) (cons (caar oldbidings) varnames)))
  )))
(define caaar (lambda (x) (car (car (car x)))))

(define expandletrec
 (lambda (prog) 
 (define binds (car prog))
 (define body (cdr prog))
 ;(display binds current-error-port)(newline current-error-port)
 (let ((vnames (letrec-proc binds '())))
   ;(display vnames current-error-port)(newline current-error-port)
   `(let ,(map (lambda (x) (list x 0)) vnames)
      ,(cons 'begin (append (map (lambda (y) (cond ((and (pair? (car y)) (eq? (caar y) 'DUMMY)) (cadr y)) (else (cons 'set! y)))) binds) body))))
 )) ; buggy here

(define expandlet* (lambda (binds . body)
 (cond 
  ((null? binds) (append '(let ()) body))
  (else (cons `(lambda (,(caar binds)) (let* ,(cdr binds) . ,body)) (cdar binds))))))

(define macroexpand
 (lambda (prog)
   ;(display prog current-error-port) (newline current-error-port)
  (cond
   ((eq? (car prog) 'let)
    (expandlet (cdr prog)))
   ((eq? (car prog) 'letrec)
    (expandletrec (cdr prog)))
   ((eq? (car prog) 'let*)
    (expandlet* (cdr prog)))
   (else prog))))

