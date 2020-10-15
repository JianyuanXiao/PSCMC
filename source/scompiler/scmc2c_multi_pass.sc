;(define output_method 'OpenMP) ;can be C, OpenMP, OpenCL, CUDA or COI
;The __global_idx is the id inside the thread block, currently two dimensional block is supported for CUDA, one dimensional block for OpenCL
;The global_idy is the id of the thread block
;use (defkernel name ((type0 arg0) (type1 arg1) ...) . body) to define the compute kernel
;use (defun name rettype ((type0 arg0) (type1 arg1) ...) . body) to define the function can be called by compute kernels
;include- = include "", include< = include <>
;use (type-convert totype arg) to generate ((totype)(arg))
;
(optload "pass1_remove_nonregdefs.ss")
(define kernel_fun_prefix "")
(define device_fun_prefix "")
(define kernel_arg_prefix "")
(define g_idx  0)
(define g_idy  0)
(define g_xlen 0)
(define g_ylen 0)
(define g_num_compute_unit 0)
(define g_current_compute_unit_id 0)
(define g_global_idx 0)

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
   (set! g_current_compute_unit_id g_idy)
   (set! g_num_compute_unit g_ylen)
)
 ((eq? output_method 'OpenCL) 
   (set! kernel_fun_prefix '__kernel)
   (set! device_fun_prefix "")
   (set! kernel_arg_prefix '__global)
   (set! g_idx '(get_local_id 0))
   (set! g_idy '(get_group_id 0))
   (set! g_xlen '(get_local_size 0))
   (set! g_ylen '(get_num_groups 0))
   (set! g_global_idx '(+ __idx (* __idy __xlen)))
   (set! g_current_compute_unit_id g_idy)
   (set! g_num_compute_unit g_ylen))
 (else 
   (set! g_idx 0)
   (set! g_idy '(omp_get_thread_num))
   (set! g_xlen 1)
   (set! g_ylen '(omp_get_num_threads))
   (set! g_global_idx '(+ __idx (* __idy __xlen)))
   (set! g_current_compute_unit_id g_idy)
   (set! g_num_compute_unit g_ylen)
)
)
 
  
(define (to-string arg)
 (if (string? arg) arg (symbol->string arg))
)
(define varnotbound 'VAR-NOT-BOUND)
(define (find-var-in-multi-env var envs)
  (cond
    ((null? envs) 'VAR-NOT-BOUND)
    (else (define var1 (fast-find-var-in-single-env var (car envs)))
      (if (eq? var1 'VAR-NOT-BOUND) (find-var-in-multi-env var (cdr envs)) var1)
)
)
)

(define (type-or-not arg)
 (cond
   ((pair? arg) (apply multi-concat (map (lambda (x) (concat " " (extra-complex-type x))) arg)))
   (else  (to-string arg))
)
)
(define (genarglst arglst)
  (cond
    ((null? arglst) "")
    ((null? (cdr arglst)) (car arglst))
    (else (multi-concat (car arglst) "," (genarglst (cdr arglst))))
)
)
(defmacro read-infile ()
 '(read infile) 
)
;(define infile (open-input-file "test1.c.ss"))
;(set! (current-input-port infile))
(defmacro ifconte ()
'(if (eq? cont 'e) (write-string ";\n") ""))
(define (error-h str opt . e)
  (write-string str current-error-port)
  (write opt current-error-port)
  (write-string "\n" current-error-port)
  (if (null? e) 0
  (car 0) )
)
(define macros-interp '(0))
(define (read-all infile)
 (let loop ((l1 (read-infile)) (curlst '()))
   (cond ((eof-object? l1) (set! macros-interp (cons 'begin (reverse macros-interp))) (cons 'begin (reverse curlst)))
     ((eq? (car l1) 'defmacro) (set! macros-interp (cons l1 macros-interp)) (loop (read-infile) curlst)) 
  (else (loop (read-infile) (cons l1 curlst))))
)
)
(defmacro find-type-current (type)
  `(find-type ,type env)
)
(define mathe-funs '(sin cos tan asin acos atan sqrt cbrt erf erfc fabs j0 j1 exp sinh cosh tanh asinh acosh atanh y0 y1 expm1 exp2 floor ceil log log10 pow atan2 floor))
(define stdio-funs '(printf fprintf sprintf snprintf vprintf vfprintf vsprintf vsnprintf scanf fscanf sscanf vscanf vsscanf vfscanf bcmp memcmp strcmp strncmp fclose fflush))
(define file-funs '(fopen fdopen freopen))
(define mallocfuns '(calloc malloc realloc alloca memcpy))
(define init-env-lst (append (map (lambda (x) (cons x '(double))) mathe-funs) (map (lambda (x) (cons x '(int))) stdio-funs) (map (lambda (x) (cons x '(void*) )) mallocfuns) (map (lambda (x) (cons x '(FILE*))) file-funs)))
(define str-funs '(strstr strcasestr strcpy strncpy))
(define const_arg_endfix 'Cpointer)
(define (add-empty-env-layer env . add?)
  (if (and  (pair? add?) (car add?)) (cons (fast-make-single-env-from-var-and-val '()) env) env)
)

(define (isvectp? x) (eq? (car (reverse (string->list (if (symbol? x) (symbol->string x) x)))) #\*))

(define (write-typelist tplst)
  (let loop ((tplst tplst))
    (cond
      ((null? tplst) "")
      ((or (eq? (car tplst) 'scalar) (eq? (car tplst) "scalar")) (loop (cdr tplst)))
      ((string? (car tplst)) (write-string tplst) (write-string " ") (loop (cdr tplst)))
      (else (write (car tplst)) (write-string " ") (loop (cdr tplst)))
)
)
)
(define (map-write-comma fun arg)
  (let loop ((arg arg))
    (cond
      ((null? arg) "")
      ((null? (cdr arg)) (fun (car arg)))
      (else (fun (car arg)) (write-string ",") (loop (cdr arg)))
)
)
)
(define (write-var-typelist vtplst)
  (write-typelist (car vtplst)) (write-string " ")
  (write-typelist (list (cadr vtplst)))
)
(defmacro write-sqr-parentheses (wrt)
`(begin (write-string "[") ,wrt (write-string "]"))
)
(defmacro write-parentheses (wrt)
`(begin (write-string "(") ,wrt (write-string ")"))
)
(defmacro write-brackets (wrt)
`(begin (write-string "{\n") ,wrt (write-string "}"))
)
(define (fin-shell d1)
  (define functiondefs '())
  (define kernelfunctions '())
  (pre_eval_global )

 (if (eq? output_method 'OpenCL) (write-string "#pragma OPENCL EXTENSION cl_khr_fp64: enable\n") 0)
 (if (eq? output_method 'OpenMP) (write-string "#include <omp.h> \n#include <math.h>\n") 0)
 (if (eq? output_method 'COI) 
  (write-string 
"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <unistd.h>
#include <math.h>
#include <string.h>
#include <omp.h>
#include <intel-coi/sink/COIPipeline_sink.h>
#include <intel-coi/sink/COIProcess_sink.h>
#include <intel-coi/common/COIMacros_common.h>
#include <intel-coi/common/COISysInfo_common.h>
#include <intel-coi/common/COIEvent_common.h>
#include \"local_header.h\"
") 0)
 (if (eq? output_method 'SWMC) (write-string "#include \"slave.h\"\n") 0)
 ;(if (eq? output_method 'C) (write-string "\n#include <math.h>\n") 0)
   (let self ((l1 (readport infile)) (cont 'e))
	;(write l1 current-error-port) (newline)
      (patmatch l1 
      ((include str) (guard (isinlst include '(include< include-)))
	(define bondl (if (eq? include 'include-) "\"" "<"))
	(define bondr (if (eq? include 'include-) "\"" ">"))
	(cond
	  ((or (string? str) (symbol? str)) 
_PLAIN_TEXT
#include `bondl``str``bondr`

_END_PLAIN_TEXT
)
	  (else (error-h "Invalid program: " l1 0))
)
)
      (('typedef-struct name . decs)
_PLAIN_TEXT
typedef struct { 
_END_PLAIN_TEXT
         (map (lambda (x) (self x 'e)) decs)
_PLAIN_TEXT
} `name`;
_END_PLAIN_TEXT
	)
      (('sizeof-var var) (write 'sizeof) (write-parentheses (self var 'v)) (ifconte))
      (('sizeof type) (write 'sizeof) (write-parentheses (write-typelist type)) (ifconte))
      ;(('find-type arg) (find-type arg env))
      (('pure-text arg) (if (symbol? arg) (write arg) (write-string arg)))
      ;(var (guard (eq? var ivtmp)) (self 0 cont))
      ((defun-or-declare name rettype arglst . body) (guard (isinlst defun-or-declare '(defun dec-fun)))
	;(write name current-error-port) (write "\n" current-error-port)
	(define isdeclare (eq? defun-or-declare 'dec-fun))
	(write-var-typelist (list rettype name))
	(write-parentheses (map-write-comma write-var-typelist arglst))
	(if isdeclare (write-string ";") (self (cons 'block body) 'e))
	(write-string "\n") ""
)

      (('semicolon . y) (self `(begin . ,y) cont))
      (('begin) "")
      (('begin x) (self x cont))
      (('type-convert newtype expr)
	(write-parentheses (begin (write-parentheses (write-typelist newtype)) (self expr cont)))
""
)
      (('block x) 
        (cond
	  ((eq? 'e cont) (write-brackets (self x 'e)))
  	  ((isinlst cont '(p v)) (self `(cblock ,x) cont))) 
	"")
      (('pow x n) (guard (and #t (isinlst output_method '(CUDA OpenCL HIP)) (number? n) (eq? (floor n) n)))
	(if (fixnum? n) 0 (set! n (integer-floor n)))
	;(write x current-error-port) (write n current-error-port) (newline current-error-port)
	(if (< n 0) (self `(/ 1.0 (pow ,x ,(- n))) cont)
	 (if (eq? output_method 'CUDA)
	  (self 
	   `(block 
		   (begin
		    (declare (double) (tmppowvar ,x ))
		    ,(let loop ((n n))
			    (cond
			     ((eq? n 0) 1)
			     ((eq? n 1) 'tmppowvar)
			     (else `(* tmppowvar ,(loop (- n 1))))
			    )
		     ))) cont)
	  (self (let loop ((n n))
		 (cond
		  ((eq? n 0) 1)
		  ((eq? n 1) x)
		  (else `(* ,x ,(loop (- n 1))))
		 )
		) cont)
	 ))
	  ;(cond ((< n 0) `(/ 1.0 ,(self `(pow ,x ,(- n)) cont))) ((eq? n 1) (self x cont)) (else (self `(* ,x (pow ,x ,(- n 1))) cont)))
)
      (('cblock x) (write-parentheses (write-brackets (self x 'e))) "")
      ;(('block . y) (self `(block (begin . ,y)) 'e) "")
      (('begin x . y) (self x 'e) (self `(begin . ,y) cont))
      (('dec-fun0 ret paratps name)
	(write-typelist ret)
	(write-parentheses (write-typelist (list '* name)))
	(write-parentheses (map-write-comma write-typelist paratps))
	(ifconte)
)
      (('declare type (name initl ))
	;(if (eq? name 'blas_dot_kernel) (begin (write (list name type) current-error-port) (write-string "\n" current-error-port)) 0)
_PLAIN_TEXT
	`(write-typelist type)` `name` = `(self initl 'v) ` ;

_END_PLAIN_TEXT
)
      (('typedef type newname)
_PLAIN_TEXT
typedef `(write-typelist type) ` `newname` ;

_END_PLAIN_TEXT
)
      ;(('declare ('find-type name) . a) (write name current-error-port) (newline current-error-port) (write (find-type-current name) current-error-port) (newline current-error-port) (self `(declare ,(find-type-current name) . ,a) x))

      (('declare type name)
_PLAIN_TEXT
	`(write-typelist type)` `name` ;

_END_PLAIN_TEXT
)
      ;(('dec-array-pointer type name . lenxs))
      ;(('dec-array ('find-type name) . y) (write name current-error-port) (newline current-error-port) (write (find-type-current name) current-error-port) (newline current-error-port) (self `(dec-array ,(find-type-current name) . ,y) x))
      (('dec-array type name . lenxs) 
	(define algn (car type))
	(if (number? algn) (begin (set! algn (multi-concat "__attribute__((aligned(" (number->string algn) ")))")) (set! type (cdr type ))) (set! algn ""))
	(define star-prfix "")
	(define star-lsfix "")
	(if (eq? (car type) 'c-pointer)
	   (begin
	     (set! star-prfix "(*")
	     (set! star-lsfix ")")
	     (set! type (cdr type))
) 
	0
	)
_PLAIN_TEXT
	`(write-typelist type)` `star-prfix` `name` `star-lsfix` ` (begin (map (lambda (x) (write-sqr-parentheses (self x))) lenxs) "") ``algn`;
_END_PLAIN_TEXT
)
      (('vector-set! x n y) (self `(set! (vector-ref ,x ,n) ,y) cont))
      (('force-v-set! x y) (self `(set! ,x ,y) cont))
      (('force-scalar-ver x) (self x cont))
      (('force-simd-ver ('inner-simd-comp n) . y) (self `(begin . ,y) cont))
      (('force-simd-ver . y) (self `(begin . ,y) cont))
      (('IS_IN_VEC_LOOP) (self 0 cont))
      (('set! x y) 
	;(write x current-error-port) (write-string "\n" current-error-port)
       (define new-expr ;this can only eliminate some stupid blocks
	(if (eq? output_method 'OpenCL)
	 (begin
	  (multi-define retpreblock new-expr (pass-remove-blocks-returns-for-stupid-opencl-compilers y))
	  (if (not (null? retpreblock))
	   (self `(begin . ,retpreblock) 'e) 0
	  )
	  new-expr
	 ) y))
       (write-string "(") (self x 'v) (write-string " = ") (self new-expr 'v) (write-string ")") (ifconte))
      (('vector-ref x n) (write-string "(") (self x 'v) (write-string ")[") (self n 'v) (write-string "]") (ifconte))
      (('continue) (write-string "continue;\n"))
      (('label l1) 
_PLAIN_TEXT
	`l1`:

_END_PLAIN_TEXT
)
      (('goto l1)
_PLAIN_TEXT
	goto `(self l1 'v) `;
_END_PLAIN_TEXT
)
      (('inner-for-from-to var from to body)
	(self `(block (begin (declare (long) ,var) (for (set! ,var ,from) (< ,var ,to) (set! ,var (+ ,var 1)) ,body))) cont)
)
      (('for e0 p0 plusplus body)
_PLAIN_TEXT
	for (`(self e0 'v)` ; `(self p0 'p)` ; `(self plusplus 'v)`)
	`(begin (self body 'e) "") `
_END_PLAIN_TEXT
)
      (('reduce op var) (self var cont))
      (('struct-ref str name)
_PLAIN_TEXT
	( `(begin (self str 'v) "")` ).`name`
_END_PLAIN_TEXT
	(ifconte)
)
      (('structp-ref str name)
_PLAIN_TEXT
	( `(begin (self str 'v))` )->`name`
_END_PLAIN_TEXT
	(ifconte)
)
      ;(('get-pointer arg) (display-list ("&(")) (self arg env 'e))
      (('if p e1 e2) (guard (isinlst cont '(p v)))
	(write-string "((")
	(self p 'p)
	(write-string ")?(")
	(self e1 cont)
	(write-string "):(")
	(self e2 cont)
	(write-string "))")
	(ifconte)
)
      ((ifexp p e1 e2) (guard (isinlst ifexp '(if ifmacro ifdefmacro ifndefmacro)))
	(define ifpfx "if (")
	(define ifrlst "){")
	(define ifelse "}else{")
	(define ifendif "}")
	(define useblock #f)
	(case ifexp
	  ('ifmacro (set! ifpfx "#if ") (set! ifrlst "") (set! ifelse "#else") (set! ifendif "#endif"))
	  ('ifdefmacro (set! ifpfx "#ifdef ") (set! ifrlst "") (set! ifelse "#else") (set! ifendif "#endif"))
	  ('ifndefmacro (set! ifpfx "#ifndef ") (set! ifrlst "") (set! ifelse "#else") (set! ifendif "#endif"))
	  ('if (set! useblock #t))
	  (else 0))
_PLAIN_TEXT
	`ifpfx `  `(self p 'p)`  `ifrlst`  
		`(begin (self e1 cont) "") `
	`ifelse`
		`(begin (self e2 cont) "") `
	 `ifendif`

_END_PLAIN_TEXT
)
      (('extern str . prog) (guard (string? str))
_PLAIN_TEXT
extern "`str`" { 
	`(begin (self (cons 'begin prog) 'e) "") `
}

_END_PLAIN_TEXT
)
      (('extern type arg)
_PLAIN_TEXT
extern `(write-typelist type)` `arg`;
_END_PLAIN_TEXT
)
      (('condmacro ('else . cl)) (self `(cond (else . ,cl)) cont))
      (('condmacro (p1 . cl) . y) (self `(ifmacro ,p1 ,(cons 'begin cl) (condmacro . ,y)) cont))
      (('conddefmacro (p1 . cl) . y) (self `(ifdefmacro ,p1 ,(cons 'begin cl) (conddefmacro . ,y)) cont))
      (('condndefmacro (p1 . cl) . y) (self `(ifndefmacro ,p1 ,(cons 'begin cl) (condndefmacro . ,y)) cont))
      (('cond ) (self 0 cont))
      (('cond ('else . cl)) (self (cons 'begin cl) cont))
      (('cond (p1 . cl) . y) (self `(if ,p1 ,(cons 'begin cl) (cond . ,y)) cont))
      ((condexp . g) (guard (isinlst condexp '(cond condmacro conddefmacro condndefmacro))) (error-h "Error: Invalid cond: " l1 0))
      (('const-string . y) (map (lambda (x) (write x) (write-string "\n")) y) (ifconte))
      (('const-string-from-file filename)
	(write filename current-error-port) (newline current-error-port)
	(define fp (open-input-file filename))
	;(ifconte)
	(let loop 
	  ((l1 (read-line fp)))
	    ;(write l1 current-error-port) (newline current-error-port)
	    (if (eof-object? l1) 
	      (begin 
		(close-input-port fp) 
		(ifconte)) 
	      (begin 
		(write l1) 
		(write-string "\n") 
		(loop (read-line fp)))))
)

      (('return)
_PLAIN_TEXT
	return ;
_END_PLAIN_TEXT
)
      (('return x) 
_PLAIN_TEXT
	return  `(begin (self x 'v) "") ` ;
_END_PLAIN_TEXT
)
      ((booleanop x y) (guard (isinlst booleanop operator-booleans))
_PLAIN_TEXT
	(  `(begin (self x 'v) "")` `(fast-find-var-in-single-env booleanop boolean-op-map) ` `(begin (self y 'v) "") ` )
_END_PLAIN_TEXT
	(ifconte)
)
      ((operator2 x y) (guard (isinlst operator2 operator-2s-lst))
_PLAIN_TEXT
	(  `(begin (self x 'v) "")` `(fast-find-var-in-single-env operator2 operator-2s)` `(begin (self y 'v) "") ` )
_END_PLAIN_TEXT
	(ifconte)
)
      ((booleanop y) (guard (isinlst booleanop operator-booleans))
_PLAIN_TEXT
	(  `(fast-find-var-in-single-env booleanop boolean-op-map) ` `(begin (self y 'v) "") ` )
_END_PLAIN_TEXT
	(ifconte)
)
      ((function . args) (guard #t)
_PLAIN_TEXT
	`function` ( `(map-commas (lambda (x) (self x 'v)) args)` )
_END_PLAIN_TEXT
	(ifconte)
)
      (x (guard (or (number? x) (symbol? x) (string? x))) (write x)
	(ifconte)
)
      (x (guard (char? x)) (write-string "'" outfp) (write-char x outfp) (write-string "'" outfp) (ifconte))
      (x "")
)
)
)
(define boolean-op-map-no-env '((or . "||") (not . "!") (and . "&&") (eq? . "==")))
(define integer-ops '((shift-l . "<<") (shift-r . ">>") (b-and . "&") (b-or . "|") (b-xor . "^") (b-not . "~") (remainder . "%")))
(define operator-booleans '(< > <= >= == not or and eq?))
(define operator-2s-no-env (append  '((+ .  +) (- . -) (* . *) (/ . /) (semicolon . ";")) integer-ops (map (lambda (x) (cons x x)) operator-booleans)))
(define operator-2s-lst (map (lambda (x) (car x)) operator-2s-no-env))
(define operator-2s (fast-make-single-env-from-var-and-val operator-2s-no-env))
(define boolean-op-map (fast-make-single-env-from-var-and-val boolean-op-map-no-env))

(define simple-type-map 
  (fast-make-single-env-from-var-and-val 
    '((fixnum long) (float double) (string char*) (boolean int)))
)
(define int-types '(int unsigned-int long unsigned-long size_t ssize_t))
;(set! int-types (append int-types (map list int-types)))
(define float-types '(float double))
;(set! float-types (append float-types (map list float-types)))
(define find-type 
  (named-lambda self (y env)
    (patmatch y
      (x (guard (fixnum? x)) (fast-find-var-in-single-env 'fixnum simple-type-map))
      (x (guard (float? x)) (fast-find-var-in-single-env 'float simple-type-map))
      (x (guard (string? x)) (fast-find-var-in-single-env 'string simple-type-map))
      (x (guard (boolean? x)) (fast-find-var-in-single-env 'boolean simple-type-map))
      (x (guard (symbol? x)) (find-var-in-multi-env x env))
      ((leq . x) (guard (isinlst leq operator-booleans))
	(self #t env)
)
      ((xor . y) (guard (isinlst xor integer-ops))
	(self 0 env)
)
      ((addmul x y) (guard (isinlst addmul operator-2s-lst))
        (let ((typex (self x env)) (typey (self y env)))
	  (cond
	    ((and (isinlst typex int-types) (isinlst typey int-types))
	      (fast-find-var-in-single-env 'fixnum simple-type-map)
)
	    ((and (isinlst typex (append float-types int-types)) (isinlst typey (append float-types int-types)))
	      (fast-find-var-in-single-env 'float simple-type-map)
)
	    (else varnotbound )
)
)
)
      ;(('get-pointer arg) ())
      (('vector-ref arg n) (define vectype (self arg env)) 
	(if (eq? vectype varnotbound) varnotbound
	(string->symbol (list->string (reverse (cdr (reverse (string->list (symbol->string vectype))))))))
)
      ((x . rst) (find-var-in-multi-env x env))
      (x varnotbound)
)
))
(define (get-type-declare declares)
  (let loop ((n 7) (declares (string->list (to-string declares))))
    (cond ((eq?  n  -1) (string->symbol (list->string declares)))
      (else (loop (- n 1) (cdr declares)))
)
)
)
(define (get-type-define declares)
  (let loop ((n 6) (declares (string->list (to-string declares))))
    (cond ((eq?  n  -1) (string->symbol (list->string declares)))
      (else (loop (- n 1) (cdr declares)))
)
)
)
(define (first-n lst n)
  (cond ((= n 0) '()) (else (cons (car lst) (first-n (cdr lst) (- n 1)))))
)
(define (isdefine? dec)
  (cond
    ((or (symbol? dec) (string? dec)) 
      (define strl (string->list (to-string dec)))
      ;(define str (to-string dec))
      (cond 
	((> (length strl) 6) (eq? (list->string (first-n strl 6)) "define"))
        (else #f)
)
)
    (else #f)
)
)
(define (isdeclare? dec)
  (cond
    ((or (symbol? dec) (string? dec)) 
      (define strl (string->list (to-string dec)))
      ;(define str (to-string dec))
      (cond 
	((> (length strl) 7) (eq? (list->string (first-n strl 7)) "declare"))
        (else #f)
)
)
    (else #f)
)
)
(define (map-commas fun lst)
 (cond
  ((null? lst) "")
  ((null? (cdr lst)) (fun (car lst)) "")
  (else (fun (car lst)) (write-string " , ") (map-commas fun (cdr lst)))
)
)

;(fin-shell infile '())
