CC=clang
CFLAGS=-O0 -lm -I./
CFLAGS_FOR_ELIMINATE_DEAT=-DMAX_STACK_NUM=10960000 -DMAX_HEAP_NUM=203840000 -DMAX_CALL_STACK=102400
CFLAGS_FOR_REGALLOC=-DMAX_STACK_NUM=10960000 -DMAX_HEAP_NUM=203840000 -DMAX_CALL_STACK=102400
all: pass13-regalloc generate-c-file pass1 pass3-uncover-settable pass3-2-remove-impure-letrec pass35-remove-set! pass2-convert-complex-datum pass5-remove-anoymous-lambda pass6-sanitize-binding pass7-uncover-free pass75 pass9-lift-lambdas pass8-convert-closures pass955-remove-dummy pass10-core pass11-eliminate-let flatten-prog pass-partial-eval-opt pass-eliminate-dead pass-reduce-varlen eliminate-list-vector current-compile
ALLT=pass13-regalloc generate-c-file pass1 pass3-uncover-settable pass3-2-remove-impure-letrec pass35-remove-set! pass2-convert-complex-datum pass5-remove-anoymous-lambda pass6-sanitize-binding pass7-uncover-free pass75 pass9-lift-lambdas pass8-convert-closures pass955-remove-dummy pass10-core pass11-eliminate-let flatten-prog pass-partial-eval-opt pass-eliminate-dead pass-reduce-varlen eliminate-list-vector current-compile
pass1:
generate-c-file: generate-c-file.c testffi.c
	$(CC) $(CFLAGS) generate-c-file.c testffi.c -o generate-c-file
pass13-regalloc: pass13-regalloc.c
	$(CC) $(CFLAGS) $(CFLAGS_FOR_REGALLOC) pass13-regalloc.c -o pass13-regalloc
pass3-uncover-settable:
pass3-2-remove-impure-letrec:
"pass35-remove-set\!":
pass2-convert-complex-datum:
pass5-remove-anoymous-lambda:
pass6-sanitize-binding:
pass7-uncover-free:
pass75:
pass9-lift-lambdas:
eliminate-list-vector:
pass8-convert-closures:
pass955-remove-dummy:
pass10-core:
pass11-eliminate-let:
flatten-prog: flatten-prog.c
	$(CC) $(CFLAGS) $(CFLAGS_FOR_REGALLOC) flatten-prog.c -o flatten-prog
pass-partial-eval-opt: pass-partial-eval-opt.c hashcore.c
	$(CC) $(CFLAGS) $(CFLAGS_FOR_REGALLOC) pass-partial-eval-opt.c hashcore.c -o pass-partial-eval-opt
pass-eliminate-dead: pass-eliminate-dead.c
	$(CC) $(CFLAGS) $(CFLAGS_FOR_ELIMINATE_DEAT) pass-eliminate-dead.c -o pass-eliminate-dead
pass-reduce-varlen: pass-reduce-varlen.c
	$(CC) $(CFLAGS) $(CFLAGS_FOR_ELIMINATE_DEAT) pass-reduce-varlen.c -o pass-reduce-varlen
current-compile:
.PHONY:clean
clean	:
	-rm $(ALLT)
