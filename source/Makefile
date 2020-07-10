CC=cc
CFLAG=-O0 -lm -I./
PREFIX=/usr/local
all	:cscheme scmc2c_pre_pass scmc2c_multi_pass
cscheme	:cscheme.c singlemath.h binops.h uthash.h types.h
	$(CC) cscheme.c $(CFLAG) -o cscheme
scmc2c_pre_pass	:pre_passes.c hashcore_scmc.c
	$(CC) pre_passes.c hashcore_scmc.c $(CFLAG) -o scmc2c_pre_pass
scmc2c_multi_pass	:fin_shell.c hashcore_scmc.c
	$(CC) fin_shell.c hashcore_scmc.c $(CFLAG) -o scmc2c_multi_pass
clean		:
	rm cscheme scmc2c_pre_pass scmc2c_multi_pass
