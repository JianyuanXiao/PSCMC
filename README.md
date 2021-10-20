# PSCMC
The SCMC and PSCMC programming language is designed for multi-platform parallel programming. It is a DSL based on the scheme programming language which is a dialect of lisp. Currently it support C, OpenMP, CUDA, OpenCL, SWMC, COI, HIP and SYCL backends. The document can be accessed through 

https://jianyuanxiao.github.io/scmc.html

and 

https://jianyuanxiao.github.io/pscmc_kernel.html

In this project, the superfasthash 
http://www.azillionmonkeys.com/qed/hash.html
and the uthash
https://troydhanson.github.io/uthash/
are used.

# Install 
Using the following command to compile the compiler for PSCMC, 

```bash
cd source
make
```

To run the compiler, several environment variables are needed. In the source directory,
these variables can be set as

```bash
export SCMC_COMPILE_ROOT=`pwd`
export SCMC_ROOT=`pwd`/runtime_passes
export STDLIB=`pwd`/stdlib.scm
```

Note that the STDLIB variable is required by the scheme interpreter, it is the same as 
the one used in the SymPIC project. Now the compiler scripts scmc_compile_passes and 
scmc_parallel_compile_passes are ready, and you may try examples located in the example 
directory

# Compile
The source code of the SCMC and PSCMC compilers are located in the source/scompiler 
directory. To compile the code, you should first run
```bash
cd source/scompiler
make
```
to build a scheme to c compiler. Note that due to the compiling speed and memory usage reason, 
we use clang and -O0 in the Makefile. You may change the compiler to gcc and the CFLAGS to -O2 
in machines with large memory. I have test it under amd64 Linux systems. Then use 
```bash
./gen_pscmc_compiler
```
to generate the SCMC and PSCMC compilers.
