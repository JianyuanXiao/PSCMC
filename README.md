# PSCMC
The SCMC and PSCMC programming language is designed for multi-platform parallel programming. It is a DSL based on the scheme programming language which is a dialect of lisp. Currently it support C, OpenMP, CUDA, OpenCL and SWMC backends. The document can be accessed through 

https://jianyuanxiao.github.io/scmc.html

and 

https://jianyuanxiao.github.io/pscmc_kernel.html

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
the one used in the SymPIC project. Now you may try examples located in the example 
directory
