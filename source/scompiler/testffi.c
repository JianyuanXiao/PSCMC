#include <stdio.h>
#include "typedefs.h"
extern general_element global_argv;
general_element internal_call_ffi(general_element funnum,general_element funargs){
	//fprintf(stdout,"the funnum is %ld\n",funnum.data.num_int);
	return global_argv;
}
