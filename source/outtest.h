#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <time.h>
#include <ctype.h>
#include <assert.h>

/* The max number of args for function is 255
 * */
#include "typedefs.h"
#ifndef ALLOC
#define ALLOC malloc
#endif

general_element internal_call_ffi(general_element funnum,general_element funargs);

general_element internal_remainder(general_element a,general_element b){
	general_element ans;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=a.data.num_int%b.data.num_int;
	}else{
		fprintf(stderr,"Error: remainder must take integer arguments\n");
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_general_sqrt(general_element a){
	general_element ans;
	if(TYPE_OF(a)==INT_NUM ){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=sqrt(a.data.num_int);
	}else
	if(TYPE_OF(a)==FLOAT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=sqrt(a.data.num_float);
	}else{
		fprintf(stderr,"Error: sqrt must take number arguments\n");
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_general_floor(general_element a){
	general_element ans;
	if(TYPE_OF(a)==INT_NUM ){
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=a.data.num_int;
	}else
	if(TYPE_OF(a)==FLOAT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=floor(a.data.num_float);
	}else{
		fprintf(stderr,"Error: floor must take number arguments\n");
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=0;
	}
	return ans;
}

general_element internal_general_mul(general_element a,general_element b){
	general_element ans;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=a.data.num_int*b.data.num_int;
	}else
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==FLOAT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_int*b.data.num_float;
	}else
	if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==INT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_float*b.data.num_int;
	}else
	if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==FLOAT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_float*b.data.num_float;
	}else{
		fprintf(stderr,"Error: mul must take number arguments\n");
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_general_div(general_element a,general_element b){
	general_element ans;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=(FLOAT)a.data.num_int/b.data.num_int;
	}else
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==FLOAT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_int/b.data.num_float;
	}else
	if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==INT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_float/b.data.num_int;
	}else
	if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==FLOAT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_float/b.data.num_float;
	}else{
		fprintf(stderr,"Error: mul must take number arguments\n");
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_int2char(general_element a){
	general_element ans;
	TYPE_OF(ans)=CHAR;
	if(TYPE_OF(a)==INT_NUM){
		ans.data.character=a.data.num_int;
		return ans;
	}else{
		fprintf(stderr,"Error in int2char: not a int\n");
		return ans;
	}

}
general_element internal_general_sub(general_element a,general_element b){
	general_element ans;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=a.data.num_int-b.data.num_int;
	}else
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==FLOAT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_int-b.data.num_float;
	}else
	if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==INT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_float-b.data.num_int;
	}else
	if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==FLOAT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_float-b.data.num_float;
	}else{
		fprintf(stderr,"Error: sub must take number arguments\n");
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=0;
	}
	return ans;
}

general_element internal_bitwise_and(general_element a,general_element b){
	general_element ans;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=a.data.num_int&b.data.num_int;
	}else{
		fprintf(stderr,"Error: bitwise-and must take fixnum arguments\n");
		fprintf(stderr,"type(a)=%d, type(b)=%d\n",TYPE_OF(a),TYPE_OF(b));
		assert(0);
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_arithmetic_shift(general_element a,general_element b){
	general_element ans;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		TYPE_OF(ans)=INT_NUM;
		if(b.data.num_int>0){
			ans.data.num_int=a.data.num_int<<b.data.num_int;
		}else{
			ans.data.num_int=a.data.num_int>>(-b.data.num_int);
		}
	}else{
		fprintf(stderr,"Error: arithmetic-shift must take fixnum arguments\n");
		fprintf(stderr,"type(a)=%d, type(b)=%d\n",TYPE_OF(a),TYPE_OF(b));
		assert(0);
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_general_add(general_element a,general_element b){
	general_element ans;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=a.data.num_int+b.data.num_int;
	}else
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==FLOAT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_int+b.data.num_float;
	}else
	if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==INT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_float+b.data.num_int;
	}else
	if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==FLOAT_NUM){
		TYPE_OF(ans)=FLOAT_NUM;
		ans.data.num_float=a.data.num_float+b.data.num_float;
	}else{
		fprintf(stderr,"Error: add must take number arguments\n");
		fprintf(stderr,"type(a)=%d, type(b)=%d\n",TYPE_OF(a),TYPE_OF(b));
		assert(0);
		TYPE_OF(ans)=INT_NUM;
		ans.data.num_int=0;
	}
	return ans;
}


general_element init_from_string(char * a){
	general_element ans;
	TYPE_OF(ans)=STRING;
	ans.data.string=ALLOC(sizeof(struct_string));
	((struct_string*)ans.data.string)->length=0;
	((struct_string*)ans.data.string)->gced=0;
	INT len=strlen(a);
	PUSH(ans);
	char * data=ALLOC(sizeof(char)*(len+1));
	POP(ans);
	((struct_string*)ans.data.string)->string_data=data;
	((struct_string*)ans.data.string)->length=len;
	TYPE_OF(ans)=STRING;
	strcpy(((struct_string*)ans.data.string)->string_data,a);
	return ans;
}
general_element init_from_symbol(char * a){
	assert(isalpha(a[0]) || (a[0]!='#' && a[0]!='\"' && a[0]!='\''));
	general_element ans=init_from_string(a);
	TYPE_OF(ans)=SYMBOL;
	return ans;
}
general_element init_from_float(FLOAT a){
	general_element ans;
	TYPE_OF(ans)=FLOAT_NUM ;
	ans.data.num_float=a;
	return ans;
}
general_element init_from_char(char a){
	general_element ans;
	TYPE_OF(ans)=CHAR;
	ans.data.character=a;
	return ans;
}
general_element init_from_function(void * a){
	general_element ans;
	TYPE_OF(ans)=FUNCTION;
	ans.data.function=a;
	return ans;
}
general_element init_from_function_narg(void * a,INT numargs,INT isthelast_pair){
	general_element ans;
	({TYPE_OF(ans)=numargs*2+isthelast_pair;});
	ans.data.function=a;
	return ans;
}
general_element init_from_boolean(INT a){
	general_element ans;
	({TYPE_OF(ans)=BOOLEAN;});
	ans.data.num_int=a;
	return ans;
}
general_element init_from_null(){
	general_element ans;
	TYPE_OF(ans)=EMPTY_LIST;
	return ans;
}
general_element init_from_int(INT a){
	general_element ans;
	({TYPE_OF(ans)=INT_NUM;});
	ans.data.num_int=a;
	return ans;
}

#define GETCAR(p) (((general_pair*)p.data.pair)->car)
#define GETCDR(p) (((general_pair*)p.data.pair)->cdr)
general_element internal_write(general_element m,general_element fp);
general_element write_stderr(general_element m);

general_element internal_write_pair(general_element p,general_element fp){
	FILE * outfp=((struct_port*)(fp.data.port))->data.fp;
begin:
	if(TYPE_OF(GETCDR(p))==PAIR){
		//if (TYPE_OF(GETCAR(p)) == SYMBOL && !strcmp(((struct_string*)GETCAR(p).data.string)->string_data,"vector-ref")) { general_element p1=GETCAR(GETCDR(p)); fprintf(stderr,"%d,%d,",TYPE_OF(p1),SYMBOL); if(TYPE_OF(p1)==SYMBOL){ fprintf(stderr,"l=%d,s=%s,",((struct_string*)p1.data.string)->length,((struct_string*)p1.data.string)->string_data); } write_stderr(GETCDR(p)); fprintf(stderr,"\n"); }
		internal_write(GETCAR(p),fp);

		fprintf(outfp," ");
		p=GETCDR(p);
		goto begin;
	}else{
		internal_write(GETCAR(p),fp);
		if(TYPE_OF(GETCDR(p))!=EMPTY_LIST){
			fprintf(outfp," . ");
			internal_write(GETCDR(p),fp);
		}else{
			;
		}
	}
	return init_from_int(0);
}
general_element internal_get_build_in_ports(general_element);
general_element internal_car(general_element p){
	if(TYPE_OF(p)!=PAIR){
		//internal_write(p,internal_get_build_in_ports(init_from_int(2)));
		fprintf(stderr,"type=%ld,should be %ld\n",TYPE_OF(p),PAIR);
	}
	assert(TYPE_OF(p)==PAIR);
	return GETCAR(p);
}
general_element internal_get_build_in_ports(general_element );
general_element internal_cdr(general_element p){
	if(TYPE_OF(p)!=PAIR){
		//internal_write(p,internal_get_build_in_ports(init_from_int(2)));
		fprintf(stderr,"type=%ld,should be %ld\n",TYPE_OF(p),PAIR);
	}
	assert(TYPE_OF(p)==PAIR);
	return GETCDR(p);
}
void write_string_to_file(char * str , FILE * out){
	fprintf(out,"\"");
	while(*str){
		switch(*str){
			case '\n':
				fprintf(out,"\\n");
				break;
			case '\t':
				fprintf(out,"\\t");
				break;
			case '\\':
				fprintf(out,"\\\\");
				break;
			case '"':
				fprintf(out,"\\\"");
				break;
			default:
				fprintf(out,"%c",*str);
				break;
		}
		str++;
	}
	fprintf(out,"\"");
}

general_element internal_write_p(general_element * m,general_element fp){
	FILE * outfp=((struct_port*)(fp.data.port))->data.fp;
	general_element donesym;
	TYPE_OF(donesym)=INT_NUM;
	donesym.data.num_int=0;
	switch (TYPE_OF_P(m)){
		case INT_NUM:
			fprintf(outfp,"%ld",m->data.num_int);
			break;
		case FLOAT_NUM:
			fprintf(outfp,"%.17e",m->data.num_float); 
			break;
		case STRING:
			write_string_to_file(((struct_string*)m->data.string)->string_data,outfp);
			//fprintf(outfp,"\"%s\"",((struct_string*)m->data.string)->string_data);
			break;
		case SYMBOL:
			fprintf(outfp,"%s",((struct_string*)m->data.string)->string_data);
			break;
		case CHAR:
			if(m->data.character==' '){
				fprintf(outfp,"#\\space");
			}else 
			if(m->data.character=='\n'){
				fprintf(outfp,"#\\newline");
			}else{
				fprintf(outfp,"#\\%c",m->data.character);
			}
			break;
		case BOOLEAN:
			if(m->data.num_int){
				fprintf(outfp,"#t");
			}else{
				fprintf(outfp,"#f");
			}
			break;
		case PAIR:
			fprintf(outfp,"(");
			internal_write_pair(m[0],fp);
			fprintf(outfp,")");
			break;
		case VECTOR:
			fprintf(outfp,"#(");
			int i;
			for(i=0;i<((general_vector*)(m->data.ge_vector))->length-1;i++){
				internal_write_p(((general_vector*)(m->data.ge_vector))->data+i,fp);
				fprintf(outfp," ");
			}
			if(((general_vector*)(m->data.ge_vector))->length>=1){
				internal_write_p(((general_vector*)(m->data.ge_vector))->data+((general_vector*)(m->data.ge_vector))->length-1,fp);
			}
			fprintf(outfp,")");
			break;
		case EMPTY_LIST:
			fprintf(outfp,"()");
			break;
		default:
			break;
	}
	return donesym;
}
general_element internal_write(general_element m,general_element fp){
	assert(TYPE_OF(fp)==PORT);
	return internal_write_p(&m,fp);
}

general_element internal_general_iseq(general_element a,general_element b){
	general_element ans;
	TYPE_OF(ans)=BOOLEAN;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_int==b.data.num_int;
	}else if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_int==b.data.num_float;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_float==b.data.num_int;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_float==b.data.num_float;
	}else if(TYPE_OF(a)==BOOLEAN && TYPE_OF(b)==BOOLEAN){
		ans.data.num_int=a.data.num_int==b.data.num_int;
	}else if(TYPE_OF(a)==CHAR && TYPE_OF(b)==CHAR){
		ans.data.num_int=a.data.character==b.data.character;
	}else if(TYPE_OF(a)==VECTOR&& TYPE_OF(b)==VECTOR){
		ans.data.num_int=a.data.ge_vector==b.data.ge_vector;
	}else if(TYPE_OF(a)==PAIR && TYPE_OF(b)==PAIR){
		ans.data.num_int=a.data.pair==b.data.pair;
	}else if(TYPE_OF(a)==STRING && TYPE_OF(b)==STRING){
		ans.data.num_int=!(strcmp(((struct_string*)(a.data.string))->string_data,((struct_string*)b.data.string)->string_data));
	}else if(TYPE_OF(a)==SYMBOL && TYPE_OF(b)==SYMBOL){
		ans.data.num_int=!(strcmp(((struct_string*)(a.data.string))->string_data,((struct_string*)b.data.string)->string_data));
	}else if(TYPE_OF(a)==FUNCTION && TYPE_OF(b)==FUNCTION){
		ans.data.num_int=(a.data.function==b.data.function);
	}else if(TYPE_OF(a)==EMPTY_LIST && TYPE_OF(b)==EMPTY_LIST){
		ans.data.num_int=1;
	}else{
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_not(general_element a){
	general_element ans;
	TYPE_OF(ans)=BOOLEAN;
	if(TYPE_OF(a)==BOOLEAN){
		ans.data.num_int=!a.data.num_int;
	}else{
		ans.data.num_int=1;
	}
	return ans;
}
general_element null_i_s(general_element a){
	general_element ans;
	TYPE_OF(ans)=BOOLEAN;
	if(TYPE_OF(a)==EMPTY_LIST){
		ans.data.num_int=1;
	}else{
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_ispair(general_element a){
	general_element ans;
	TYPE_OF(ans)=BOOLEAN;
	if(TYPE_OF(a)==PAIR){
		ans.data.num_int=1;
	}else{
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_larger_eq(general_element a,general_element b){
	general_element ans;
	TYPE_OF(ans)=BOOLEAN;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_int>=b.data.num_int;
	}else if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_int>=b.data.num_float;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_float>=b.data.num_int;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_float>=b.data.num_float;
	}else {
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_larger_than(general_element a,general_element b){
	general_element ans;
	TYPE_OF(ans)=BOOLEAN;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_int>b.data.num_int;
	}else if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_int>b.data.num_float;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_float>b.data.num_int;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_float>b.data.num_float;
	}else {
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_less_than(general_element a,general_element b){
	general_element ans;
	TYPE_OF(ans)=BOOLEAN;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_int<b.data.num_int;
	}else if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_int<b.data.num_float;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_float<b.data.num_int;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_float<b.data.num_float;
	}else {
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_less_eq(general_element a,general_element b){
	general_element ans;
	TYPE_OF(ans)=BOOLEAN;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_int<=b.data.num_int;
	}else if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_int<=b.data.num_float;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_float<=b.data.num_int;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_float<=b.data.num_float;
	}else {
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_iseq(general_element a,general_element b){
	general_element ans;
	TYPE_OF(ans)=BOOLEAN;
	if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_int==b.data.num_int;
	}else if(TYPE_OF(a)==INT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_int==b.data.num_float;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==INT_NUM){
		ans.data.num_int=a.data.num_float==b.data.num_int;
	}else if(TYPE_OF(a)==FLOAT_NUM && TYPE_OF(b)==FLOAT_NUM){
		ans.data.num_int=a.data.num_float==b.data.num_float;
	}else {
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_make_n_vector(INT n){
	if(n==0){
		fprintf(stderr,"Warning: 0 length vector\n");
	}
	general_element ans;
	TYPE_OF(ans)=VECTOR;
	ans.data.ge_vector=ALLOC(sizeof(general_vector));
	((general_vector*)(ans.data.ge_vector))->gced=0;
	((general_vector*)(ans.data.ge_vector))->length=0;
	PUSH(ans);
	general_element * data=ALLOC(sizeof(general_element)*n);
	POP(ans);
	((general_vector*)(ans.data.ge_vector))->data=data;
	//((general_vector*)(ans.data.ge_vector))->gced=0;
	((general_vector*)(ans.data.ge_vector))->length=n;
	//TYPE_OF(ans)=VECTOR;
	return ans;
}
general_element internal_make_vector(general_element n){
	assert(TYPE_OF(n)==INT_NUM);
	return internal_make_n_vector(n.data.num_int);
}
general_element internal_make_closure_narg(INT n, void * funname,INT numargs,INT islastpair){
	general_element ans=internal_make_n_vector(n);
	(((general_vector*)ans.data.ge_vector)->data)[0]=init_from_function_narg(funname,numargs,islastpair);
	return ans;
}
general_element internal_make_closure(INT n, void * funname){
	general_element ans=internal_make_n_vector(n);
	(((general_vector*)ans.data.ge_vector)->data)[0]=init_from_function(funname);
	return ans;
}
general_element internal_make_vector_from_array(INT n, general_element * ge_array){
	
	INT i;
	for(i=0;i<n;i++){
		PUSH(ge_array[i]);
	}
	general_element ans=internal_make_n_vector(n);
	for(i=n-1;i>=0;i--){
		POP(ge_array[i]);
	}
	for(i=0;i<n;i++){
		(((general_vector*)ans.data.ge_vector)->data)[i]=ge_array[i];
	}
	return ans;
}
general_element internal_setcar(general_element pair,general_element rhs){
	assert(TYPE_OF(pair)==PAIR);
	((general_pair*)pair.data.pair)->car=rhs;
	return pair;
}
general_element internal_setcdr(general_element pair,general_element rhs){
	assert(TYPE_OF(pair)==PAIR);
	((general_pair*)pair.data.pair)->cdr=rhs;
	return pair;
}
general_element internal_vector_set(general_element vec,general_element n,general_element rhs){
	assert(TYPE_OF(vec)==VECTOR);
	assert(n.data.num_int < ((general_vector*)vec.data.ge_vector)->length);
	((general_vector*)vec.data.ge_vector)->data[n.data.num_int]=rhs;
	return vec;
}
general_element internal_vector_ref(general_element vec,general_element n){
	assert(TYPE_OF(vec)==VECTOR);
	assert(n.data.num_int < ((general_vector*)vec.data.ge_vector)->length);
	return ((general_vector*)vec.data.ge_vector)->data[n.data.num_int];
}
general_element internal_vector_length(general_element vec){
	assert(TYPE_OF(vec)==VECTOR);
	return init_from_int(((general_vector*)vec.data.ge_vector)->length);
}
general_element internal_cons(general_element carele,general_element cdrele){
	general_element ans;
	TYPE_OF(ans)=PAIR;
	PUSH(carele);
	PUSH(cdrele);
	ans.data.pair=ALLOC(sizeof(general_pair));
	((general_pair*)ans.data.pair)->gced=0;
	POP(cdrele);
	POP(carele);
	((general_pair*)ans.data.pair)->car=carele;
	((general_pair*)ans.data.pair)->cdr=cdrele;
	return ans;
}
general_element internal_make_list_from_array(INT n, general_element * ge_array){
	INT i;
	general_element ans;
	TYPE_OF(ans)=EMPTY_LIST;
	general_element tmp1=internal_make_vector_from_array(n,ge_array);
	PUSH(tmp1);
	for(i=n-1;i>=0;i--){
		//POP(tmp1);
		general_element tmp2=global_stack[current_stack_head-1];
		ans=internal_cons(((general_vector*)(tmp2.data.ge_vector))->data[i],ans);
		//ans=internal_cons(ge_array[i],ans);
		//PUSH(tmp1);
	}
	POP(tmp1);
	return ans;
}
