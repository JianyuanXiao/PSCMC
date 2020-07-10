#ifndef TYPES_FOR_CSCHEME_COMPILER
#define TYPES_FOR_CSCHEME_COMPILER
typedef double FLOAT;
typedef long INT;
typedef enum {INT_NUM=512,FLOAT_NUM,BOOLEAN,CHAR,STRING,VECTOR,PAIR,EMPTY_LIST,FUNCTION,SYMBOL,PORT,EOF_OBJECT}types;

typedef struct general_element
{
	INT type_and_gc;
	union{
		FLOAT num_float;
		INT num_int;
		char character;
		void * pair;
		void * ge_vector;
		void * function;
		void * string;
		void * symbol;
		void * port;
	}data;
}general_element;
typedef enum {CLOSED,FILE_IN_PORT,FILE_OUT_PORT} port_type;
typedef struct{
	void * gced;
	INT length;
	char * string_data;
}struct_string;
typedef struct {
	void * gced;
	INT isclosed_and_type;
	union{
		FILE * fp;
	}data;
}struct_port;
#define TYPE_OF_PORT(pt) (pt).isclosed_and_type
/*
typedef struct{
	INT length;
	char * symbol_string_data;
}struct_symbol;*/
typedef struct general_vector{
	void * gced;
	INT length;
	general_element * data;
}general_vector;
typedef struct general_pair
{
	void * gced;
	general_element car;
	general_element cdr;
}general_pair;
#define TYPE_OF(a) (a).type_and_gc
#define TYPE_OF_P(a) (a)->type_and_gc


#endif //TYPES_FOR_CSCHEME_COMPILER
