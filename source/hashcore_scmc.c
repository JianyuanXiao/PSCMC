#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <typedefs.h>
#include <math.h>

uint32_t SuperFastHash (const char * data, int len) ;
general_element internal_car(general_element );
general_element internal_cdr(general_element );
general_element write_stdout(general_element );
general_element internal_read_line(general_element );
general_element internal_call_ffi(general_element funnum,general_element funargs){
	assert(TYPE_OF(funnum)==INT_NUM);
	switch (funnum.data.num_int){
		case 0: 
			//write_stdout(funargs);
			assert(TYPE_OF(funargs)==STRING || TYPE_OF(funargs)==SYMBOL); 
			funnum.data.num_int=SuperFastHash(((struct_string*)funargs.data.string)->string_data,((struct_string*)funargs.data.string)->length); 
			return funnum;
			break;
		case 1:
			funnum.data.num_int=internal_car(funargs).data.num_int % internal_cdr(funargs).data.num_int;
			return funnum;
		case 2:
			funnum.data.num_int=internal_car(funargs).data.character;
			return funnum;
		case 3:
			funnum.data.character=internal_car(funargs).data.num_int;
			TYPE_OF(funnum)=CHAR;
			return funnum;
		case 4:
			funnum.data.num_int=floor(funargs.data.num_float);
			TYPE_OF(funnum)=INT_NUM;
			return funnum;
		case 5:
			return internal_read_line (funargs);
		default:
			break;
	}
	return funargs;
}
#undef get16bits
#if (defined(__GNUC__) && defined(__i386__)) || defined(__WATCOMC__) \
  || defined(_MSC_VER) || defined (__BORLANDC__) || defined (__TURBOC__)
#define get16bits(d) (*((const uint16_t *) (d)))
#endif

#if !defined (get16bits)
#define get16bits(d) ((((uint32_t)(((const uint8_t *)(d))[1])) << 8)\
                       +(uint32_t)(((const uint8_t *)(d))[0]) )
#endif
uint32_t SuperFastHash (const char * data, int len) {
uint32_t hash = len, tmp;
int rem;

    if (len <= 0 || data == NULL) return 0;

    rem = len & 3;
    len >>= 2;

    /* Main loop */
    for (;len > 0; len--) {
        hash  += get16bits (data);
        tmp    = (get16bits (data+2) << 11) ^ hash;
        hash   = (hash << 16) ^ tmp;
        data  += 2*sizeof (uint16_t);
        hash  += hash >> 11;
    }

    /* Handle end cases */
    switch (rem) {
        case 3: hash += get16bits (data);
                hash ^= hash << 16;
                hash ^= ((signed char)data[sizeof (uint16_t)]) << 18;
                hash += hash >> 11;
                break;
        case 2: hash += get16bits (data);
                hash ^= hash << 11;
                hash += hash >> 17;
                break;
        case 1: hash += (signed char)*data;
                hash ^= hash << 10;
                hash += hash >> 1;
    }

    /* Force "avalanching" of final 127 bits */
    hash ^= hash << 3;
    hash += hash >> 5;
    hash ^= hash << 4;
    hash += hash >> 17;
    hash ^= hash << 25;
    hash += hash >> 6;

    return hash;
}
