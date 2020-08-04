#include <stdint.h>
#define ERR_REPORT(x) ;
general_element global_eof;
general_element the_empty_list;
general_element quote_vector_symbol;
general_element quote_symbol;
general_element unquote_symbol;
general_element quasiquote_symbol;
general_element global_true;
general_element global_false;
general_element global_argv;
INT getc_from_port(struct_port in);
INT ungetc_from_port(INT c,struct_port in);
INT delete_void_char(struct_port in);
INT dec_is_slash(char * str,INT cur_i){
	INT ret=1;
	cur_i--;
	while(cur_i>=0 && str[cur_i]=='\\'){
		ret=!ret;
		cur_i--;
	}
	return ret;
}
INT escape_char(INT in){
	INT out;
	switch(in){
		case 't':
			out='\t';
			break;
		case 'r':
			out='\r';
			break;
		case 'v':
			out='\v';
			break;
		case 'n':
			out='\n';
			break;
		case '"':
			out='"';
			break;
		default:
			out=in;
			break;
	}
	return out;
}
INT delete_void_char(struct_port in){
	INT c;
beg:
	c=getc_from_port(in);
	if(c==EOF){
		return EOF;
	}
	if(isspace(c))goto beg;
	if(c==';'){
		while(((c=getc_from_port(in))!=EOF) && (c != '\n'));
		goto beg;
	}
	ungetc_from_port(c,in);
	return c;
}

INT first_char(struct_port in){
	INT c;
	c=getc_from_port(in);
	ungetc_from_port(c,in);
	return c;
}
INT string_escape_copy(char * dst,char * src,size_t n){
	INT i=0;
	INT j=0;
	while(i<n-1 && src[j]){
		if(src[j]=='\\'){
			j++;
			dst[i]=escape_char(src[j]);
		}else{
			dst[i]=src[j];
		}
		i++;
		j++;
	}
	dst[i]=0;
	return i;
}

INT isint_or_float(const char * buf){ //int=1, float=2, other=0
	INT fstc=buf[0];
	if('0' == buf[0]  &&  'x'==buf[1])return 1;
	if(isdigit(fstc)||fstc=='.'||fstc=='-'){
		if(fstc=='-'&& buf[1]!='.' && !isdigit(buf[1]))return 0;
		if(strstr(buf,"e")||strstr(buf,"E") || strstr(buf,"."))return 2;
		else return 1;
	}else{
		return 0;
	}
}

INT read_int_from_buf(char * buf){
	INT ans;
	sscanf(buf,"%ld",&ans);
	return ans;
}
FLOAT read_float_from_buf(char * buf){
	FLOAT ans;
	sscanf(buf,"%lf",&ans);
	return ans;
}
INT issymbol_char(INT c){
	return isalpha(c)||c=='+'||c=='-'||c=='*'||c=='/'||c=='>'||c=='<'||c=='_'||c=='='||c=='$'||c=='%';
}

#define BUFMAX 409600
char buffer[BUFMAX];
INT isdelimiter(INT c){
	//fprintf(stderr,"%c\n",c);
	return isspace(c)||c=='('||c==')'||c==EOF||c=='"'||c==';'||c=='['||c==']';
}

INT getc_from_port(struct_port port){
	switch (TYPE_OF_PORT(port)){
		case CLOSED:
			return EOF;
			break;
		case FILE_IN_PORT:
			return getc(port.data.fp);
			break;
		default:
			return EOF;
			break;
	}
}
INT ungetc_from_port(INT c,struct_port port){
	switch (TYPE_OF_PORT(port)){
		case CLOSED:
			return EOF;
			break;
		case FILE_IN_PORT:
			return ungetc(c,port.data.fp);
			break;
		default:
			return EOF;
			break;
	}
}

void read_buf(struct_port in){
	INT i=0;
	while(i<BUFMAX){
		char c=getc_from_port(in);
		if(isdelimiter(c)){
			if(!(i>1&&buffer[i-2]=='#' && buffer[i-1]=='\\')){
				ungetc_from_port(c,in);
				break;
			}
		}
		buffer[i]=c;
		i++;
	}
	if(i>=BUFMAX){
		fprintf(stderr,"Error: read buffer over flow\n");
		ERR_REPORT(1);
	}
	buffer[i]=0;
}
general_element internal_get_type(general_element a){
	return init_from_int(a.type_and_gc);
}


general_element read_element(struct_port in);

general_element read_pair(struct_port in){
	general_element ans;
	INT jdg=delete_void_char(in);
	if(jdg==EOF)return global_eof;
	char c=getc_from_port(in);
	if(c==')'||c==']'){
		return the_empty_list;
	}
	ungetc_from_port(c,in);
	//ans->type=PAIR;
	//ans->data.pair.istail=0;
	general_element carans=read_element(in);
	general_element cdrans;
	PUSH(carans);
	//fprintf(stderr,"pair detected, %ld\n",ans->data.pair.car->data.intnum);
	delete_void_char(in);
	c=getc_from_port(in);
	if(c == '.'){
		cdrans=read_element(in);
		delete_void_char(in);
		c=getc_from_port(in);
		//assert(c==')'||c==']');
		if(!(c==')'||c==']')){
			fprintf(stderr,"Error: ) or ] not matched\n");
			ERR_REPORT(1);
		}
		POP(carans);
		ans=internal_cons(carans,cdrans);
		return ans;
	}
	if(c == ')' || c==']'){
		POP(carans);
		ans=internal_cons(carans,the_empty_list);
		return ans;
	}
	ungetc_from_port(c,in);
	cdrans=read_pair(in);
	POP(carans);
	ans=internal_cons(carans,cdrans);
	return ans;
}
general_element init_from_string(char *);
general_element internal_read_line(general_element fp){
	char * p1=NULL;
	size_t len=0;
	struct_port * sp=fp.data.port;
	ssize_t readed;
	if(sp->isclosed_and_type==FILE_IN_PORT){
		readed=getline(&p1,&len,sp->data.fp);
	}else{
		fprintf(stderr,"Error: invalid fp in read-line!\n");
	}
	if(readed==-1){
		return global_eof;
	}else{
		general_element ans=init_from_string(p1);
		free(p1);
		return ans;
	}
}

general_element internal_get_argv(){
	return global_argv;
}

general_element internal_system(general_element a){
	assert(TYPE_OF(a)==STRING);
	struct_string * st=a.data.string;
	return init_from_int(system(st->string_data));
}


general_element read_element(struct_port in){
	if(in.isclosed_and_type==CLOSED){
		return global_eof;
	}
	INT ret=delete_void_char(in);
	if(ret==EOF)return global_eof;
	INT fstc=first_char(in);
	if(fstc=='('||fstc=='['){
		getc_from_port(in);
		return read_pair(in);
	}
	if(fstc==')'){
		fprintf(stderr,"Error: unmatched parentheses )\n");
		getc_from_port(in);
		ERR_REPORT(1);
	}
	if(fstc=='\''){
		getc_from_port(in);
		general_element dat=read_element(in);
		general_element tmp=internal_cons(dat,the_empty_list);
		general_element ret=internal_cons(quote_symbol,tmp);
		return ret;
	}
	if(fstc=='`'){
		getc_from_port(in);
		general_element dat=read_element(in);
		general_element tmp=internal_cons(dat,the_empty_list);
		general_element ret=internal_cons(quasiquote_symbol,tmp);
		return ret;
	}
	if(fstc==','){
		getc_from_port(in);
		general_element dat=read_element(in);
		general_element tmp=internal_cons(dat,the_empty_list);
		general_element ret=internal_cons(unquote_symbol,tmp);
		return ret;
	}
	general_element ans;//=alloc_element();
	if(fstc=='"'){
		INT i=0;
		char c=getc_from_port(in);
		while((c=getc_from_port(in))!=EOF && i<BUFMAX){
			if(c=='"'){
				if(dec_is_slash(buffer,i)){
					buffer[i]=0;
					string_escape_copy(buffer,buffer,sizeof(char)*(i+1));
					ans=init_from_string(buffer);
					return ans;
				}
			}
			buffer[i]=c;
			i++;
		}
		if(i>=BUFMAX){
			fprintf(stderr,"Error: reading buffer over flow in read_element\n");
			buffer[i]=0;
			fprintf(stderr,"\"%s\" too long\n",buffer);
			ERR_REPORT(1);
		}
		if(c==EOF){
			fprintf(stderr,"Error: unexpected EOF\n");
			ERR_REPORT(1);
		}
		//assert(i<BUFMAX);
		//assert(c!=EOF);
	}
	read_buf(in);


	INT intorfloat=isint_or_float(buffer);
	if(intorfloat==1){
		return init_from_int(read_int_from_buf(buffer));
	}
	if(intorfloat==2){
		return init_from_float(read_float_from_buf(buffer));
	}
	if(fstc=='#'){
		if(buffer[1]=='f'){
			/*
			ans->data.boolean=0;
			ans->type=BOOLEAN;*/
			return global_false;
		}else if(buffer[1]=='t'){
			/*
			ans->data.boolean=1;
			ans->type=BOOLEAN;*/
			return global_true;
		}else if(buffer[1]=='\\'){
			char curchar=buffer[2];
			//prINTf("curchar=%c\n",curchar);
			switch(curchar){
				case 's':
					if(strcmp(buffer+2,"space")==0){
						//ans->data.char_var=' ';
						ans=init_from_char(' ');
						return ans;
					}
					break;
				case 'n':
					if(strcmp(buffer+2,"newline")==0){
						//ans->data.char_var='\n';
						ans=init_from_char('\n');
						return ans;
					}
					break;
				default :
					break;
			}
			//ans->data.char_var=curchar;
			ans=init_from_char(curchar);
			return ans;
		}else{
			INT m=getc_from_port(in);
			if(m=='(' || m=='['){
				general_element rdpair=read_pair(in);
				general_element thepair=internal_cons(quote_vector_symbol,rdpair);
				return thepair;
			}else{
				fprintf(stderr,"Error: unknown expression in read_element;m=%c\n",m);
				ERR_REPORT(1);
			}
		}
	}
	if(issymbol_char(fstc)){
		return init_from_symbol(buffer);
	}
	return global_eof;
}

struct_port make_output_port_from_fp(FILE * fp){
	struct_port ans;
	TYPE_OF_PORT(ans)=FILE_OUT_PORT;
	ans.data.fp=fp;
	ans.gced=0;
	return ans;
}
struct_port make_input_port_from_fp(FILE * fp){
	struct_port ans;
	TYPE_OF_PORT(ans)=FILE_IN_PORT;
	ans.data.fp=fp;
	ans.gced=0;
	return ans;
}
general_element make_input_port_element_from_struct_port(struct_port port){
	general_element ans;
	TYPE_OF(ans)=PORT;
	struct_port * pt=ALLOC(sizeof(struct_port));
	pt[0]=port;
	ans.data.port=pt;
	return ans;
}

general_element internal_close_port(general_element ele){
	if(TYPE_OF(ele)!=PORT){
		fprintf(stderr,"arg of close-port is not a port\n");
		ERR_REPORT(1);
	}
	struct_port * sp=ele.data.port;
	if(sp->isclosed_and_type==CLOSED || sp->data.fp==stdin || sp->data.fp==stdout || sp->data.fp==stderr){
		return global_true;
	}else{
		if(sp->isclosed_and_type==FILE_IN_PORT || sp->isclosed_and_type==FILE_OUT_PORT){ 
			fclose(sp->data.fp);
		}
		sp->isclosed_and_type=CLOSED;
	}
	return global_true;
}
general_element internal_open_output_file(general_element ele){
	//general_element carele=internal_car(ele);
	general_element carele=ele;
	if(TYPE_OF(carele)!=STRING){
		fprintf(stderr,"arg of open-input-file is not a string!\n");
		ERR_REPORT(1);
	}
	
	char * filename=((struct_string*)(carele.data.string))->string_data;
	FILE * in_port=fopen(filename,"w");
	if(in_port==NULL) {
		fprintf(stderr, "Error: could not open file \"%s\"\n", filename);
		return global_false;
		//exit(1);
	}
	return make_input_port_element_from_struct_port(make_output_port_from_fp(in_port));
}
general_element internal_open_input_file(general_element ele){
	//general_element carele=internal_car(ele);
	general_element carele=ele;
	if(TYPE_OF(carele)!=STRING){
		fprintf(stderr,"arg of open-input-file is not a string!\n");
		ERR_REPORT(1);
	}
	
	char * filename=((struct_string*)(carele.data.string))->string_data;
	FILE * in_port=fopen(filename,"r");
	if(in_port==NULL) {
		fprintf(stderr, "Error: could not open file \"%s\"\n", filename);
		return global_false;
		//exit(1);
	}
	return make_input_port_element_from_struct_port(make_input_port_from_fp(in_port));
}
general_element internal_bin_write32(general_element in,general_element port){
	assert(TYPE_OF(port)==PORT);
	FILE * outfp=((struct_port*)(port.data.port))->data.fp;
	uint32_t u1=in.data.num_int;
	return init_from_int(sizeof(uint32_t)*fwrite(&u1,sizeof(uint32_t),1,outfp));
}

general_element internal_read_from_stdin(){
	struct_port in=make_input_port_from_fp(stdin);
	return read_element(in);
}
general_element read_from_port(general_element in){
	if(TYPE_OF(in)!=PORT){
		fprintf(stderr,"Error: can not read non-port object\n");
		return global_false;
	}
	return read_element(((struct_port*)in.data.port)[0]);
}
general_element internal_isempty(general_element pr){
	return internal_general_iseq(pr, the_empty_list);
}
general_element internal_string_length(general_element str){
	if(TYPE_OF(str)!=STRING){
		fprintf(stderr,"Error: arg of string-length is not string");
		return global_false;
	}
	return init_from_int(((struct_string*)(str.data.string))->length);
}

general_element internal_isfloatnum(general_element ele){
	INT tp=TYPE_OF(ele);
	if(tp==FLOAT_NUM){
		return global_true;
	}else{
		return global_false;
	}
}
general_element internal_isfixnum(general_element ele){
	INT tp=TYPE_OF(ele);
	if(tp==INT_NUM){
		return global_true;
	}else{
		return global_false;
	}
}
general_element internal_iseof(general_element ele){
	INT tp=TYPE_OF(ele);
	if(tp==EOF_OBJECT){
		return global_true;
	}else{
		return global_false;
	}
}
general_element internal_isnumber(general_element ele){
	INT tp=TYPE_OF(ele);
	if(tp==INT_NUM || tp==FLOAT_NUM){
		return global_true;
	}else{
		return global_false;
	}
}
general_element internal_isboolean(general_element ele){
	INT tp=TYPE_OF(ele);
	if(tp==BOOLEAN){
		return global_true;
	}else{
		return global_false;
	}
}
general_element internal_ischar(general_element ele){
	INT tp=TYPE_OF(ele);
	if(tp==CHAR){
		return global_true;
	}else{
		return global_false;
	}
}
general_element internal_isvector(general_element ele){
	INT tp=TYPE_OF(ele);
	if(tp==VECTOR){
		return global_true;
	}else{
		return global_false;
	}
}
general_element internal_isstring(general_element ele){
	INT tp=TYPE_OF(ele);
	if(tp==STRING){
		return global_true;
	}else{
		return global_false;
	}
}
general_element internal_issymbol(general_element ele){
	INT tp=TYPE_OF(ele);
	if(tp==SYMBOL){
		return global_true;
	}else{
		return global_false;
	}
}
general_element internal_write_char(general_element ele,general_element fp){
	FILE * outfp=((struct_port*)(fp.data.port))->data.fp;

	assert(TYPE_OF(ele)==CHAR);
	fprintf(outfp,"%c",ele.data.character);
	return global_true;
}
general_element internal_write_string(general_element ele,general_element fp){
	FILE * outfp=((struct_port*)(fp.data.port))->data.fp;

	assert(TYPE_OF(ele)==STRING);
	fwrite(((struct_string*)(ele.data.string))->string_data,sizeof(char),((struct_string*)(ele.data.string))->length,outfp);
	//fprintf(outfp,"%s",((struct_string*)(ele.data.string))->string_data);
	return global_true;
}
general_element internal_write_string_to_stdout(general_element ele){
	assert(TYPE_OF(ele)==STRING);
	fprintf(stdout,"%s",((struct_string*)(ele.data.string))->string_data);
	return global_true;
}
general_element internal_fun_eq(general_element a,general_element b){
	general_element ans;
	TYPE_OF(ans)=BOOLEAN;
	if(TYPE_OF(a)==VECTOR&& TYPE_OF(b)==VECTOR){
		ans.data.num_int=(((general_vector*)(a.data.ge_vector))->data->data.function==((general_vector*)(b.data.ge_vector))->data->data.function);
	}else{
		ans.data.num_int=0;
	}
	return ans;
}
general_element internal_get_build_in_ports (general_element n);
general_element write_stderr(general_element a){
	PUSH(a);
	general_element fp=internal_get_build_in_ports(init_from_int(2));
	POP(a);
	return internal_write(a,fp);
}
general_element write_stdout(general_element a){
	PUSH(a);
	general_element fp=internal_get_build_in_ports(init_from_int(1));
	POP(a);
	return internal_write(a,fp);
}
INT get_num_args_of_function(general_element a){
	return TYPE_OF(a)/2;
}
INT get_islast_pair_arg_of_function(general_element a){
	return TYPE_OF(a)&1;
}
INT list_length(general_element lst){
	INT ans=0;
	while(internal_isempty(lst).data.num_int!=1){
		lst=internal_cdr(lst);
		ans++;
	}
	return ans;
}

general_element internal_make_new_type(general_element oldele, general_element num){
	TYPE_OF(oldele)=num.data.num_int;
	return oldele;
}

general_element internal_quotient(general_element a,general_element b);
general_element internal_hash_string(general_element a);

general_element internal_get_build_in_ports (general_element n){
	INT dat=n.data.num_int;
	switch (dat){
		case 0:
			return make_input_port_element_from_struct_port(make_input_port_from_fp(stdin));
			break;
		case 1:
			return make_input_port_element_from_struct_port(make_output_port_from_fp(stdout));
			break;
		case 2:
			return make_input_port_element_from_struct_port(make_output_port_from_fp(stderr));
			break;
		default:
			return global_false;
	}
}
general_element internal_str2list(general_element str){
	if(TYPE_OF(str)!=STRING){
		fprintf(stderr,"type=%ld,should be %d\n",TYPE_OF(str),STRING);
		fprintf(stderr,"str is not a string in str2list.\n");
		assert(0);
		return the_empty_list;
	}else{
		general_element ans=the_empty_list;
		char * pstr_c1=((struct_string*)(str.data.string))->string_data;
		INT len=((struct_string*)(str.data.string))->length;
		char * pstr=malloc(sizeof(char*)*(len+1));
		strcpy(pstr,pstr_c1);
		char * endc=pstr+len-1;
		while(endc>=pstr){
			ans=internal_cons(init_from_char(endc[0]),ans);
			endc--;
		}
		free(pstr);
		return ans;
	}
}
general_element init_from_byte(char * a,INT length){
	general_element ans;
	TYPE_OF(ans)=STRING;
	ans.data.string=ALLOC(sizeof(struct_string));
	((struct_string*)ans.data.string)->length=0;
	((struct_string*)ans.data.string)->gced=0;
	INT len=length;
	PUSH(ans);
	char * data=ALLOC(sizeof(char)*(len+1));
	POP(ans);
	((struct_string*)ans.data.string)->string_data=data;
	((struct_string*)ans.data.string)->length=len;
	TYPE_OF(ans)=STRING;
	memcpy(((struct_string*)ans.data.string)->string_data,a,length);
	((struct_string*)ans.data.string)->string_data[length]=0;
	return ans;
}

general_element internal_list2bytestring(general_element lst){
	INT len=list_length(lst);
	char * str=malloc(sizeof(char)*(len+1));
	INT i=0;
	while(TYPE_OF(lst)!=EMPTY_LIST){
		general_element carlst=internal_car(lst);
		assert(TYPE_OF(carlst)==CHAR);
		str[i]=carlst.data.character;
		i++;
		lst=internal_cdr(lst);
	}
	str[i]=0;
	general_element ret=init_from_byte(str,len);
	free(str);
	return ret;
}
general_element internal_list2str(general_element lst){
	INT len=list_length(lst);
	char * str=malloc(sizeof(char)*(len+1));
	INT i=0;
	while(TYPE_OF(lst)!=EMPTY_LIST){
		general_element carlst=internal_car(lst);
		assert(TYPE_OF(carlst)==CHAR);
		str[i]=carlst.data.character;
		i++;
		lst=internal_cdr(lst);
	}
	str[i]=0;
	general_element ret=init_from_string(str);
	free(str);
	return ret;
}
general_element internal_symbol2str(general_element sym){
	assert(TYPE_OF(sym)==SYMBOL);
	INT len=((struct_string*)(sym.data.string))->length;
	char * str=malloc(sizeof(char)*(len+1));
	memcpy(str,((struct_string*)(sym.data.string))->string_data,len+1);
	general_element ans=init_from_string(str);
	free(str);
	return ans;
}
general_element internal_str2symbol(general_element sym){
	assert(TYPE_OF(sym)==STRING);
	INT len=((struct_string*)(sym.data.string))->length;
	char * str=malloc(sizeof(char)*(len+1));
	memcpy(str,((struct_string*)(sym.data.string))->string_data,len+1);
	general_element ans=init_from_symbol(str);
	free(str);
	return ans;
}
general_element internal_num2str(general_element input){
	char str[128];
	if(TYPE_OF(input)==INT_NUM){
		sprintf(str,"%ld",input.data.num_int);
	}else if(TYPE_OF(input)==FLOAT_NUM){
		sprintf(str,"%.16e",input.data.num_float);
	}else{
		str[0]=0;
	}
	general_element ans=init_from_string(str);
	return ans;
}

