
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "as.h"
#include "output.h"
#include "util.h"
#include "ffwd.h"
#include "do.h"
#include "ffwd.h"
#include "pseudo.h"
#include "symtab.h"
#include "globals.h"

void initialize(void);
void make_pass(void);
void re_init(void);
void process(void);
int parse_line(void);
void write_s9_record(void);

/*
	as ---	cross assembler main program
 */
int main(int argc, char *argv[])
{
	char	**np;
	char	*i;
	FILE	*fopen();
	int	j = 0;

	if(argc < 2){
		printf("Usage: %s [files]\n",argv[j]);
		exit(1);
		}
	  Argv = argv;
	  initialize();
	  while ((*argv[j] != '-') && (j<argc))
	  {
	   j++;
	   if (j == argc) break;
	  }
	  N_files = j-1;
	 if (j < argc )
	  {
	  argv[j]++;
	  while (j<argc)
	   {
	   for (i = argv[j]; *i != 0; i++)
	     if ((*i <= 'Z') && (*i >= 'A'))
	       *i = *i + 32;
	   if (strcmp(argv[j],"l")==0)
	     Lflag = 1;
	   else if (strcmp(argv[j],"nol")==0)
	     Lflag = 0;
	   else if (strcmp(argv[j],"c")==0)
	      Cflag = 1;
	   else if (strcmp(argv[j],"noc")==0)
	     Cflag = 0;
	   else if (strcmp(argv[j],"s")==0)
	     Sflag = 1;
	   else if (strcmp(argv[j],"cre")==0)
	     CREflag = 1;
	    j++;
	   }
	  }
	root = NULL;

	Cfn = 0;
	np = argv;
	Line_num = 0; /* reset line number */
	while( ++Cfn <= N_files )
		if((Fd = fopen(*++np,"r")) == NULL)
			printf("as: can't open %s\n",*np);
		else{
			make_pass();
			fclose(Fd);
		}
	if( Err_count == 0 ){
		Pass++;
		re_init();
		Cfn = 0;
		np = argv;
		Line_num = 0;
		while( ++Cfn <= N_files)
			if((Fd = fopen(*++np,"r")) != NULL)
			    {
				make_pass();
				fclose(Fd);
			     }
			if (Sflag == 1)
			  {
			    printf ("\f");
			    stable (root);
			  }
			if (CREflag == 1)
			  {
			    printf ("\f");
			    cross (root);
			  }
		write_s9_record();
		}
	exit(Err_count);
}

void write_s9_record(void)
{
	int addr;
	int chksum;

	addr = Xfer_addr & 0xFFFF;
	chksum = 3 + (addr >> 8) + lobyte(addr);
	chksum = ~chksum;

	fprintf(Objfil,"S9");
	hexout(3);
	hexout(addr >> 8);
	hexout(addr);
	hexout(chksum);
	fprintf(Objfil,"\n");
}

void initialize(void)
{
	FILE	*fopen();
	char	*src;
	char	*last_slash;
	char	*base;
	char	*last_dot;

#ifdef DEBUG
	printf("Initializing\n");
#endif
	Err_count = 0;
	Pc	  = 0;
	Pass	  = 1;
	Lflag	  = 0;
	Cflag	  = 0;
	Ctotal	  = 0;
	Sflag	  = 0;
	CREflag   = 0;
	N_page	  = 0;
	Xfer_addr = 0;
	Line[MAXBUF-1] = NEWLINE;

	src = Argv[1];
	last_slash = strrchr(src,'/');
	if( last_slash == NULL )
		base = src;
	else
		base = last_slash + 1;
	strncpy(Obj_name,base,MAXBUF-1);
	Obj_name[MAXBUF-1] = EOS;
	base = Obj_name;
	last_dot = strrchr(base,'.');
	if( last_dot != NULL && last_dot != base )
		*last_dot = EOS;
	strncat(Obj_name,".s19",MAXBUF-1-strlen(Obj_name));
	if( (Objfil = fopen(Obj_name,"w")) == NULL)
		fatal("Can't create object file");
	fwdinit();	/* forward ref init */
	localinit();	/* target machine specific init. */
}

void re_init(void)
{
#ifdef DEBUG
	printf("Reinitializing\n");
#endif
	Pc	= 0;
	E_total = 0;
	P_total = 0;
	Ctotal	= 0;
	N_page	= 0;
	fwdreinit();
}

void make_pass(void)
{
	char	*fgets();

#ifdef DEBUG
	printf("Pass %d\n",Pass);
#endif
	while( fgets(Line,MAXBUF-1,Fd) != (char *)NULL ){
		Line_num++;
		P_force = 0;	/* No force unless bytes emitted */
		N_page = 0;
		   if(parse_line())
			process();
		if(Pass == 2 && Lflag && !N_page)
			print_line();
		P_total = 0;	/* reset byte count */
		Cycles = 0;	/* and per instruction cycle count */
		}
	f_record();
}


/*
 *	parse_line --- split input line into label, op and operand
 */
int parse_line(void)
{
	register char *ptrfrm = Line;
	register char *ptrto = Label;
	char	*skip_white();

	if( *ptrfrm == '*' || *ptrfrm == '\n' )
		return(0);	/* a comment line */

	while( delim(*ptrfrm)== NO )
		*ptrto++ = *ptrfrm++;
	if(*--ptrto != ':')ptrto++;     /* allow trailing : */
	*ptrto = EOS;

	ptrfrm = skip_white(ptrfrm);

	ptrto = Op;
	while( delim(*ptrfrm) == NO)
		*ptrto++ = mapdn(*ptrfrm++);
	*ptrto = EOS;

	ptrfrm = skip_white(ptrfrm);

	ptrto = Operand;
	while( *ptrfrm != NEWLINE )
		*ptrto++ = *ptrfrm++;
	*ptrto = EOS;

#ifdef DEBUG
	printf("Label-%s-\n",Label);
	printf("Op----%s-\n",Op);
	printf("Operand-%s-\n",Operand);
#endif
	return(1);
}

/*
 *	process --- determine mnemonic class and act on it
 */
void process(void)
{
	register struct oper *i;
	struct oper *mne_look();

	Old_pc = Pc;		/* setup `old' program counter */
	Optr = Operand; 	/* point to beginning of operand field */

	if(*Op==EOS){		/* no mnemonic */
		if(*Label != EOS)
			install(Label,Pc);
		}
	else if( (i = mne_look(Op))== NULL)
		error("Unrecognized Mnemonic");
	else if( i->class == PSEUDO )
		do_pseudo(i->opcode);
	else{
		if( *Label )install(Label,Pc);
		if(Cflag)Cycles = i->cycles;
		do_op(i->opcode,i->class);
		if(Cflag)Ctotal += Cycles;
		}
}
