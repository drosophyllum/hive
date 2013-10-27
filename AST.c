#include<stdio.h>
#include "AST.h"
#include "Runtime.h"
#include "Global.h"
#include <errno.h>
#include <pthread.h>
#include <readline/readline.h>
#include <readline/history.h>
#include <regex.h>
#include <signal.h>
#include <time.h>
#include <sys/socket.h>
#include <netinet/in.h>

struct Arrow* topnode = NULL;

regex_t injection;
regex_t query;

void null(struct Arrow* arr);
void scrapeNodes(struct Symbol* symb);
void printAST(struct Arrow* arr);
void printbinds(struct Symbol* bind,bool list);
void traverse(void (*arrow)(struct Arrow*) , void (*symbol)(struct Symbol*),struct Arrow* top);
void traverseBind(void (*symbol)(struct Symbol*),struct Symbol* bind);
void initPropagators(struct Arrow* top);
void initPropagatorRing();
void* threadMain(void* param);
int binds(struct Propagator* prop,struct NodeValue* synapse);
int transmit(struct Propagator* propagator,struct NodeValue* transmiter);
void repl();
void tcpServer();
void lineParse(char * line);
void inject(char* node, char* value);
void registerVariable(struct Propagator* prop, char* name, char*value);
char* aquireVariable(struct Propagator* prop, char* name);
unsigned long int binder = 0 ; 


struct NodeValue* generateSynapse(struct Symbol*);
struct NodeValue* generateTransmit(struct Symbol*);
struct Propagator* PTABLE = NULL;
struct Node* NTBL = NULL;
struct Node* lookupNode(char * name);
pthread_t executers[10];

void main(){
        char *file = "obama.hive";
        initRuntime(file);
	initPropagatorRing();
	int i;	
	
	for (i = 0; i<1; i++) {
		pthread_create(&executers[i], NULL, &threadMain, NULL);	
	}
	if (regcomp(&injection, "(\\w+)\\.(\\w+)",REG_EXTENDED)) {
		fprintf(stderr, "Could not compile regex\n"); exit(1); 
	}if (regcomp(&query, "(\\w+)?",REG_EXTENDED)) {
		fprintf(stderr, "Could not compile regex\n"); exit(1); 
	}
//	inject("mother1","Z");

//	inject("mother2","adam");
//	repl();
//
	tcpServer();
}

void tcpServer(){
   int listenfd,connfd,n;
   struct sockaddr_in servaddr,cliaddr;
   socklen_t clilen;
   pid_t     childpid;
   char mesg[1000];

   listenfd=socket(AF_INET,SOCK_STREAM,0);

   bzero(&servaddr,sizeof(servaddr));
   servaddr.sin_family = AF_INET;
   servaddr.sin_addr.s_addr=htonl(INADDR_ANY);
   servaddr.sin_port=htons(7892);
   bind(listenfd,(struct sockaddr *)&servaddr,sizeof(servaddr));

   listen(listenfd,1024);

   for(;;)
   {
      clilen=sizeof(cliaddr);
      connfd = accept(listenfd,(struct sockaddr *)&cliaddr,&clilen);
      close(listenfd);
         for(;;)
         {
            n = recvfrom(connfd,mesg,1000,0,(struct sockaddr *)&cliaddr,&clilen);
            sendto(connfd,mesg,n,0,(struct sockaddr *)&cliaddr,sizeof(cliaddr));
            mesg[n] = '\n';
	    mesg[n+1] = 0;
	    lineParse(mesg);
         }
         
      close(connfd);
   }
}


void repl(){	
	char* line;
	while(line = readline(">>")){
		lineParse(line);
		printf("\n");
	}
}


void lineParse(char * line){
	regmatch_t matches[5];
	if(regexec(&injection,line,5,&matches,0)){
		printf("not understood");
		return;
	}else{
		line[matches[1].rm_eo]='\0'; 
		line[matches[2].rm_eo]='\0'; 
		char * node = line+matches[1].rm_so;
		char * value = line+matches[2].rm_so;	
		printf("%s injected with value %s",node,value);
		inject(node,value);
	}
}

void inject(char* node, char * value){
		struct Node*  nodeptr = lookupNode(node);
		if(!nodeptr){
			printf("\n ## Node %s not found!!!", node);
		}
		struct PropagatorList* iterDep;
		for(iterDep = nodeptr->connected; iterDep; iterDep = iterDep->next){
			pthread_mutex_lock(&iterDep->ref->runLock);
			struct NodeValue* iterSyn;
			for(iterSyn=iterDep->ref->synapse; iterSyn; iterSyn = iterSyn->next){
				if(nodeptr == iterSyn->node){
					struct Valuelist *needle;
					needle = (struct Valuelist*)malloc(sizeof(struct Valuelist));
					memset(needle, 0 , sizeof(struct Valuelist));
					needle->value = value; //change for reflexivity
					needle-> next = iterSyn->values;
					iterSyn->values = needle;
					break;
				}
			}
			for(iterSyn=iterDep->ref->transmit; iterSyn; iterSyn = iterSyn->next){
				if(nodeptr == iterSyn->node){
					struct Valuelist *needle;
					needle = (struct Valuelist*)malloc(sizeof(struct Valuelist));
					memset(needle, 0 , sizeof(struct Valuelist));
					needle->value = value; //change for reflexivity
					needle-> next = iterSyn->values;
					iterSyn->values = needle;
					break;
				}
			}
			pthread_mutex_unlock(&iterDep->ref->runLock);		
		}
}

void initPropagatorRing(){
	struct Propagator* iter,*last;
	for(iter = PTABLE ; iter !=NULL; iter = iter->next){
		struct NodeValue* iterNode;
		for (iterNode=iter->synapse; iterNode; iterNode = iterNode->next){
			struct PropagatorList* needle;
			needle = (struct PropagatorList*) malloc(sizeof(struct PropagatorList));
			memset(needle, 0 , sizeof(struct PropagatorList));
			needle->ref = iter;
			needle-> next = iterNode->node->connected;
			iterNode->node->connected = needle;
		}for (iterNode=iter->transmit; iterNode; iterNode = iterNode->next){
			struct PropagatorList* needle;
			needle = (struct PropagatorList*) malloc(sizeof(struct PropagatorList));
			memset(needle, 0 , sizeof(struct PropagatorList));
			needle->ref = iter;
			needle-> next = iterNode->node->connected;
			iterNode->node->connected = needle;
		}
		last = iter;
	}
	last->next = PTABLE;
}



void* threadMain(void* param){
	struct Propagator* proc;
	for(proc = PTABLE; proc ; proc= proc->next){ //ring 
		if ( pthread_mutex_trylock(&proc->runLock) == EBUSY)
			continue;
		if (binds(proc, proc->synapse)){
			pthread_mutex_unlock(&proc->runLock);  // never hold two locks!
			binder++;
			printf(" => ");
			transmit(proc,proc->transmit);		// acquires other lock.
			printf("\n");
			
		}else{
			pthread_mutex_unlock(&proc->runLock);   // otherwise, release lock anyways.
		}
		if ( pthread_mutex_trylock(&proc->runLock) == EBUSY)
			continue;
		if (binds(proc, proc->transmit)){
			pthread_mutex_unlock(&proc->runLock);  // never hold two locks!
			binder++;
			printf(" => ");
			transmit(proc,proc->synapse);		// acquires other lock.
			printf("\n");
			
		}else{
			pthread_mutex_unlock(&proc->runLock);   // otherwise, release lock anyways.
		}
		
	}
	return NULL;
}


// add non determinism
int binds(struct Propagator* propagator,struct NodeValue* synapse){
	struct NodeValue* iter;
	for (iter=synapse; iter; iter = iter->next){
		struct Valuelist* valiter;
		bool bound=false;
		for (valiter=iter->values; valiter; valiter = valiter->next){
			if (iter->isVar ||(!strcmp(iter->bindsTo,valiter->value))){
				bound = true;
				break;
			}
			else if (isupper((int)*valiter->value))  { //transmit VARAIBLE
				bound = true;
				break;
			}
		}
		if (!bound)
			return 0;
	}
	printf("BIND: " );
	for (iter=synapse; iter; iter = iter->next){
		printf(" %s.%s",iter->node->name,iter->values->value);
		struct Valuelist* valiter, *last;
		last=NULL;
		for (valiter=iter->values; valiter; valiter = valiter->next){
			if (iter->isVar || (!strcmp(iter->bindsTo,valiter->value)) || isupper((int)*valiter->value)){
				if(iter->isVar){ //is variable!
					registerVariable(propagator,iter->bindsTo,valiter->value);
				}
				if (isupper((int)*valiter->value))  { //transmit VARAIBLE
					registerVariable(propagator, iter->bindsTo,valiter->value);
				}
				if (!last){
					iter->values = valiter->next;
				}else{	
					last->next= valiter->next;
				}
				free(valiter);
				break;
			}
			last=valiter;
			
		}
	}		
	return 1;
}

void registerVariable(struct Propagator* prop, char* name, char*value){
	struct VariableMap* iter;
	for(iter=prop->variables;iter; iter=iter->next){
		if(!strcmp(iter->name,name)){
			iter->value = value;
			return;
		}
	}
	iter = (struct VariableMap*) malloc(sizeof(struct VariableMap));
	iter->name = name;
	iter->value = value;
	iter->next = prop->variables ;
	prop->variables = iter;
	return; 
}
char* acquireVariable(struct Propagator* prop, char* name){
	struct VariableMap* iter;
	for(iter=prop->variables;iter; iter=iter->next){
		if(!strcmp(iter->name,name)){
			return iter->value;
		}
	}
	return NULL;	
}

int transmit(struct Propagator* propagator,struct NodeValue* transmiter){
	struct NodeValue* iter;
	for (iter = transmiter; iter ; iter = iter->next) {
		char* tmp;
		struct PropagatorList* iterDep;
		printf("%s.%s ",iter->node->name ,  (iter->values && iter->values->value)? acquireVariable(propagator, iter->bindsTo): iter->bindsTo );
		for(iterDep = iter->node->connected; iterDep; iterDep = iterDep->next){
			if (iterDep->ref == propagator)
				continue;
			pthread_mutex_lock(&iterDep->ref->runLock);
			struct NodeValue* iterSyn;
			for(iterSyn=iterDep->ref->synapse; iterSyn; iterSyn = iterSyn->next){
				if(iter->node == iterSyn->node){
					struct Valuelist *needle;
					needle = (struct Valuelist*)malloc(sizeof(struct Valuelist));
					memset(needle, 0 , sizeof(struct Valuelist));
					char* variable = acquireVariable(propagator, iter->bindsTo);
					if (variable){
						needle->value= variable;
					}else if(iter->isVar){
						needle->value = acquireVariable(propagator,iter->bindsTo);
					}else{
						needle->value = iter->bindsTo; //change for reflexivity
					}
					needle-> next = iterSyn->values;
					iterSyn->values = needle;
					break;
				}
			}
			for(iterSyn=iterDep->ref->transmit; iterSyn; iterSyn = iterSyn->next){
				if(iter->node == iterSyn->node){
					struct Valuelist *needle;
					needle = (struct Valuelist*)malloc(sizeof(struct Valuelist));
					memset(needle, 0 , sizeof(struct Valuelist));
					char* variable = acquireVariable(propagator, iter->bindsTo);
					if (variable) {
						needle->value = variable;
					}else if(iter->isVar){
						needle->value = acquireVariable(propagator,iter->bindsTo);
					}else{
						needle->value = iter->bindsTo; //change for reflexivity
					}
					needle-> next = iterSyn->values;
					iterSyn->values = needle;
					break;
				}
			}
			pthread_mutex_unlock(&iterDep->ref->runLock);		
		}
	}
}

void initNode(char* elem){
        struct Node *iter;
        for(iter = NTBL; iter != NULL; iter=iter->next){
                if (strcmp(iter->name,elem) == 0 ){
                        return;
                }
        }
        iter = NTBL; 
        NTBL = (struct Node*) malloc(sizeof(struct Node)); 
        memset(NTBL, 0,sizeof(struct Node));    
        NTBL->name = elem;
        NTBL->next = iter;
}


int initRuntime(char* file){
	FILE *myfile = fopen(file, "r");
	struct Arrow *d;
	d = parse(myfile);
//update nodetable
	traverse(&null,&scrapeNodes,d); 
//initialize progagator table
	initPropagators(d);
	return d;
}

void initPropagators(struct Arrow* iter){
	struct Propagator* needle;
	for(; iter != NULL; iter=iter->next){
		needle = (struct Propagator*)malloc(sizeof(struct Propagator));
		memset(needle,0,sizeof(struct Propagator));
		pthread_mutex_init(&needle->runLock, NULL);
		needle->synapse = generateSynapse(iter->inBind);
		needle->transmit = generateSynapse(iter->outBind);
		needle->next = PTABLE;
		PTABLE = needle;	
	}
}

struct NodeValue* generateSynapse(struct Symbol* s){
	if(!s)
		return NULL;

	struct NodeValue* synapse = (struct NodeValue*)	malloc(sizeof(struct NodeValue));
	struct NodeValue *tail;
	memset(synapse,0,sizeof(struct NodeValue));
	synapse->node = lookupNode(s->node);
	if(! s->isVariable){
		synapse->bindsTo = s->name;
		synapse->isVar = 0;
	}else{
		synapse->bindsTo = s->name;
		synapse->isVar = 1 ;
	}
	synapse->next = generateSynapse(s->children);
	if (synapse->next){
		for(tail =synapse->next; tail->next !=NULL; tail = tail->next);
		tail->next = generateSynapse(s->next);
	}else{
		synapse->next = generateSynapse(s->next);
	}
	return synapse;
}
struct NodeValue* generateTransmit(struct Symbol* s){
	return NULL;
}

struct Node* lookupNode(char* elem){
        struct Node *iter;
        for(iter = NTBL; iter != NULL; iter=iter->next){
                if (strcmp(iter->name,elem) == 0 ){
                        return iter;
                }
        }
}





void printAST(struct Arrow* arr){
	struct Arrow* iter;
	for(iter=arr; iter != NULL; iter=iter->next){
	    printbinds(arr->inBind,false);
	    printf(" => ");
	    printbinds(arr->outBind,false);
	    printf("\n");
	}	
}

void printbinds(struct Symbol* bind,bool list){
	struct Symbol* iter;
	for(iter=bind; iter != NULL; iter=iter->next){
		printf("%s.%s ",iter->node,iter->name);
		if (iter->children){
			printf("(");
			printbinds(iter->children,true);
			printf(")");
		}
		if (list && iter->next){
			printf(",");}
		
	}
}


void null(struct Arrow* arr){
	return;
}

void scrapeNodes(struct Symbol* symb){
	initNode(symb->node);
}



void traverse(void (*arrow)(struct Arrow*) , void (*symbol)(struct Symbol*),struct Arrow* top){
	struct Arrow* arrIter;
	for(arrIter = top; arrIter != NULL; arrIter = arrIter->next){
		arrow(arrIter);
		traverseBind(symbol, arrIter-> inBind);
		traverseBind(symbol, arrIter-> outBind);
	}
}

void traverseBind(void (*symbol)(struct Symbol*),struct Symbol* bind){
	struct Symbol* symbIter;
	for(symbIter=bind; symbIter != NULL; symbIter=symbIter->next){
		symbol(symbIter);
		if (symbIter->children){
			traverseBind(symbol,symbIter->children);
		}
		if (symbIter->next){
			traverseBind(symbol, symbIter-> children);
		}	
	}
}
