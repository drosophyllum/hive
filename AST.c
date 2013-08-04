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

struct Arrow* topnode = NULL;

regex_t regex;

void null(struct Arrow* arr);
void scrapeNodes(struct Symbol* symb);
void printAST(struct Arrow* arr);
void printbind(struct Symbol* bind,bool list);
void traverse(void (*arrow)(struct Arrow*) , void (*symbol)(struct Symbol*),struct Arrow* top);
void traverseBind(void (*symbol)(struct Symbol*),struct Symbol* bind);
void initPropagators(struct Arrow* top);
void initPropagatorRing();
void* threadMain(void* param);
int bind(struct Propagator* prop,struct NodeValue* synapse);
int transmit(struct Propagator* propagator,struct NodeValue* transmiter);
int feedback(struct Propagator* propagator,struct NodeValue* transmiter);
void repl();
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
        char *file = "test.hive";
        initRuntime(file);
	initPropagatorRing();
	int i;	
	
//	for (i = 0; i<10; i++) {
//		pthread_create(&executers[i], NULL, &threadMain, NULL);	
//	}
//	if (regcomp(&regex, "(\\w+)\\.(\\w+)",REG_EXTENDED)) {
//		fprintf(stderr, "Could not compile regex\n"); exit(1); 
//	}
	inject("x","up");
	threadMain(NULL);
	repl();
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
	if(regexec(&regex,line,5,&matches,0)){
		printf("not understood");
		return;
	}
	line[matches[1].rm_eo]='\0'; 
	line[matches[2].rm_eo]='\0'; 
	char * node = line+matches[1].rm_so;
	char * value = line+matches[2].rm_so;	
	printf("%s injected with value %s",node,value);
	inject(node,value);
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
			pthread_mutex_unlock(&iterDep->ref->runLock);		
		}
}

void initPropagatorRing(){
	struct Propagator* iter,*last;
	for(iter = PTABLE ; iter !=NULL; iter = iter->next){
		struct NodeValue* iterNode;
		for (iterNode=iter->synapse; iterNode; iterNode = iterNode->next){
			struct PropagatorList* iterDep,*needle;
			for (iterDep=iterNode->node->connected;iterDep;iterDep=iterDep->next);
			iterDep; // now the last node
			needle = (struct PropagatorList*) malloc(sizeof(struct PropagatorList));
			memset(needle, 0 , sizeof(struct PropagatorList));
			needle-> next = iterDep;
			needle->ref = iter;
			iterNode->node->connected = needle;
		}for (iterNode=iter->transmit; iterNode; iterNode = iterNode->next){
			struct PropagatorList* iterDep,*needle;
			for (iterDep=iterNode->node->receive;iterDep;iterDep=iterDep->next);
			iterDep; // now the last node
			needle = (struct PropagatorList*) malloc(sizeof(struct PropagatorList));
			memset(needle, 0 , sizeof(struct PropagatorList));
			needle-> next = iterDep;
			needle->ref = iter;
			iterNode->node->receive = needle;
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
		if (bind(proc, proc->synapse)){
			pthread_mutex_unlock(&proc->runLock);  // never hold two locks!
			binder++;
			printf("# %lu \n",binder);
			transmit(proc,proc->transmit);		// acquires other lock.
			
		}else{
			pthread_mutex_unlock(&proc->runLock);   // otherwise, release lock anyways.
		}
		if ( pthread_mutex_trylock(&proc->runLock) == EBUSY)
			continue;
		if (bind(proc, proc->transmit)){
			pthread_mutex_unlock(&proc->runLock);  // never hold two locks!
			binder++;
			printf("# %lu \n",binder);
			feedback(proc,proc->synapse);		// acquires other lock.
			
		}else{
			pthread_mutex_unlock(&proc->runLock);   // otherwise, release lock anyways.
		}
		
	}
	return NULL;
}


// add non determinism
int bind(struct Propagator* propagator,struct NodeValue* synapse){
	struct NodeValue* iter;
	for (iter=synapse; iter; iter = iter->next){
		struct Valuelist* valiter;
		bool bound=false;
		for (valiter=iter->values; valiter; valiter = valiter->next){
			if (iter->isVar || (!strcmp(iter->bindsTo,valiter->value))){
				bound = true;
				break;
			}
		}
		if (!bound)
			return 0;
	}
	for (iter=synapse; iter; iter = iter->next){
		struct Valuelist* valiter, *last;
		last=NULL;
		for (valiter=iter->values; valiter; valiter = valiter->next){
			if (iter->isVar || (!strcmp(iter->bindsTo,valiter->value))){
				char *valuename = iter->node->name;
				if(iter->isVar){ //is variable!
					registerVariable(propagator,valuename,valiter->value);
				}
				if (!last){
					iter->values = valiter->next;
				}else{	
					last->next= valiter->next;
				}
				free(valiter);
				continue;
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
	iter->next = (prop->variables)? prop->variables->next : NULL;
	prop->variables = iter->next;
	return; 
}
char* acquireVariable(struct Propagator* prop, char* name){
	struct VariableMap* iter;
	for(iter=prop->variables;iter; iter=iter->next){
		if(!strcmp(iter->name,name)){
			return iter->value;
		}
	}	
}

int transmit(struct Propagator* propagator,struct NodeValue* transmiter){
	struct NodeValue* iter;
	for (iter = transmiter; iter ; iter = iter->next) {
		struct PropagatorList* iterDep;
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
					if(iter->isVar){
						needle->value = acquireVariable(propagator,iter->node->name);
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
int feedback(struct Propagator* propagator,struct NodeValue* transmiter){
	struct NodeValue* iter;
	for (iter = transmiter; iter ; iter = iter->next) {
		struct PropagatorList* iterDep;
		for(iterDep = iter->node->receive; iterDep; iterDep = iterDep->next){	
			if (iterDep->ref == propagator)
				continue;
			pthread_mutex_lock(&iterDep->ref->runLock);
			struct NodeValue* iterSyn;
			for(iterSyn=iterDep->ref->synapse; iterSyn; iterSyn = iterSyn->next){
				if(iter->node == iterSyn->node){
					struct Valuelist *needle;
					needle = (struct Valuelist*)malloc(sizeof(struct Valuelist));
					memset(needle, 0 , sizeof(struct Valuelist));
					if(iter->isVar){
						needle->value = acquireVariable(propagator,iter->node->name);
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
	    printbind(arr->inBind,false);
	    printf(" => ");
	    printbind(arr->outBind,false);
	    printf("\n");
	}	
}

void printbind(struct Symbol* bind,bool list){
	struct Symbol* iter;
	for(iter=bind; iter != NULL; iter=iter->next){
		printf("%s.%s ",iter->node,iter->name);
		if (iter->children){
			printf("(");
			printbind(iter->children,true);
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
