#pragma once
#include<pthread.h>

int initRuntime(char* file);

struct Node 	{
		char* name;
		struct PropagatorList* receive ;
		struct PropagatorList* connected ;
		struct Node* next;
		};

struct Valuelist 	{
			 	char* value;
				struct Valuelist* next;
			};

struct Propagator 	{
			pthread_mutex_t runLock;
			struct NodeValue* synapse;
			struct VariableMap* variables;
			struct NodeValue* transmit;
			struct Propagator* next;
			};

struct PropagatorList      {
				struct Propagator* ref;
				struct PropagatorList* next;
			};

struct NodeValue{
	struct Node* node;
	struct Valuelist* values;
	char* bindsTo;
	int isVar;
	struct NodeValue* next;
	};


struct VariableMap {
		char* name;
		char* value;
		char* next;	
	};

void initNode(char* elem);
