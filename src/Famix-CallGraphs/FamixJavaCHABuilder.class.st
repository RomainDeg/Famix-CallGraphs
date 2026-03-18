"
I am a class used to build a CHA call graph for a Moose java model.

To be used you need to define entry points for your application lake this:

```st
	(FamixJavaCHABuilder entryPoints: (model allMethods select: [ :method | method name = 'main' ])) build
```

In case the program to analyze is using reflectivity, we might miss some edges. If the user knows some edges to add, it is possible to add them using the #reflectiveHook variable. 
For example:

```st
	(FamixJavaCHABuilder entryPoints: (model allMethods select: [ :method | method name = 'main' ]))
	reflectiveHook: [ :node :builder |
			(node kindName = 'Toto' and: [ node methodName = 'myMethod' ]) ifTrue: [
					node addCallee: (builder nodeForMethodSignature: 'myOtherMethod(String)' kind: (model allClasses detect: [ :class | class name = 'Titi' ]) stub: false) ] ];
	build
```

## Options

The algo provides some options. 

### Max Depth
 
It is possible to set a max depth to not build the full CallGraph but stop at a maximum depth. 

```st
	(FamixJavaCHABuilder entryPoints: (model allMethods select: [ :method | method name = 'main' ]))
		maxDepth: 10; ""Will build 10 nodes depth""
		build
```

### Reflective hook

Sometimes we have reflective calls that we cannot find in the call graph. 
If the user knows what is invoked, they can use #reflectiveHook: to add the missing nodes ""by hand""

# Caching

The algo is building some caches in the caches of the entities. Those caches are kept after building a call graph in case multiple needs to be built. 

If you wish to flush the caches to same some memory once the call graph is built you can execute:

```st
	model resetCallGraphCaches
```

# Implementation detail

Originaly the implementation was using an `OrderedCollection` for the worklist and a `Set` for the visited list. But to check if we already have a node created for a method and kind it was taking a lot of time.
Now the implementation is using two `Dictionary` and is using a hash for key. This is here for performance reasons. 
This made a run go from 25min to 2min.

For performance I also cache the possible runtime types of the types since we access it a lot.
"
Class {
	#name : 'FamixJavaCHABuilder',
	#superclass : 'FamixAbstractCallGraphBuilder',
	#instVars : [
		'visited',
		'worklist',
		'reflectiveHook',
		'typesMap'
	],
	#category : 'Famix-CallGraphs',
	#package : 'Famix-CallGraphs'
}

{ #category : 'building' }
FamixJavaCHABuilder >> addEdgesTo: aNode for: invocation types: possibleRuntimeTypes [
	"We save the invokedEntity and signature for speed reasons. It is slower to access a slot than an ivar and we get so much in this method that it has an impact. "

	| nodes invokedEntity signature encounterMatchingNode |
	invokedEntity := invocation invokedEntity.
	signature := invokedEntity signature.
	encounterMatchingNode := false. "In the past we used a #select:thenCollect: and an #ifEmpty:ifNotEmpty instead but this is creating a lot of temporary collections stressing the GC. So now we only do a #do: and we use this variable "

	nodes := possibleRuntimeTypes do: [ :type |
			         [
				         (type implementesMethodEquivalentTo: invokedEntity) ifTrue: [
						         encounterMatchingNode := true.
						         aNode addCallee: (self nodeForMethodSignature: signature kind: type stub: false) ] ]
				         on: Error
				         do: [ :exception |
						         self addErrorTo: aNode signature: signature kind: type exception: exception reason: 'An error occurend while trying to find the implementors of the invocked method. The model is not right.' ] ].

	encounterMatchingNode ifFalse: [
			invokedEntity isStub
				ifTrue: [
					"In case we have an invocation to a stub method of an interface with no known implementation, we create a stub node"
					aNode addCallee: (self nodeForMethodSignature: signature kind: invokedEntity parentType stub: true) ]
				ifFalse: [
						self addErrorTo: aNode signature: signature kind: invokedEntity parentType exception: nil reason: 'No matching node found. Either the model is wrong or the method has no implementor in the current model' ] ]
]

{ #category : 'accessing' }
FamixJavaCHABuilder >> addErrorTo: aNode signature: signature kind: type exception: exception reason: reason [
	"We check if we already have an error node like this. We use the hash for speed reasons."

	aNode addCallee: (graph errorNodes
			 detect: [ :node | node hash = (type idFor: signature) ]
			 ifNone: [
					 | errorNode |
					 errorNode := (FamixCallGraphErrorNode methodSignature: signature kind: type)
						              exception: exception;
						              reason: reason.
					 graph addError: errorNode.
					 errorNode ])
]

{ #category : 'building' }
FamixJavaCHABuilder >> build [
	| numberOfIterations |
	numberOfIterations := 0.
	self entryPoints do: [ :aNode | worklist at: aNode hash put: aNode ].

	[ numberOfIterations >= maxDepth or: [ worklist isEmpty] ] whileFalse: [
		"Usually we would treat only one node at a time but this is more costly than doing by batch"
		| toVisit |
		numberOfIterations := numberOfIterations + 1.
		toVisit := worklist values.
		worklist removeAll.
		toVisit do: [ :node | visited at: node hash put: node  ]. "If we do both things in the same loop sone nodes will be missing in `visited` and could lead to errors later."
		toVisit do: [ :node | self computeCallGraphOf: node ] ].
		
	"If errors occured, inspect them."
	graph errorNodes ifNotEmpty: [ :collection | collection inspect ].

	^ graph
]

{ #category : 'building' }
FamixJavaCHABuilder >> computeCallGraphOf: aNode [

	| invocations |
	invocations := self filteredOutgoingInvocationsForNode: aNode.

	invocations do: [ :invocation |
			(invocation isSuperInvocation or: [ invocation invokedEntity isConstructor ])
				ifTrue: [ self addEdgesTo: aNode for: invocation types: { invocation invokedEntity parentType } ]
				ifFalse: [ self addEdgesTo: aNode for: invocation types: (self possibleRuntimeTypesOf: invocation invokedEntity parentType) ] ].
			
	"We allow the user to define a block to add edges if reflection is involved and the user knows what to call"
	self reflectiveHook cull: aNode cull: self
]

{ #category : 'building' }
FamixJavaCHABuilder >> filteredOutgoingInvocationsForNode: aNode [

	^ aNode outgoingInvocations reject: [ :inv |
			  inv class = FamixJavaParametricInvocation or: [
					  inv target first name = 'clone' or: [
							  inv target first parentType name = '<StubMethodContainer>'
								  or: [
										  inv target first isParametricEntity or: [
												  inv target first containers anySatisfy: [ :c |
													  c isParametricEntity or: [
														  c isType and: [ c isInnerClass ] ] ] ] ] ] ] ]
]

{ #category : 'building' }
FamixJavaCHABuilder >> filteredRuntimeTypes: possibleRuntimeTypes [

	^ possibleRuntimeTypes reject: [ :rtt |
			  rtt isInnerClass or: [
				  rtt isParametricEntity or: [ rtt name = '<StubMethodContainer>' ] ] ]
]

{ #category : 'initialization' }
FamixJavaCHABuilder >> initialize [

	super initialize.
	worklist := IdentityDictionary new.
	visited := IdentityDictionary new.
	typesMap := IdentityDictionary new. "Used to cache the possible runtime types"

	self flag: #todo "Manage graph exploration:
	- Is there a path between two methods?
	- What are all the paths between two methods?
	- Is a not reacheable?"
]

{ #category : 'building' }
FamixJavaCHABuilder >> nodeForMethodSignature: signature kind: kind stub: aBoolean [

	| node id |
	id := kind idFor: signature. "This is the equivalent of the hash of the node to potentialy find."
	visited at: id ifPresent: [ :aNode | ^ aNode ].
	worklist at: id ifPresent: [ :aNode | ^ aNode ].

	node := (aBoolean
		         ifTrue: [ FamixCallGraphStubNode ]
		         ifFalse: [ FamixCallGraphNode ]) methodSignature: signature kind: kind.

	aBoolean ifFalse: [ worklist at: id put: node ].

	^ node
]

{ #category : 'building' }
FamixJavaCHABuilder >> possibleRuntimeTypesOf: aKind [

	^ typesMap at: aKind ifAbsentPut: [ self filteredRuntimeTypes: aKind possibleRuntimeTypes ]
]

{ #category : 'accessing' }
FamixJavaCHABuilder >> reflectiveHook [

	^ reflectiveHook ifNil: [ reflectiveHook := [ :node :builder | "Do nothing" ] ]
]

{ #category : 'accessing' }
FamixJavaCHABuilder >> reflectiveHook: anObject [

	reflectiveHook := anObject
]
