Class {
	#name : 'FamixCallGraph',
	#superclass : 'Object',
	#instVars : [
		'entryPoints',
		'errors'
	],
	#category : 'Famix-CallGraphs',
	#package : 'Famix-CallGraphs'
}

{ #category : 'comparing' }
FamixCallGraph >> = aCallGraph [

	| sortMethod selfNodesSorted otherNodesSorted |
	"self allNodes size = aCallGraph allNodes size ifFalse: [ ^ false ]."
	sortMethod := [ :a :b |
		              (String streamContents: [ :s | a printOn: s ])
		              > (String streamContents: [ :s | b printOn: s ]) ].

	selfNodesSorted := self allNodes sorted: sortMethod.
	otherNodesSorted := aCallGraph allNodes sorted: sortMethod.

	selfNodesSorted withIndexDo: [ :el :i |
			| otherEl |
			otherEl := otherNodesSorted at: i.
			(el = otherEl and: [
					 el callers size = otherEl callers size and: [
							 (el callers includesAll: otherEl callers) and: [
									 el callees size = otherEl callees size and: [
										 el callees includesAll: otherEl callees ] ] ] ]) ifFalse: [
				^ false ] ].

	^ true
]

{ #category : 'adding' }
FamixCallGraph >> addError: aNode [

	errors add: aNode
]

{ #category : 'helpers' }
FamixCallGraph >> allNodes [

	^ self entryPoints flatCollectAsSet: #withAllCallees
]

{ #category : 'accessing' }
FamixCallGraph >> entryPoint [

	self entryPoints size = 1 ifFalse: [ self error: 'This method should be called only if the graph has 1 entry point.' ].
	^ self entryPoints anyOne
]

{ #category : 'accessing' }
FamixCallGraph >> entryPoints [

	^ entryPoints
]

{ #category : 'accessing' }
FamixCallGraph >> entryPoints: aCollection [

	entryPoints := aCollection collect: [ :method |
			               method isMooseObject
				               ifTrue: [ method asCallGraphNode ]
				               ifFalse: [ method ] ]
]

{ #category : 'accessing' }
FamixCallGraph >> errorNodes [

	^ errors
]

{ #category : 'initialization' }
FamixCallGraph >> initialize [

	super initialize.
	errors := IdentitySet new
]

{ #category : 'helpers' }
FamixCallGraph >> numberOfNodes [

	^ self allNodes size
]
