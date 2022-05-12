module base
open util/relation

// The operation of an execution
abstract sig Operation {}

// What is returned by an operation
abstract sig Value {}

// The special symbol (upside down delta) that shows an operation that does not return
one sig Nabla {}

// Represents an event in an execution
sig E {
	op: Operation, // The operation of this event
	rval: Value + Nabla, // The returned value of this event (or Nabla if it never returns)
	rb: set E, // returns-before (partial order)
	ss: set E, // same-session (equivalence)
	vis: set E, // visibility (acyclic)
	ar: set E // arbitration (total order)
}

// every operation is connected to an event
fact OpSomeE {
	all o: Operation | one op.o
}

// rb is a partial order
fact rbPartialOrder {
	acyclic[rb, E]
	transitive[rb]
}

// ss is an equivalence
fact ssEquiv {
	equivalence[ss, E]
}

// vis is acyclic
fact visAcyclic {
	acyclic[vis, E]
}

// ar is a total order
fact arTotalOrder {
	acyclic[ar, E]
	transitive[ar]
	complete[ar, E]
}

// (x ->rb y) implies rval(x) != nabla
pred rbNoNabla {
	all x, y : E | (x -> y) in rb => x.rval != Nabla
}

// events are consistent with a timeline with operations corresponding to segments on a line
pred intervalOrder {
	all a, b, c, d : E | (a -> b) in rb and (c -> d) in rb =>
		 (a -> d) in rb or (c -> b) in rb
}

// events in the same session have a natural (i.e. not an infinite prefix) total order
pred ssEnumeration {
	acyclic[ss & rb, E] and
	transitive[ss & rb] and
	complete[ss & rb, E]
}

// Definition 3.2 in Principles of Eventual Consistency
pred wellFormed {
	rbNoNabla
	intervalOrder
	ssEnumeration
}

run {wellFormed} for 3 but 3 E
