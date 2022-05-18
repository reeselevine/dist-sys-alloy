module consistency
open base

// session order is a partial order defined as the intersection of returns before and same session
fun so: E->E {
	rb & ss
}

// happens before is the transitive closure of the union of session order and visibility
fun hb: E->E {
	^(so + vis)
}

// The following three predicates are "session guarantees", defined to
// preserve the order of operations within a single session

// Events in the a session must be visible to later events in that same session
pred readMyWrites {
	so in vis
}

// If an event e is visible to an event e', e must also be visible to an event e'' in
// the same session as e'.
pred monotonicReads {
	vis.so in vis
}

// If an event from another session is visible, so are all events that precede
// that event in arbitration order.
pred consistentPrefix {
	ar.(vis & ~ss) in vis
}

// The following four predicates guarantee varying levels of causality

// Happens before is acyclic
pred noCircularCausality {
	acyclic[hb, E]
}

// If an event happens before another event, it is visible to that event
pred causalVisibility {
	hb in vis
}

// If an event happens before another event, it must be arbitrated before it.
pred causalArbitration {
	hb in ar
}

// The combination of causal visibility and arbitration is called causality.
pred causality {
	causalVisibility
	causalArbitration
}

// The single order predicate enforces sequential consistency, as it ensures
// that events must see events that are arbitrated before it, and that visible events
// must be arbitrated before it. The only exception is events that are arbitrated 
// earlier but never return are not visible.
// Note: This predicate is not analyzable by Alloy, as it requires quantifying over
// all combinations of subsets of events that do not return, which is higher-order.
// Alloy* is an option, but does not look like it has been actively developed in a while.
pred singleOrder {
	some E" : set rval.Nabla | vis = (ar - E"->E)
}

// To remove the above issue, we can state that visibility is equal to arbitration.
// For this to work, a given datatype must contain events that always return.
pred singleOrderSimpl {
	vis = ar
}

// Linearizability requires that if an operation returns before (using a wall-clock
// as the decider of when it returns), it must be arbitrated before another operation
// that returns later. In practice, this requires either perfectly synchronized clocks
// or a side-channel for systems to use that determines the rb relation.
pred realtime {
	rb in ar
}


// Finally, we can define the predicates necessary for each level of consistency.
// Note that without modeling a datatype, these definitions are of limited usefulness.

pred basicEventualConsistency {
	noCircularCausality
}

pred causalConsistency {
	causality
}

pred sequentialConsistency {
	singleOrderSimpl
	readMyWrites
}

pred linearizability {
	singleOrderSimpl
	realtime
}
	
