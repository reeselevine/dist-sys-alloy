module set_base
open consistency

// Values that can be added to/removed from a set
sig SetElem extends Value {}

// A read returns the elements in the set
sig SetReadValue extends Value {
	values: set SetElem
}

// The value returned by an add/remove
one sig Ok extends Value {}

// Read op
sig Read extends Operation {}

// Adds the specified element to the set
sig Add extends Operation {
	ae: SetElem
}

// Removes the specified element from the set
sig Remove extends Operation {
	re: SetElem
}

// every set element is connected to some adds and/or removes
fact setElemSomeOp {
	all se: SetElem | some (ae.se + re.se)
}

// every add/remove must return ok
fact SetOpRVal {
	all o : (op.Add + op.Remove) | o.rval = Ok
}
