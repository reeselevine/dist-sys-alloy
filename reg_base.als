module reg_base
open consistency

// Values that can be written
sig WriteValue extends Value {}

// An undefined value, for a read from an unitialized location
one sig Undefined extends Value {}

// The value returned by a write
one sig Ok extends Value {}

// Read op
sig Read extends Operation {}

// Write op
sig Write extends Operation {
	v: WriteValue
}

// every write value is connected to one write
fact writeValueSomeWrite {
	all wv: WriteValue | one v.wv
}

// every write must return ok
fact WriteRVal {
	all w : op.Write | w.rval = Ok
}
