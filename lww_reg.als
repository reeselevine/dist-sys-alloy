module lww_reg
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

// utility function for showing write values as attributes of an event
fun arg[]: E->(WriteValue + Undefined) {
    {e : E, val:(WriteValue+Undefined) | val=(e in op.Write => e.op.v else Undefined)}
}

// every write value is connected to one write
fact writeValueSomeWrite {
	all wv: WriteValue | one v.wv
}

// every read must return a written value or undefined
fact ReadRVal {
	all r : op.Read | r.rval in WriteValue + Undefined
}

// every write must return ok
fact WriteRVal {
	all w : op.Write | w.rval = Ok
}

// given an event e, returns the last visible write in arbitration order
fun maximalWrite[e: E]: lone E {
	{w : op.Write | 
		w->e in vis and no w" : op.Write | 
			w"->e in vis and w->w" in ar}
}

// a read must return the last visible write, or undefined if there is no visible write
fact UpdateReadRVal {
	all r : op.Read |
		some (op.Write & vis.r) => r.rval = maximalWrite[r].op.v else r.rval = Undefined
}

check {noCircularCausality}

check {basicEventualConsistency => readMyWrites}
check {basicEventualConsistency => monotonicReads}
check {basicEventualConsistency => consistentPrefix}

check {basicEventualConsistency => causalVisibility}
check {basicEventualConsistency => causalArbitration}

check {causalConsistency => singleOrder}
check {causalConsistency => realtime}
check {causalConsistency => consistentPrefix}

check {sequentialConsistency => realtime}
