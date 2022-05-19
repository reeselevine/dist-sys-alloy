module ctr
open consistency
open util/integer

sig CtrReadValue extends Value {
  value: Int
}

// The value returned by a write
one sig Ok extends Value {}

// Read op
sig Read extends Operation {}

// Increment op
sig Inc extends Operation {}

// every write must return ok
fact IncRVal {
	all inc : op.Inc | inc.rval = Ok
}

fun visibleIncs[e: E]: E {
	{ inc : op.Inc | inc in vis.e}
}

fact ReadRVal {
	all r : op.Read | r.rval = { crv : CtrReadValue |
		crv.value = #{visibleIncs[r]}
	}
}

// utility function for showing the set of values a read returns
fun ctrValue : E-> Int {
    {e : E, val: Int | e in op.Read and val = e.rval.value }
}

pred noIncRead {
	no r : op.Read |
		r.rval.value > 0
}

check {causalConsistency => noIncRead} for 5



