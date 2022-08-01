module kvs
open consistency

// A key used to lookup a value in the kvs
sig Key {}

// Values that can be written
sig WriteValue extends Value {}

// An undefined value, for a read from an unitialized location
one sig Undefined extends Value {}

// The value returned by a write
one sig Ok extends Value {}

// Write op
sig Write extends Operation {
	wk: Key,
	v: WriteValue
}

// Read op
sig Read extends Operation {
	rk: Key
}

// every write value is connected to one write
fact writeValueSomeWrite {
	all wv: WriteValue | one v.wv
}

// every key is connected to some reads/writes
fact KeySomeOp {
	all k: Key | some (wk.k + rk.k)
}

// every write must return ok
fact WriteRVal {
	all w : op.Write | w.rval = Ok
}

// given a read, returns the last visible write to the same key in arbitration order
fun maximalWrite[r: E]: lone E {
	{w : op.Write |
		r in op.Read and r.op.rk = w.op.wk and w->r in vis and no w" : op.Write | 
			w.op.wk = w".op.wk and w"->r in vis and w->w" in ar}
}

// a read must return the last visible write to the same key, or undefined if 
// there is no visible write.
fact ReadRVal {
	all r : op.Read |
		some maximalWrite[r] => r.rval = maximalWrite[r].op.v else r.rval = Undefined
}

fun arg[]: E-> set (WriteValue + Undefined) {
    {e : E, val: (WriteValue+Undefined) | val=(e in op.Write => e.op.v else none)}
}

fun karg[]: E-> Key {
    {e : E, val: Key | val=(e in op.Write => e.op.wk else 
		(e in op.Read => e.op.rk else none))}
}

pred DekkerAnomaly {
	no wx, wy, rx, ry : E |
		wx in op.Write and wy in op.Write and rx in op.Read and ry in op.Read
		and wx->ry in ss and wy->rx in ss and wx->wy not in ss
		and wx.op.wk = rx.op.rk and wy.op.wk = ry.op.rk
		and wx->ry in rb and wy->rx in rb
		and rx.rval = Undefined and ry.rval = Undefined
}

assert CCAllowsDekker {
	 causalConsistency => DekkerAnomaly
}

assert SCAllowsDekker {
	sequentialConsistency => DekkerAnomaly
}

check CCAllowsDekker for 4
check SCAllowsDekker for 4


check CCConsistentPrefix for 3


