module lww_reg
open reg_base

// given an event e, returns the last visible write in arbitration order
fun maximalWrite[e: E]: lone E {
	{w : op.Write | 
		w->e in vis and no w" : op.Write | 
			w"->e in vis and w->w" in ar}
}

// a read must return the last visible write, or undefined if there is no visible write
// every read must return a written value or undefined
fact ReadRVal {
	all r : op.Read |
		some (op.Write & vis.r) => r.rval = maximalWrite[r].op.v else r.rval = Undefined
}

// utility function for showing write values as attributes of an event
fun arg[]: E-> set (WriteValue + Undefined) {
    {e : E, val: (WriteValue+Undefined) | val=(e in op.Write => e.op.v else none)}
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
