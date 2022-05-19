module mv_reg
open reg_base

sig MVReadValue extends Value {
  values: set WriteValue
}

fun unshadowedWrites[e: E] : E {
	{ w : op.Write | no w" : op.Write | w != w" and w" in vis.e and (w-> w")  in vis}
}


fact ReadRVal {
	all r : op.Read |
		r.rval = { mvr : MVReadValue | 
			mvr.values = { unshadowedWrites[r] & vis.r }.op.v 
		}
}

// utility function for showing write values as attributes of an event
fun arg[]: E-> WriteValue {
    {e : E, val: WriteValue | val=(e in op.Write => e.op.v else none)}
}

// utility function for showing the set of values a read returns
fun readValues : E-> WriteValue {
    {e : E, val: WriteValue | e in op.Read and val in e.rval.values }
}

pred twoUnshadowedWrites {
	some r, w, w" : E |
		r in op.Read and w in op.Write and w" in op.Write
		and w != w" and (w->r) in vis and (w"->r) in vis and (w->w" not in vis)
		and (w"->w) not in vis and (w->w") not in ss
}
		
//run {causalConsistency and #Read > 0 and #Write > 0 some vis} for 5
run {twoUnshadowedWrites} for 5
