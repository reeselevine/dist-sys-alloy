module std_set
open set_base

// The standard set returns all visible elements, except for ones that were later
// removed (as decided by arbitration order ar).
fun visibleAdds[e: E]: E {
	{ a : op.Add | 
		a->e in vis and no r : op.Remove |
			r->e in vis and a->r in ar}
}

fact ReadRVal {
	all r : op.Read |
		r.rval = { srv : SetReadValue | 
			srv.values = { visibleAdds[r] }.op.ae
		}
}


// utility function for showing write values as attributes of an event
fun arg[]: E-> SetElem {
    {e : E, val: SetElem | val=(e in op.Add => e.op.ae else (
		e in op.Remove => e.op.re else none)) }
}

// utility function for showing the set of values a read returns
fun readValues : E-> SetElem {
    {e : E, val: SetElem | e in op.Read and val in e.rval.values }
}

pred noMultSet {
	no r : op.Read |
		#{r.rval.values} > 1
}

pred concurAddRem {
	no r, a, rem : E |
		r in op.Read and a in op.Add and rem in op.Remove
		and a->r in vis and rem->r in vis and a->rem not in (vis + ~vis)
		and a.op.ae = rem.op.re and a->rem in ar
		and a.op.ae not in r.rval.values
}
		
check BECReadMyWrites for 3 but exactly 1 Add, 1 Read, 0 Remove

check {causalConsistency => concurAddRem} for 3
